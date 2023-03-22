{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
-- | This module defines an interface to drive macaw code discovery and identify
-- corresponding blocks in an original and patched binary
module Pate.Discovery (
  discoverPairs,
  runDiscovery,
  lookupBlocks,
  getBlocks,
  getBlocks',
  getAbsDomain,
  getStackOffset,
  matchesBlockTarget,
  associateFrames,
  matchingExits,
  isMatchingCall,
  concreteToLLVM,
  nextBlock
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad (forM)
import qualified Control.Monad.Catch as CMC
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO, MonadIO )
import qualified Data.IORef as IO
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Reader as CMR
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import           Data.Functor.Const
import           Data.Int
import qualified Data.List.NonEmpty as DLN
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.WithRepr
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.Set as Set
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           GHC.Stack ( HasCallStack )

import qualified Data.Macaw.AbsDomain.AbsState as MAS
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.ELF as MBLE
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI
import qualified What4.Partial as WP
import qualified What4.SatResult as WR

import qualified Pate.Address as PA
import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery.ParsedFunctions as PDP
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory as PM
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimState as PSS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.SymbolTable as PSym
import qualified What4.ExprHelpers as WEH

import           Pate.TraceTree

--------------------------------------------------------
-- Block pair matching

-- | Compute all possible valid exit pairs from the given slice.
discoverPairs ::
  forall sym arch v.
  SimBundle sym arch v ->
  EquivM sym arch [PPa.PatchPair (PB.BlockTarget arch)]
discoverPairs bundle = withTracing @"debug" "discoverPairs" $ withSym $ \sym -> do
  cachedTargets <- lookupBlockCache envExitPairsCache pPair >>= \case
    Just pairs -> return pairs
    Nothing -> return Set.empty
  cache <- IO.liftIO $ IO.newIORef (Map.empty :: Map.Map (Some (PB.BlockTarget arch)) Bool)
  let
    -- quickly filter out unreachable block exits
    checkSat :: forall bin. PB.KnownBinary bin => PB.BlockTarget arch bin -> EquivM_ sym arch Bool
    checkSat blkt = do
      matches <- (matchesBlockTargetOne bundle blkt >>= PAS.toPred sym)
      goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
      result <- isPredSat' goalTimeout matches >>= \case
        Just True -> return True
        Just False -> return False
        Nothing -> throwHere PEE.InconclusiveSAT
      IO.liftIO $ IO.modifyIORef cache (Map.insert (Some blkt) result)
      return result

  blkTs <- PPa.forBinsF $ \bin -> do
    blk <- PPa.get bin pPair
    blks <- getSubBlocks blk
    subTree @"blocktarget1" ("Targets (" ++ show bin ++ ")") $ do
      mapM_ (\blkts -> subTrace (Some blkts) $ return ()) blks
    subTree @"blocktarget1" ("Sat Targets (" ++ show bin ++ ")") $ do
      blks' <- CMR.lift $ CMR.filterM checkSat blks
      mapM_ (\blkts -> subTrace (Some blkts) $ return ()) blks'
      return blks'

  let
    allCalls = case blkTs of
      PPa.PatchPairF blksO blksP ->
        [ PPa.PatchPair blkO blkP
          | blkO <- blksO
          , blkP <- blksP
          , compatibleTargets blkO blkP]
      PPa.PatchPairSingle bin (PPa.LiftF blks) -> map (PPa.mkSingle bin) blks
  blocks <- getBlocks $ PSS.simPair bundle
  
  let newCalls = Set.toList ((Set.fromList allCalls) Set.\\ cachedTargets)
  
  
  subTree @"blocktarget" "Cached Pairs" $
    mapM_ (\blkts -> subTrace blkts $ return ()) (Set.toList cachedTargets)


  result <-
    subTree @"blocktarget" "Discovered Pairs" $ 
    forM newCalls $ \blkts -> subTrace blkts $ startTimer $ do
      let emit r = (emitEvent (PE.DiscoverBlockPair blocks blkts r) >> emitTrace @"blocktargetresult" r)
      matches <- (matchesBlockTarget bundle blkts >>= PAS.toPred sym)
      case WI.asConstantPred matches of
        Just True -> do
          emit PE.Reachable
          return $ Just $ blkts
        Just False -> do
          emit PE.Unreachable
          return $ Nothing
        _ ->  do
          goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
          er <- checkSatisfiableWithModel goalTimeout "discoverPairs" matches $ \satRes -> do
            case satRes of
              WR.Sat _ -> do
                emit PE.Reachable
                return $ Just $ blkts
              WR.Unsat _ -> do
                emit PE.Unreachable
                return Nothing
              WR.Unknown -> do
                emit PE.InconclusiveTarget
                throwHere PEE.InconclusiveSAT
          case er of
            Left _err -> do
              emit PE.InconclusiveTarget
              throwHere PEE.InconclusiveSAT
            Right r -> return r
  let resultSet = Set.fromList (catMaybes result)
  modifyBlockCache envExitPairsCache pPair Set.union resultSet
  return $ Set.toList (Set.union resultSet cachedTargets)
  where
  pPair = PSS.simPair bundle

matchingExits ::
  forall sym arch v.
  SimBundle sym arch v ->
  MCS.MacawBlockEndCase ->
  EquivM sym arch (WI.Pred sym)
matchingExits bundle ecase = withSym $ \sym -> PPa.joinPatchPred (\x y -> liftIO $ WI.andPred sym x y) $ \bin ->  do
  blkend <- PSS.simOutBlockEnd <$> PPa.get bin (PSS.simOut bundle)
  liftIO $ MCS.isBlockEndCase (Proxy @arch) sym blkend ecase

-- | True when both the patched and original program necessarily end with
-- a call to the same function, assuming exact initial equivalence.
isMatchingCall ::
  forall sym arch v.
  SimBundle sym arch v ->
  EquivM sym arch Bool
isMatchingCall bundle = withSym $ \sym -> do
  eqIPs <- PPa.defaultPair (return $ WI.truePred sym) (PSS.simOut bundle) $ \outO outP -> do
    let
      ipO = (PSS.simOutRegs outO) ^. MC.curIP
      ipP = (PSS.simOutRegs outP) ^. MC.curIP
    liftIO $ MT.llvmPtrEq sym (PSR.macawRegValue ipO) (PSR.macawRegValue ipP)
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- TODO: Why are some of the calls being classified as Arch exits?
  isCall <- matchingExits bundle MCS.MacawBlockEndCall
  isArch <- matchingExits bundle MCS.MacawBlockEndArch
  isExpectedExit <- liftIO $ WI.orPred sym isArch isCall
  goal <- liftIO $ WI.andPred sym eqIPs isExpectedExit
  asm <- exactEquivalence (PSS.simIn bundle)
  withAssumption asm $
    isPredTrue' goalTimeout goal

-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  PB.BlockTarget arch PB.Original ->
  PB.BlockTarget arch PB.Patched ->
  Bool
compatibleTargets blkt1 blkt2 = (PB.targetEndCase blkt1 == PB.targetEndCase blkt2) &&
  PB.concreteBlockEntry (PB.targetCall blkt1) == PB.concreteBlockEntry (PB.targetCall blkt2) &&
  case (PB.targetReturn blkt1, PB.targetReturn blkt2) of
    (Just blk1, Just blk2) -> PB.concreteBlockEntry blk1 == PB.concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

exactEquivalence ::
  PPa.PatchPair (PSS.SimInput sym arch v) ->
  EquivM sym arch (WI.Pred sym)
exactEquivalence input = withSym $ \sym ->
  PPa.defaultPair (return $ WI.truePred sym) input $ \inO inP -> do
    eqCtx <- equivalenceContext
    regsEqs <- liftIO $ PRt.zipWithRegStatesM (PSS.simInRegs inO) (PSS.simInRegs inP) $ \r v1 v2 ->
      Const <$> PEq.registerValuesEqual sym eqCtx r v1 v2

    regsEq <- liftIO $ WEH.allPreds sym (map snd $ PRt.assocs regsEqs)
    heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
    isPredSat heuristicTimeout regsEq >>= \case
      True -> return ()
      False -> CME.fail "exactEquivalence: regsEq: assumed false"

    memEq <- liftIO $ MT.memEqExact sym (MT.memState $ PSS.simInMem inO) (MT.memState $ PSS.simInMem inP)

    isPredSat heuristicTimeout memEq >>= \case
      True -> return ()
      False -> CME.fail "exactEquivalence: memEq: assumed false"

    liftIO $ WI.andPred sym regsEq memEq

matchesBlockTargetOne ::
  forall sym arch bin v.
  PB.KnownBinary bin =>
  SimBundle sym arch v ->
  PB.BlockTarget arch bin ->
  EquivM sym arch (PAS.AssumptionSet sym)
matchesBlockTargetOne bundle blkt = withSym $ \sym -> do
    -- true when the resulting IPs call the given block targets
   let (bin :: PB.WhichBinaryRepr bin) = WI.knownRepr
   regs <- PSS.simOutRegs <$> PPa.get bin (PSS.simOut bundle)
   endCase <- PSS.simOutBlockEnd <$> PPa.get bin (PSS.simOut bundle)
   let
     ip = regs ^. MC.curIP
     ret = MCS.blockEndReturn (Proxy @arch) endCase

   callPtr <- concreteToLLVM (PB.targetCall blkt)
   let eqCall = PAS.ptrBinding (PSR.macawRegValue ip) callPtr

   targetRet <- targetReturnPtr blkt
   eqRet <- liftIO $ liftPartialRel sym (\p1 p2 -> return $ PAS.ptrBinding p1 p2) ret targetRet
   MapF.Pair e1 e2 <- liftIO $ MCS.blockEndCaseEq (Proxy @arch) sym endCase (PB.targetEndCase blkt)
   let eqCase = PAS.exprBinding e1 e2
   return $ eqCall <> eqRet <> eqCase
  

matchesBlockTarget ::
  forall sym arch v.
  SimBundle sym arch v ->
  PPa.PatchPair (PB.BlockTarget arch) ->
  EquivM sym arch (PAS.AssumptionSet sym)
matchesBlockTarget bundle blktPair =
  PPa.catBins $ \bin -> do
    blkt <- PPa.get bin blktPair
    matchesBlockTargetOne bundle blkt


-- | Compute an 'PAS.AssumptionSet' that assumes the association between
-- the 'PSS.StackBase' of the input and output states of the given bundle,
-- according to the given exit case.
-- In most cases the assumption is that the stack base does not change (i.e.
-- a backjump within a function maintains the same base). In the case that
-- the block end is a 'MCS.MacawBlockEndCall', this assumes that outgoing
-- stack base is now equal to the value of the stack register after the function call.
--
-- This assumption is needed in the final stage of widening, in order to re-phrase
-- any stack offsets that appear in the resulting equivalence domain: from the callee's stack
-- base to the caller's stack base.
-- See: 'PSS.StackBase'
associateFrames ::
  forall sym arch v.
  SimBundle sym arch v ->
  MCS.MacawBlockEndCase ->
  Bool ->
  EquivM sym arch (SimBundle sym arch v)
associateFrames bundle exitCase isStub = do
  (asm :: PAS.AssumptionSet sym) <- PPa.catBins $ \bin -> do
    input <- PPa.get bin $ simIn bundle
    output <- PPa.get bin $ simOut bundle
    let
      st_pre = PSS.simInState input
      st_post = PSS.simOutState output
      frame_pre = PSS.unSE $ PSS.unSB $ PSS.simStackBase $ st_pre
      frame_post = PSS.unSE $ PSS.unSB $ PSS.simStackBase $ st_post
      CLM.LLVMPointer _ sp_post = PSR.macawRegValue $ PSS.simSP st_post
    case exitCase of
      -- a backjump does not modify the frame
      MCS.MacawBlockEndJump -> return $ PAS.exprBinding frame_post frame_pre
      -- Stubs are treated specially and do not create return nodes, so
      -- the pre and post frames are the same
      MCS.MacawBlockEndCall | isStub -> return $ PAS.exprBinding frame_post frame_pre
      -- For a function call the post-state frame is the frame for the
      -- target function, and so we represent that by asserting that it is
      -- equal to the value of the stack pointer at the call site
      MCS.MacawBlockEndCall -> return $ PAS.exprBinding frame_post sp_post
      -- note that a return results in two transitions:
      -- the first transitions to the "Return" graph node and then
      -- the second transitions from that node to any of the call sites (nondeterministically)
      -- this case is only for the first transition, which does not perform
      -- any frame rebinding (as we don't yet know where we are returning to)
      MCS.MacawBlockEndReturn -> return $ PAS.exprBinding frame_post frame_pre
      -- a branch does not modify the frame
      MCS.MacawBlockEndBranch -> return $ PAS.exprBinding frame_post frame_pre
      -- nothing to do on failure
      MCS.MacawBlockEndFail -> return mempty
      -- this likely requires some architecture-specific reasoning
      MCS.MacawBlockEndArch -> return mempty
  -- we apply the rewrite in-line here so that the transformation of
  -- the frame variable is included as part of the semantics for this bundle
  withSym $ \sym -> do
    out' <- PAS.apply sym asm (simOut bundle)
    return $ bundle { simOut = out' }

liftPartialRel ::
  CB.IsSymInterface sym =>
  sym ->
  (a -> a -> IO (PAS.AssumptionSet sym)) ->
  WP.PartExpr (WI.Pred sym) a ->
  WP.PartExpr (WI.Pred sym) a ->
  IO (PAS.AssumptionSet sym)
liftPartialRel sym rel (WP.PE p1 e1) (WP.PE p2 e2) = do
  bothConds <- WI.andPred sym p1 p2
  rel' <- rel e1 e2
  case WI.asConstantPred bothConds of
    Just True -> return rel'
    Just False -> return mempty
    Nothing -> do
      relPred <- PAS.toPred sym rel'
      justCase <- PAS.fromPred <$> WI.impliesPred sym bothConds relPred
      return $ (PAS.exprBinding p1 p2) <> justCase
liftPartialRel _sym _ WP.Unassigned WP.Unassigned = return mempty
liftPartialRel sym _ WP.Unassigned (WP.PE p2 _) = PAS.fromPred <$> WI.notPred sym p2
liftPartialRel sym _ (WP.PE p1 _) WP.Unassigned = PAS.fromPred <$> WI.notPred sym p1

targetReturnPtr ::
  PB.BlockTarget arch bin ->
  EquivM sym arch (CS.RegValue sym (CT.MaybeType (CLM.LLVMPointerType (MC.ArchAddrWidth arch))))
targetReturnPtr blkt | Just blk <- PB.targetReturn blkt = withSym $ \sym -> do
  ptr <- concreteToLLVM blk
  return $ WP.justPartExpr sym ptr
targetReturnPtr _ = withSym $ \sym -> return $ WP.maybePartExpr sym Nothing


-- | From the given starting point, find all of the accessible
-- blocks
getSubBlocks ::
  forall sym arch bin.
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch [PB.BlockTarget arch bin]
getSubBlocks b = withBinary @bin $
  do let addr = PB.concreteAddress b
     pfm <- PMC.parsedFunctionMap <$> getBinCtx @bin
     mtgt <- PDP.parsedBlocksContaining b pfm
     tgts <- case mtgt of
       Just (PDP.ParsedBlocks pbs) ->
         concat <$> mapM (\x -> concreteJumpTargets b x) pbs
       Nothing -> throwHere $ PEE.UnknownFunctionEntry addr
     mapM_ (\x -> validateBlockTarget x) tgts
     return tgts

-- | Find the abstract domain for a given starting point
getAbsDomain ::
  forall sym arch bin.
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (MAS.AbsBlockState (MC.ArchReg arch))
getAbsDomain b = withRepr (PB.blockBinRepr b) $ withBinary @bin $ do
  pfm <- PMC.parsedFunctionMap <$> getBinCtx @bin
  mtgt <- liftIO $ PDP.parsedBlockEntry b pfm
  case mtgt of
    Right (Some pb) -> return $ MD.blockAbstractState pb
    Left err -> throwHere $ PEE.MissingParsedBlockEntry err b

getStackOffset ::
  forall sym arch bin.
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch Int64
getStackOffset b = do
  absSt <- getAbsDomain b
  let
    regs = absSt ^. MAS.absRegState
    sp = regs ^. (MC.boundValue MC.sp_reg)
  case sp of
    MAS.StackOffsetAbsVal _ i -> return i
    _ -> throwHere $ PEE.UnexpectedStackValue (PB.concreteAddress b)


validateBlockTarget ::
  HasCallStack =>
  PB.KnownBinary bin =>
  PB.BlockTarget arch bin ->
  EquivM sym arch ()
validateBlockTarget tgt = do
  let blk = PB.targetCall tgt
  case PB.concreteBlockEntry blk of
    PB.BlockEntryInitFunction -> do
      (manifestError $ lookupBlocks blk) >>= \case
        Left err -> throwHere $ PEE.InvalidCallTarget (PB.concreteAddress blk) err
        Right _ -> return ()
    _ -> return ()

concreteNextIPs ::
  PA.ValidArch arch =>
  MC.RegState (MC.ArchReg arch) (MC.Value arch ids) ->
  [PA.ConcreteAddress arch]
concreteNextIPs st = concreteValueAddress $ st ^. MC.curIP

concreteValueAddress ::
  forall arch ids.
  PA.ValidArch arch =>
  MC.Value arch ids (MT.BVType (MC.ArchAddrWidth arch)) ->
  [PA.ConcreteAddress arch]
concreteValueAddress = \case
  MC.RelocatableValue _ addr -> [ PA.memAddrToAddr addr ]
  MC.BVValue w bv |
    Just WI.Refl <- WI.testEquality w (MM.memWidthNatRepr @(MC.ArchAddrWidth arch)) ->
      [ PA.memAddrToAddr (MM.absoluteAddr (MM.memWord (fromIntegral bv))) ]
  MC.AssignedValue (MC.Assignment _ rhs) -> case rhs of
    MC.EvalApp (MC.Mux _ _ b1 b2) -> concreteValueAddress b1 ++ concreteValueAddress b2
    _ -> []
  _ -> []
  -- TODO ^ is this complete?

concreteJumpTargets ::
  forall sym bin arch ids.
  HasCallStack =>
  PB.KnownBinary bin =>
  PA.ValidArch arch =>
  PB.ConcreteBlock arch bin ->
  MD.ParsedBlock arch ids ->
  EquivM sym arch [PB.BlockTarget arch bin]
concreteJumpTargets from pb = case MD.pblockTermStmt pb of
  MD.ParsedCall st ret ->
    callTargets from (concreteNextIPs st) ret

  MD.PLTStub st _ _ ->
    case MapF.lookup (MC.ip_reg @(MC.ArchReg arch)) st of
      Just addr -> callTargets from (concreteValueAddress addr) Nothing
      _ -> error "Could not resolve IP register in PLTStub"

  MD.ParsedJump _ tgt ->
    return [ jumpTarget from tgt ]

  MD.ParsedBranch _ _ t f ->
    return [ branchTarget from t, branchTarget from f ]

  MD.ParsedLookupTable _jt st _ _ ->
    return [ jumpTarget' from next | next <- concreteNextIPs st ]

  MD.ParsedArchTermStmt _ st ret -> do
    let ret_blk = fmap (PB.mkConcreteBlock from PB.BlockEntryPostArch) ret
    let MCS.MacawBlockEnd end_case _ = MCS.termStmtToBlockEnd (MD.pblockTermStmt pb)
    return [ PB.BlockTarget (PB.mkConcreteBlock' from PB.BlockEntryPreArch next) ret_blk end_case
           | next <- (concreteNextIPs st)
           ]

  MD.ParsedReturn{} -> return []
  MD.ParsedTranslateError{} -> return []
  MD.ClassifyFailure{} -> return []

jumpTarget ::
    PB.ConcreteBlock arch bin ->
    MC.ArchSegmentOff arch ->
    PB.BlockTarget arch bin
jumpTarget from to =
  PB.BlockTarget (PB.mkConcreteBlock from PB.BlockEntryJump to) Nothing MCS.MacawBlockEndJump

branchTarget ::
    PB.ConcreteBlock arch bin ->
    MC.ArchSegmentOff arch ->
    PB.BlockTarget arch bin
branchTarget from to =
  PB.BlockTarget (PB.mkConcreteBlock from PB.BlockEntryJump to) Nothing MCS.MacawBlockEndBranch


jumpTarget' ::
    PB.ConcreteBlock arch bin ->
    PA.ConcreteAddress arch ->
    PB.BlockTarget arch bin
jumpTarget' from to =
  PB.BlockTarget (PB.mkConcreteBlock' from PB.BlockEntryJump to) Nothing MCS.MacawBlockEndJump

callTargets ::
    forall bin arch sym .
    HasCallStack =>
    PB.KnownBinary bin =>
    PB.ConcreteBlock arch bin ->
    [PA.ConcreteAddress arch] ->
    Maybe (MC.ArchSegmentOff arch) ->
    EquivM sym arch [PB.BlockTarget arch bin]
callTargets from next_ips mret = do
   binCtx <- getBinCtx @bin
   let mem = MBL.memoryImage (PMC.binary binCtx)
   let pfm = PMC.parsedFunctionMap binCtx
   fmap catMaybes $ forM next_ips $ \next -> do
     let nextMem = PA.addrToMemAddr next  
     case MM.resolveRegionOff mem (MM.addrBase nextMem) (MM.addrOffset nextMem) of
       Just segoff -> do
         let fe = PB.FunctionEntry { PB.functionSegAddr = segoff
                                   , PB.functionSymbol = Nothing
                                   , PB.functionBinRepr = PC.knownRepr
                                   , PB.functionIgnored = False
                                   , PB.functionEnd = Nothing
                                   }
         fe' <- liftIO $ PDP.resolveFunctionEntry fe pfm
         let pb = PB.functionEntryToConcreteBlock fe'
         let ret_blk = fmap (PB.mkConcreteBlock from PB.BlockEntryPostFunction) mret
         return $ Just (PB.BlockTarget pb ret_blk MCS.MacawBlockEndCall)
       Nothing -> do
         -- this isn't necessarily an error, since we always double check
         -- the call targets anyways, if this is an actual possible call target
         -- we'll find it when checking for totality
         -- _ <- emitError $ PEE.MissingRegionOffset (MM.addrBase nextMem) (MM.addrOffset nextMem)
         return Nothing                                        

-------------------------------------------------------
-- Driving macaw to generate the initial block map

addFunctionEntryHints
  :: (MM.MemWidth (MC.ArchAddrWidth arch))
  => proxy arch
  -> MM.Memory (MC.ArchAddrWidth arch)
  -> (name, PH.FunctionDescriptor)
  -> ([Word64], [MC.ArchSegmentOff arch])
  -> ([Word64], [MC.ArchSegmentOff arch])
addFunctionEntryHints _ mem (_name, fd) (invalid, entries) =
  case MM.resolveAbsoluteAddr mem (fromIntegral addrWord) of
    Nothing -> (addrWord : invalid, entries)
    Just segOff -> (invalid, segOff : entries)
  where
    addrWord = PH.functionAddress fd

-- | Special-purpose function name that is treated as abnormal program exit
abortFnName :: T.Text
abortFnName = "__pate_abort"

addAddrSym
  :: (MM.MemWidth w, HasCallStack)
  => MM.Memory w
  -> MD.AddrSymMap w
  -> PH.FunctionDescriptor
  -> CME.ExceptT PEE.EquivalenceError IO (MD.AddrSymMap w)
addAddrSym mem m funcDesc = do
  let symbol = TE.encodeUtf8 (PH.functionSymbol funcDesc)
  let addr0 = PH.functionAddress funcDesc
  case PM.resolveAbsoluteAddress mem (fromIntegral addr0) of
    Just segoff -> return (Map.insert segoff symbol m)
    Nothing -> return m

type AddrEndMap w = Map.Map (MM.MemSegmentOff w) (MM.MemSegmentOff w)

addFnEnd
  :: (MM.MemWidth w, HasCallStack)
  => MM.Memory w
  -> AddrEndMap w
  -> PH.FunctionDescriptor
  -> CME.ExceptT PEE.EquivalenceError IO (AddrEndMap w)
addFnEnd mem m funcDesc = case PH.functionEnd funcDesc of
  Just fnEnd -> do
    let addr0 = PH.functionAddress funcDesc
    case (PM.resolveAbsoluteAddress mem (fromIntegral addr0), PM.resolveAbsoluteAddress mem (fromIntegral fnEnd)) of
      (Just segoff, Just segoffEnd) -> return (Map.insert segoff segoffEnd m)
      _ -> return m
  Nothing -> return m

-- | Build a symbol table used to support invoking overrides in the "inline
-- callee" feature using traditional symbolic execution
--
-- This differs from the other symbol table introduced by 'addAddrSym' in that
-- it has extra entries that also cover assigning names to PLT stubs (enabling
-- us to override calls to missing shared library functions).
--
-- We should ultimately combine the two and use this map in
-- 'newParsedFunctionMap'; that map is just used to provide names to discovered
-- functions, which should *never* need the extra names (but for which it
-- wouldn't hurt to have them), as we should never be running code discovery
-- over PLT stubs.
buildSymbolTable
  :: forall arch
   . (MT.KnownNat (MC.ArchAddrWidth arch))
  => PH.VerificationHints
  -> Map.Map BS.ByteString (BVS.BV (MC.ArchAddrWidth arch))
  -> PSym.SymbolTable arch
buildSymbolTable hints extraSyms =
  F.foldl' addPLTStub (F.foldl' addHintEntry PSym.emptySymbolTable funHints) (Map.toList extraSyms)
  where
    funHints = fmap snd (PH.functionEntries hints)
    addHintEntry st funcDesc =
      let addr = BVS.mkBV (PN.knownNat @(MC.ArchAddrWidth arch)) (toInteger (PH.functionAddress funcDesc))
          name = PH.functionSymbol funcDesc
      in PSym.addSymbolTableEntry addr (PSym.LocalSymbol name) st
    addPLTStub st (bsName, addr) =
      let tname = TE.decodeUtf8With TEE.lenientDecode bsName
      in PSym.addSymbolTableEntry addr (PSym.PLTSymbol tname) st


runDiscovery ::
  forall arch bin.
  PB.KnownBinary bin =>
  PA.ValidArch arch =>
  PA.ValidArchData arch ->
  Maybe FilePath ->
  PB.WhichBinaryRepr bin ->
  Map.Map BS.ByteString (BVS.BV (MC.ArchAddrWidth arch)) ->
  PLE.LoadedELF arch ->
  PH.VerificationHints ->
  PC.PatchData ->
  CME.ExceptT PEE.EquivalenceError IO ([Word64], PMC.BinaryContext arch bin)
runDiscovery aData mCFGDir repr extraSyms elf hints pd = do
  let archInfo = PLE.archInfo elf
  entries <- MBL.entryPoints bin
  addrSyms' <- F.foldlM (addAddrSym mem) mempty (fmap snd (PH.functionEntries hints))
  addrSyms <- F.foldlM (addElfFunction) addrSyms' (DLN.toList entries)

  let (invalidHints, _hintedEntries) = F.foldr (addFunctionEntryHints (Proxy @arch) mem) ([], F.toList entries) (PH.functionEntries hints)

  addrEnds <- F.foldlM (addFnEnd mem) mempty (fmap snd (PH.functionEntries hints))
  pfm <- liftIO $ PDP.newParsedFunctionMap mem addrSyms archInfo mCFGDir pd addrEnds (PA.validArchExtractPrecond aData)
  let idx = F.foldl' addFunctionEntryHint Map.empty (PH.functionEntries hints)

  let startEntry = DLN.head entries
  
  let startEntry' = PB.FunctionEntry { PB.functionSegAddr = startEntry
                                     , PB.functionSymbol = Nothing
                                     , PB.functionBinRepr = repr
                                     , PB.functionIgnored = False
                                     , PB.functionEnd = Nothing
                                     }
  startEntry'' <- liftIO $ PDP.resolveFunctionEntry startEntry' pfm
  let abortFnEntry = do
        fnDesc <- lookup abortFnName (PH.functionEntries hints)
        abortFnAddr <- PM.resolveAbsoluteAddress mem (MM.memWord (PH.functionAddress fnDesc))
        return PB.FunctionEntry { PB.functionSegAddr = abortFnAddr
                                , PB.functionSymbol = Just (TE.encodeUtf8 abortFnName)
                                , PB.functionBinRepr = repr
                                , PB.functionIgnored = False
                                , PB.functionEnd = Nothing
                                }

  let symTab = buildSymbolTable hints extraSyms

  -- FIXME: Fill in the symbol table based on the hints and the dynamic symbol table
  return $ (invalidHints, PMC.BinaryContext bin pfm startEntry'' hints idx abortFnEntry symTab)
  where
    bin = PLE.loadedBinary elf
    mem = MBL.memoryImage bin

    addElfFunction m segOff = do
      let addr = MM.segoffAddr segOff
      case MBL.symbolFor bin addr of
        Right nm -> return $ Map.insert segOff nm m
        Left (_e :: CMC.SomeException) -> return m

    addFunctionEntryHint m (_, fd) =
      let addrWord = PH.functionAddress fd
      in case MBLE.resolveAbsoluteAddress mem (fromIntegral addrWord) of
           Nothing -> m
           Just segoff ->
             let addr = PA.segOffToAddr segoff
             in Map.insert addr fd m

getBlocksSingle
  :: forall bin arch sym m e
   . (CMC.MonadThrow m, PPa.PatchPairM m, MS.SymArchConstraints arch, Typeable arch, HasCallStack, MonadIO m, PB.KnownBinary bin, IsTreeBuilder '(sym,arch) e m)
  => PMC.EquivalenceContext sym arch
  -> PB.ConcreteBlock arch bin
  -> m (PE.Blocks arch bin)
getBlocksSingle ctx blk = do
  let (bin :: PB.WhichBinaryRepr bin) = WI.knownRepr
  ctx' <- PPa.get bin (PMC.binCtxs ctx)
  (lookupBlocks' ctx' blk) >>= \case
    Right (PDP.ParsedBlocks pbs) -> return $! PE.Blocks PC.knownRepr blk pbs
    Left err -> CMC.throwM err

getBlocks'
  :: (CMC.MonadThrow m, PPa.PatchPairM m, MS.SymArchConstraints arch, Typeable arch, HasCallStack, IsTreeBuilder '(sym,arch) e m)
  => PMC.EquivalenceContext sym arch
  -> PB.BlockPair arch
  -> m (PE.BlocksPair arch)
getBlocks' ctx pPair = PPa.forBins $ \bin -> do
  blk <- PPa.get bin pPair
  getBlocksSingle ctx blk

getBlocks ::
  HasCallStack =>
  PB.BlockPair arch ->
  EquivM sym arch (PE.BlocksPair arch)
getBlocks pPair = PPa.forBins $ \bin -> do
  blk <- PPa.get bin pPair
  PDP.ParsedBlocks pbs <- lookupBlocks blk
  return $! PE.Blocks PC.knownRepr blk pbs

lookupBlocks'
  :: (MS.SymArchConstraints arch, Typeable arch, HasCallStack, IsTreeBuilder '(sym,arch) e m)
  => PMC.BinaryContext arch bin
  -> PB.ConcreteBlock arch bin
  -> m (Either (PEE.InnerEquivalenceError arch) (PDP.ParsedBlocks arch))
lookupBlocks' binCtx b = do
  mfn <- PDP.parsedBlocksContaining b (PMC.parsedFunctionMap binCtx)
  case mfn of
    Just pbs -> return (Right pbs)
    Nothing  -> return (Left (PEE.UnknownFunctionEntry (PB.concreteAddress b)))

lookupBlocks ::
  forall sym arch bin.
  HasCallStack =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (PDP.ParsedBlocks arch)
lookupBlocks b = do
  let repr = PB.blockBinRepr b
  binCtx <- getBinCtx' repr
  ebs <- lookupBlocks' binCtx b
  case ebs of
    Left ierr -> do
      CME.throwError $ PEE.equivalenceErrorFor repr ierr
    Right blocks -> return blocks

-- | From a 'PB.ConcreteBlock', if it corresponds to the start of a
--   block, find a 'PB.ConcreteBlock' immediately following
--   the end of the corresponding 'MD.ParsedBlock'
nextBlock ::
  forall sym arch bin.
  HasCallStack =>
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Maybe (PB.ConcreteBlock arch bin))
nextBlock b = do
  let
    go :: forall ids. [MD.ParsedBlock arch ids] -> Maybe (PB.ConcreteBlock arch bin)
    go [] = Nothing
    go [_pb] = Nothing
    go (pb : pbNext : pbs) = case PA.segOffToAddr (MD.pblockAddr pb) == PB.concreteAddress b of
      True -> Just (PB.ConcreteBlock (PA.segOffToAddr (MD.pblockAddr pbNext)) PB.BlockEntryJump WI.knownRepr (PB.blockFunctionEntry b))
      False -> go (pbNext : pbs)
  binCtx <- getBinCtx @bin
  ebs <- lookupBlocks' binCtx b
  case ebs of
    Left _ -> return Nothing
    Right (PDP.ParsedBlocks blocks) -> return $ go blocks

-- | Construct a symbolic pointer for the given 'ConcreteBlock'
--
-- This is actually potentially a bit complicated because macaw assigns
-- relocatable addresses (i.e., segment /= 0) to code in position-independent
-- binaries.  As long as we are only analyzing single binaries and ignoring
-- their dependent shared libraries, it should be safe to just ignore the
-- segment that macaw assigns and treat everything as if there was only a single
-- static memory segment (modulo dynamic allocations).
--
-- NOTE: If we add the capability to load code from shared libraries, we will
-- need to be much more intentional about this and change how the PC region is
-- handled.
--
-- NOTE: This is assuming that data pointers are in the same region as code from
-- the macaw point of view. This needs to be verified
concreteToLLVM ::
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (CLM.LLVMPtr sym (MC.ArchAddrWidth arch))
concreteToLLVM blk = withSym $ \sym -> do
  -- we assume a distinct region for all executable code
  region <- CMR.asks envPCRegion
  let MM.MemAddr _base offset = PA.addrToMemAddr (PB.concreteAddress blk)
  liftIO $ do
    ptrOffset <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (toInteger offset))
    pure (CLM.LLVMPointer region ptrOffset)
