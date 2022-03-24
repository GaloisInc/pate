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
  matchesBlockTarget,
  matchingExits,
  isMatchingCall,
  concreteToLLVM
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad (forM)
import qualified Control.Monad.Catch as CMC
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO, MonadIO )
import qualified Control.Monad.Reader as CMR
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import           Data.Functor.Const
import qualified Data.List.NonEmpty as DLN
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           GHC.Stack ( HasCallStack, callStack )

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.ELF as MBLE
import qualified Data.Macaw.CFG as MC
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
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimState as PSS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.SymbolTable as PSym
import qualified What4.ExprHelpers as WEH

--------------------------------------------------------
-- Block pair matching

-- | Compute all possible valid exit pairs from the given slice.
discoverPairs ::
  forall sym arch.
  SimBundle sym arch ->
  EquivM sym arch [PPa.PatchPair (PB.BlockTarget arch)]
discoverPairs bundle = do
  lookupBlockCache envExitPairsCache pPair >>= \case
    Just pairs -> return pairs
    Nothing -> do
      precond <- exactEquivalence (PSS.simInO bundle) (PSS.simInP bundle)
      blksO <- getSubBlocks (PSS.simInBlock $ PSS.simInO $ bundle)
      blksP <- getSubBlocks (PSS.simInBlock $ PSS.simInP $ bundle)

      let
        allCalls = [ (blkO, blkP)
                   | blkO <- blksO
                   , blkP <- blksP
                   , compatibleTargets blkO blkP]
      blocks <- getBlocks $ PSS.simPair bundle

      result <- Par.forMPar allCalls $ \(blktO, blktP) -> startTimer $ do
        let emit r = emitEvent (PE.DiscoverBlockPair blocks blktO blktP r)
        matches <- matchesBlockTarget bundle blktO blktP
        check <- withSymIO $ \sym -> WI.andPred sym precond matches
        case WI.asConstantPred check of
          Just True -> do
            emit PE.Reachable
            return $ Par.Immediate $ Just $ PPa.PatchPair blktO blktP
          Just False -> do
            emit PE.Unreachable
            return $ Par.Immediate $ Nothing
          _ ->  do
            goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
            Par.promise $ do
              er <- checkSatisfiableWithModel goalTimeout "check" check $ \satRes -> do
                case satRes of
                  WR.Sat _ -> do
                    emit PE.Reachable
                    return $ Just $ PPa.PatchPair blktO blktP
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
      joined <- fmap catMaybes $ Par.joinFuture result
      modifyBlockCache envExitPairsCache pPair (++) joined
      return joined
  where
    pPair = PSS.simPair bundle

matchingExits ::
  forall sym arch.
  SimBundle sym arch ->
  MS.MacawBlockEndCase ->
  EquivM sym arch (WI.Pred sym)
matchingExits bundle ecase = withSym $ \sym -> do
  case1 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (PSS.simOutBlockEnd $ PSS.simOutO bundle) ecase
  case2 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (PSS.simOutBlockEnd $ PSS.simOutP bundle) ecase
  liftIO $ WI.andPred sym case1 case2

-- | True when both the patched and original program necessarily end with
-- a call to the same function, assuming exact initial equivalence.
isMatchingCall ::
  forall sym arch.
  SimBundle sym arch ->
  EquivM sym arch Bool
isMatchingCall bundle = withSym $ \sym -> do
  eqIPs <- liftIO $ MT.llvmPtrEq sym (PSR.macawRegValue ipO) (PSR.macawRegValue ipP)
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- TODO: Why are some of the calls being classified as Arch exits?
  isCall <- matchingExits bundle MS.MacawBlockEndCall
  isArch <- matchingExits bundle MS.MacawBlockEndArch
  isExpectedExit <- liftIO $ WI.orPred sym isArch isCall
  goal <- liftIO $ WI.andPred sym eqIPs isExpectedExit
  withAssumption_ (exactEquivalence (PSS.simInO bundle) (PSS.simInP bundle)) $
    isPredTrue' goalTimeout goal
  where
    ipO = (PSS.simOutRegs $ PSS.simOutO bundle) ^. MC.curIP
    ipP = (PSS.simOutRegs $ PSS.simOutP bundle) ^. MC.curIP

-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  PB.BlockTarget arch PB.Original ->
  PB.BlockTarget arch PB.Patched ->
  Bool
compatibleTargets blkt1 blkt2 =
  PB.concreteBlockEntry (PB.targetCall blkt1) == PB.concreteBlockEntry (PB.targetCall blkt2) &&
  case (PB.targetReturn blkt1, PB.targetReturn blkt2) of
    (Just blk1, Just blk2) -> PB.concreteBlockEntry blk1 == PB.concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

exactEquivalence ::
  PSS.SimInput sym arch PB.Original ->
  PSS.SimInput sym arch PB.Patched ->
  EquivM sym arch (WI.Pred sym)
exactEquivalence inO inP = withSym $ \sym -> do
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

matchesBlockTarget ::
  forall sym arch.
  SimBundle sym arch ->
  PB.BlockTarget arch PB.Original ->
  PB.BlockTarget arch PB.Patched ->
  EquivM sym arch (WI.Pred sym)
matchesBlockTarget bundle blktO blktP = withSym $ \sym -> do
  -- true when the resulting IPs call the given block targets
  ptrO <- concreteToLLVM (PB.targetCall blktO)
  ptrP <- concreteToLLVM (PB.targetCall blktP)

  eqCall <- liftIO $ do
    eqO <- MT.llvmPtrEq sym ptrO (PSR.macawRegValue ipO)
    eqP <- MT.llvmPtrEq sym ptrP (PSR.macawRegValue ipP)
    WI.andPred sym eqO eqP

  -- true when the resulting return IPs match the given block return addresses
  targetRetO <- targetReturnPtr blktO
  targetRetP <- targetReturnPtr blktP

  eqRet <- liftIO $ do
    eqRetO <- liftPartialRel sym (MT.llvmPtrEq sym) retO targetRetO
    eqRetP <- liftPartialRel sym (MT.llvmPtrEq sym) retP targetRetP
    WI.andPred sym eqRetO eqRetP

  liftIO $ WI.andPred sym eqCall eqRet
  where
    regsO = PSS.simOutRegs $ PSS.simOutO bundle
    regsP = PSS.simOutRegs $ PSS.simOutP bundle

    ipO = regsO ^. MC.curIP
    ipP = regsP ^. MC.curIP

    retO = MS.blockEndReturn (Proxy @arch) $ PSS.simOutBlockEnd $ PSS.simOutO bundle
    retP = MS.blockEndReturn (Proxy @arch) $ PSS.simOutBlockEnd $ PSS.simOutP bundle

liftPartialRel ::
  CB.IsSymInterface sym =>
  sym ->
  (a -> a -> IO (WI.Pred sym)) ->
  WP.PartExpr (WI.Pred sym) a ->
  WP.PartExpr (WI.Pred sym) a ->
  IO (WI.Pred sym)
liftPartialRel sym rel (WP.PE p1 e1) (WP.PE p2 e2) = do
  eqPreds <- WI.isEq sym p1 p2
  bothConds <- WI.andPred sym p1 p2
  rel' <- rel e1 e2
  justCase <- WI.impliesPred sym bothConds rel'
  WI.andPred sym eqPreds justCase
liftPartialRel sym _ WP.Unassigned WP.Unassigned = return $ WI.truePred sym
liftPartialRel sym _ WP.Unassigned (WP.PE p2 _) = WI.notPred sym p2
liftPartialRel sym _ (WP.PE p1 _) WP.Unassigned = WI.notPred sym p1

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
     mtgt <- liftIO $ PDP.parsedBlocksContaining b pfm
     tgts <- case mtgt of
       Just (PDP.ParsedBlocks pbs) ->
         concat <$> mapM (\x -> concreteValidJumpTargets b pbs x) pbs
       Nothing -> throwHere $ PEE.UnknownFunctionEntry addr
     mapM_ (\x -> validateBlockTarget x) tgts
     return tgts


concreteValidJumpTargets ::
  PA.ValidArch arch =>
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  [MD.ParsedBlock arch ids] ->
  MD.ParsedBlock arch ids ->
  EquivM sym arch [PB.BlockTarget arch bin]
concreteValidJumpTargets from allPbs pb = do
  targets <- concreteJumpTargets from pb
  let
      thisAddr = PA.segOffToAddr (MD.pblockAddr pb)
      addrs = map (PA.segOffToAddr . MD.pblockAddr) allPbs

      isTargetExternal btgt = not ((PB.concreteAddress (PB.targetCall btgt)) `elem` addrs)
      isTargetBackJump btgt = (PB.concreteAddress (PB.targetCall btgt)) < thisAddr
      isTargetArch btgt = PB.concreteBlockEntry (PB.targetCall btgt) == PB.BlockEntryPostArch

      isTargetValid btgt = isTargetArch btgt || isTargetExternal btgt || isTargetBackJump btgt

  return $ filter isTargetValid targets

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
    return [ jumpTarget from t, jumpTarget from f ]

  MD.ParsedLookupTable _jt st _ _ ->
    return [ jumpTarget' from next | next <- concreteNextIPs st ]

  MD.ParsedArchTermStmt _ st ret -> do
    let ret_blk = fmap (PB.mkConcreteBlock from PB.BlockEntryPostArch) ret
    return [ PB.BlockTarget (PB.mkConcreteBlock' from PB.BlockEntryPreArch next) ret_blk
           | next <- (concreteNextIPs st)
           ]

  MD.ParsedReturn{} -> return []
  MD.ParsedTranslateError{} -> return []
  MD.ClassifyFailure{} -> return []

jumpTarget ::
    PB.ConcreteBlock arch bin ->
    MC.ArchSegmentOff arch ->
    PB.BlockTarget arch bin
jumpTarget from to = PB.BlockTarget (PB.mkConcreteBlock from PB.BlockEntryJump to) Nothing

jumpTarget' ::
    PB.ConcreteBlock arch bin ->
    PA.ConcreteAddress arch ->
    PB.BlockTarget arch bin
jumpTarget' from to = PB.BlockTarget (PB.mkConcreteBlock' from PB.BlockEntryJump to) Nothing

callTargets ::
    forall bin arch sym .
    HasCallStack =>
    PB.KnownBinary bin =>
    PB.ConcreteBlock arch bin ->
    [PA.ConcreteAddress arch] ->
    Maybe (MC.ArchSegmentOff arch) ->
    EquivM sym arch [PB.BlockTarget arch bin]
callTargets from next_ips ret = do
   let ret_blk = fmap (PB.mkConcreteBlock from PB.BlockEntryPostFunction) ret
   binCtx <- getBinCtx @bin
   let mem = MBL.memoryImage (PMC.binary binCtx)
   forM next_ips $ \next -> do
     let nextMem = PA.addrToMemAddr next
     let Just segoff = MM.resolveRegionOff mem (MM.addrBase nextMem) (MM.addrOffset nextMem)
     let fe = PB.FunctionEntry { PB.functionSegAddr = segoff
                               , PB.functionSymbol = Nothing
                               , PB.functionBinRepr = PC.knownRepr
                               }
     let pb = PB.functionEntryToConcreteBlock fe
     return (PB.BlockTarget pb ret_blk)

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
  :: (w ~ MC.ArchAddrWidth arch, MM.MemWidth w, HasCallStack)
  => MM.Memory w
  -> MD.AddrSymMap w
  -> PH.FunctionDescriptor
  -> CME.ExceptT (PEE.EquivalenceError arch) IO (MD.AddrSymMap w)
addAddrSym mem m funcDesc = do
  let symbol = TE.encodeUtf8 (PH.functionSymbol funcDesc)
  let addr0 = PH.functionAddress funcDesc
  case PM.resolveAbsoluteAddress mem (fromIntegral addr0) of
    Just segoff -> return (Map.insert segoff symbol m)
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
  Maybe FilePath ->
  PB.WhichBinaryRepr bin ->
  Map.Map BS.ByteString (BVS.BV (MC.ArchAddrWidth arch)) ->
  PLE.LoadedELF arch ->
  PH.VerificationHints ->
  PC.PatchData ->
  CME.ExceptT (PEE.EquivalenceError arch) IO ([Word64], PMC.BinaryContext arch bin)
runDiscovery mCFGDir repr extraSyms elf hints pd = do
  let archInfo = PLE.archInfo elf
  entries <- MBL.entryPoints bin
  addrSyms <- F.foldlM (addAddrSym mem) mempty (fmap snd (PH.functionEntries hints))
  let (invalidHints, _hintedEntries) = F.foldr (addFunctionEntryHints (Proxy @arch) mem) ([], F.toList entries) (PH.functionEntries hints)

  pfm <- liftIO $ PDP.newParsedFunctionMap mem addrSyms archInfo mCFGDir pd
  let idx = F.foldl' addFunctionEntryHint Map.empty (PH.functionEntries hints)

  let startEntry = DLN.head entries
  let startEntry' = PB.FunctionEntry { PB.functionSegAddr = startEntry
                                     , PB.functionSymbol = Nothing
                                     , PB.functionBinRepr = repr
                                     }
  let abortFnEntry = do
        fnDesc <- lookup abortFnName (PH.functionEntries hints)
        abortFnAddr <- PM.resolveAbsoluteAddress mem (MM.memWord (PH.functionAddress fnDesc))
        return PB.FunctionEntry { PB.functionSegAddr = abortFnAddr
                                , PB.functionSymbol = Just (TE.encodeUtf8 abortFnName)
                                , PB.functionBinRepr = repr
                                }

  let symTab = buildSymbolTable hints extraSyms

  -- FIXME: Fill in the symbol table based on the hints and the dynamic symbol table
  return $ (invalidHints, PMC.BinaryContext bin pfm startEntry' hints idx abortFnEntry symTab)
  where
    bin = PLE.loadedBinary elf
    mem = MBL.memoryImage bin

    addFunctionEntryHint m (_, fd) =
      let addrWord = PH.functionAddress fd
      in case MBLE.resolveAbsoluteAddress mem (fromIntegral addrWord) of
           Nothing -> m
           Just segoff ->
             let addr = PA.segOffToAddr segoff
             in Map.insert addr fd m

getBlocks'
  :: (CMC.MonadThrow m, MS.SymArchConstraints arch, Typeable arch, HasCallStack, MonadIO m)
  => PMC.EquivalenceContext sym arch
  -> PPa.BlockPair arch
  -> m (PE.BlocksPair arch)
getBlocks' ctx pPair = do
  bs1 <- liftIO $ lookupBlocks' ctxO blkO
  bs2 <- liftIO $ lookupBlocks' ctxP blkP
  case (bs1, bs2) of
    (Right (PDP.ParsedBlocks opbs), Right (PDP.ParsedBlocks ppbs)) -> do
      let oBlocks = PE.Blocks PC.knownRepr blkO opbs
      let pBlocks = PE.Blocks PC.knownRepr blkP ppbs
      return $! PPa.PatchPair oBlocks pBlocks
    (Left err, _) -> CMC.throwM err
    (_, Left err) -> CMC.throwM err
  where
    binCtxs = PMC.binCtxs ctx
    ctxO = PPa.pOriginal binCtxs
    ctxP = PPa.pPatched binCtxs
    blkO = PPa.pOriginal pPair
    blkP = PPa.pPatched pPair

getBlocks ::
  HasCallStack =>
  PPa.BlockPair arch ->
  EquivM sym arch (PE.BlocksPair arch)
getBlocks pPair = do
  PDP.ParsedBlocks opbs <- lookupBlocks blkO
  let oBlocks = PE.Blocks PC.knownRepr blkO opbs
  PDP.ParsedBlocks ppbs <- lookupBlocks blkP
  let pBlocks = PE.Blocks PC.knownRepr blkP ppbs
  return $ PPa.PatchPair oBlocks pBlocks
  where
    blkO = PPa.pOriginal pPair
    blkP = PPa.pPatched pPair

lookupBlocks'
  :: (MS.SymArchConstraints arch, Typeable arch, HasCallStack, PB.KnownBinary bin)
  => PMC.BinaryContext arch bin
  -> PB.ConcreteBlock arch bin
  -> IO (Either (PEE.InnerEquivalenceError arch) (PDP.ParsedBlocks arch))
lookupBlocks' binCtx b = do
  mfn <- PDP.parsedBlocksContaining b (PMC.parsedFunctionMap binCtx)
  case mfn of
    Just pbs -> return (Right pbs)
    Nothing  -> return (Left (PEE.UnknownFunctionEntry (PB.concreteAddress b)))

lookupBlocks ::
  forall sym arch bin.
  HasCallStack =>
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (PDP.ParsedBlocks arch)
lookupBlocks b = do
  binCtx <- getBinCtx @bin
  ebs <- liftIO $ lookupBlocks' binCtx b
  case ebs of
    Left ierr -> do
      let binRep :: PB.WhichBinaryRepr bin
          binRep = PC.knownRepr
      let err = PEE.EquivalenceError { PEE.errWhichBinary = Just (Some binRep)
                                     , PEE.errStackTrace = Just callStack
                                     , PEE.errEquivError = ierr
                                     }
      CME.throwError err
    Right blocks -> return blocks

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
