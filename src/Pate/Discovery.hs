{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines an interface to drive macaw code discovery and identify
-- corresponding blocks in an original and patched binary
module Pate.Discovery (
  discoverPairs,
  exactEquivalence,
  runDiscovery,
  mkConcreteBlock,
  lookupBlocks,
  getBlocks,
  getBlocks',
  matchesBlockTarget,
  concreteToLLVM
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as CMC
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Functor.Compose as DFC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           GHC.Stack ( HasCallStack, callStack )

import qualified Data.Macaw.BinaryLoader as MBL
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
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PR
import qualified Pate.SimState as PSS
import qualified Pate.SimulatorRegisters as PSR
import           Pate.Types
import qualified What4.ExprHelpers as WEH

--------------------------------------------------------
-- Block pair matching

-- | Compute all possible valid exit pairs from the given slice.
discoverPairs ::
  forall sym arch.
  SimBundle sym arch ->
  EquivM sym arch [PPa.PatchPair (BlockTarget arch)]
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
-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  BlockTarget arch PB.Original ->
  BlockTarget arch PB.Patched ->
  Bool
compatibleTargets blkt1 blkt2 =
  PB.concreteBlockEntry (targetCall blkt1) == PB.concreteBlockEntry (targetCall blkt2) &&
  case (targetReturn blkt1, targetReturn blkt2) of
    (Just blk1, Just blk2) -> PB.concreteBlockEntry blk1 == PB.concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

exactEquivalence ::
  PSS.SimInput sym arch PB.Original ->
  PSS.SimInput sym arch PB.Patched ->
  EquivM sym arch (WI.Pred sym)
exactEquivalence inO inP = withSym $ \sym -> do
  eqRel <- CMR.asks envBaseEquiv
  regsEqs <- liftIO $ PR.zipRegStates (PSS.simInRegs inO) (PSS.simInRegs inP) (PEq.applyRegEquivRelation (PEq.eqRelRegs eqRel))

  regsEq <- liftIO $ WEH.allPreds sym regsEqs
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  isPredSat heuristicTimeout regsEq >>= \case
    True -> return ()
    False -> CME.fail "exactEquivalence: regsEq: assumed false"
    
  memEq <- liftIO $ WI.isEq sym (MT.memArr (PSS.simInMem inO)) (MT.memArr (PSS.simInMem inP))

  isPredSat heuristicTimeout memEq >>= \case
    True -> return ()
    False -> CME.fail "exactEquivalence: memEq: assumed false"
    
  liftIO $ WI.andPred sym regsEq memEq

matchesBlockTarget ::
  forall sym arch.
  SimBundle sym arch ->
  BlockTarget arch PB.Original ->
  BlockTarget arch PB.Patched ->
  EquivM sym arch (WI.Pred sym)
matchesBlockTarget bundle blktO blktP = withSym $ \sym -> do
  -- true when the resulting IPs call the given block targets
  ptrO <- concreteToLLVM (targetCall blktO)
  ptrP <- concreteToLLVM (targetCall blktP)

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
  BlockTarget arch bin ->
  EquivM sym arch (CS.RegValue sym (CT.MaybeType (CLM.LLVMPointerType (MC.ArchAddrWidth arch))))
targetReturnPtr blkt | Just blk <- targetReturn blkt = withSym $ \sym -> do
  ptr <- concreteToLLVM blk
  return $ WP.justPartExpr sym ptr
targetReturnPtr _ = withSym $ \sym -> return $ WP.maybePartExpr sym Nothing


-- | From the given starting point, find all of the accessible
-- blocks
getSubBlocks ::
  forall sym arch bin.
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch [BlockTarget arch bin]
getSubBlocks b = withBinary @bin $
  do let addr = PB.concreteAddress b
     pfm <- PMC.parsedFunctionMap <$> getBinCtx @bin
     tgts <- case PMC.parsedFunctionContaining addr pfm of
       Right (_, Some pbm) -> do
         let pbs = PMC.parsedBlocksContaining addr pbm
         concat <$> mapM (concreteValidJumpTargets pbs) pbs
       Left allAddrs -> throwHere $ PEE.NoUniqueFunctionOwner addr allAddrs
     mapM_ validateBlockTarget tgts
     return tgts


concreteValidJumpTargets ::
  forall bin arch ids m.
  Monad m =>
  PB.KnownBinary bin =>
  PA.ValidArch arch =>
  [MD.ParsedBlock arch ids] ->
  MD.ParsedBlock arch ids ->
  m [BlockTarget arch bin]
concreteValidJumpTargets allPbs pb = do
  targets <- concreteJumpTargets pb
  let thisAddr = segOffToAddr (MD.pblockAddr pb)
  let addrs = map (segOffToAddr . MD.pblockAddr) allPbs
  let
    isTargetExternal btgt = not ((PB.concreteAddress (targetCall btgt)) `elem` addrs)
    isTargetBackJump btgt = (PB.concreteAddress (targetCall btgt)) < thisAddr
    isTargetArch btgt = PB.concreteBlockEntry (targetCall btgt) == PB.BlockEntryPostArch

    isTargetValid btgt = isTargetArch btgt || isTargetExternal btgt || isTargetBackJump btgt
  let validTargets = filter isTargetValid targets
  return validTargets

validateBlockTarget ::
  HasCallStack => PB.KnownBinary bin =>
  BlockTarget arch bin ->
  EquivM sym arch ()
validateBlockTarget tgt = do
  let blk = targetCall tgt
  case PB.concreteBlockEntry blk of
    PB.BlockEntryInitFunction -> do
      (manifestError $ lookupBlocks blk) >>= \case
        Left err -> throwHere $ PEE.InvalidCallTarget (PB.concreteAddress blk) err
        Right _ -> return ()
    _ -> return ()

mkConcreteBlock' ::
  PB.KnownBinary bin =>
  PB.BlockEntryKind arch ->
  PA.ConcreteAddress arch ->
  PB.ConcreteBlock arch bin
mkConcreteBlock' k a = PB.ConcreteBlock a k WI.knownRepr

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
  MC.RelocatableValue _ addr -> [PA.ConcreteAddress addr]
  MC.BVValue w bv |
    Just WI.Refl <- WI.testEquality w (MM.memWidthNatRepr @(MC.ArchAddrWidth arch)) ->
      [PA.ConcreteAddress (MM.absoluteAddr (MM.memWord (fromIntegral bv)))]
  MC.AssignedValue (MC.Assignment _ rhs) -> case rhs of
    MC.EvalApp (MC.Mux _ _ b1 b2) -> concreteValueAddress b1 ++ concreteValueAddress b2
    _ -> []
  _ -> []

concreteJumpTargets ::
  forall bin arch ids m.
  Monad m =>
  PB.KnownBinary bin =>
  PA.ValidArch arch =>
  MD.ParsedBlock arch ids ->
  m [BlockTarget arch bin]
concreteJumpTargets pb = case MD.pblockTermStmt pb of
  MD.ParsedCall st ret -> go (concreteNextIPs st) ret
  MD.PLTStub st _ _ -> case MapF.lookup (MC.ip_reg @(MC.ArchReg arch)) st of
    Just addr -> go (concreteValueAddress addr) Nothing
    _ -> return $ []
  MD.ParsedJump _ tgt -> do
    blk <- mkConcreteBlock PB.BlockEntryJump tgt
    return $ [ BlockTarget blk Nothing ]
  MD.ParsedBranch _ _ t f -> do
    blk_t <- mkConcreteBlock PB.BlockEntryJump t
    blk_f <- mkConcreteBlock PB.BlockEntryJump f
    return $ [ BlockTarget blk_t Nothing, BlockTarget blk_f Nothing ]
  MD.ParsedLookupTable _jt st _ _ -> go (concreteNextIPs st) Nothing
  MD.ParsedArchTermStmt _ st ret -> do
    ret_blk <- mapM (mkConcreteBlock PB.BlockEntryPostArch) ret
    return $ [ BlockTarget (mkConcreteBlock' PB.BlockEntryPostArch next) ret_blk
             | next <- (concreteNextIPs st) ]
  _ -> return []
  where
    go ::
      [PA.ConcreteAddress arch] ->
      Maybe (MC.ArchSegmentOff arch) ->
      m [BlockTarget arch bin]
    go next_ips ret = do
      ret_blk <- mapM (mkConcreteBlock PB.BlockEntryPostFunction) ret
      return $ [ BlockTarget (mkConcreteBlock' PB.BlockEntryInitFunction next) ret_blk | next <- next_ips ]

mkConcreteBlock ::
  Applicative m =>
  PA.ValidArch arch =>
  PB.KnownBinary bin =>
  PB.BlockEntryKind arch ->
  MC.ArchSegmentOff arch ->
  m (PB.ConcreteBlock arch bin)
mkConcreteBlock k a = pure (PB.getConcreteBlock a k WI.knownRepr)

-------------------------------------------------------
-- Driving macaw to generate the initial block map

addFunctionEntryHints
  :: (MM.MemWidth (MC.ArchAddrWidth arch))
  => proxy arch
  -> MM.Memory (MC.ArchAddrWidth arch)
  -> (name, Word64)
  -> ([Word64], [MC.ArchSegmentOff arch])
  -> ([Word64], [MC.ArchSegmentOff arch])
addFunctionEntryHints _ mem (_name, addrWord) (invalid, entries) =
  case MM.resolveAbsoluteAddr mem (fromIntegral addrWord) of
    Nothing -> (addrWord : invalid, entries)
    Just segOff -> (invalid, segOff : entries)


runDiscovery ::
  forall arch .
  PA.ValidArch arch =>
  PLE.LoadedELF arch ->
  PH.VerificationHints ->
  CME.ExceptT (PEE.EquivalenceError arch) IO ([Word64], MM.MemSegmentOff (MC.ArchAddrWidth arch), MD.DiscoveryState arch, PMC.ParsedFunctionMap arch)
runDiscovery elf hints = do
  let
    bin = PLE.loadedBinary elf
    archInfo = PLE.archInfo elf
  entries <- F.toList <$> MBL.entryPoints bin
  let mem = MBL.memoryImage bin
  let (invalidHints, hintedEntries) = F.foldr (addFunctionEntryHints (Proxy @arch) mem) ([], entries) (PH.functionEntries hints)
  let discoveryState = MD.cfgFromAddrs archInfo mem Map.empty hintedEntries []
  let pfm = PMC.buildParsedFunctionMap discoveryState
  return (invalidHints, head entries, discoveryState, pfm)

getBlocks'
  :: (CMC.MonadThrow m, MS.SymArchConstraints arch, Typeable arch, HasCallStack)
  => PMC.EquivalenceContext sym arch
  -> PPa.BlockPair arch
  -> m (PE.BlocksPair arch)
getBlocks' ctx pPair = do
  case (lookupBlocks' (PMC.originalCtx ctx) blkO, lookupBlocks' (PMC.rewrittenCtx ctx) blkP) of
    (Right (Some (DFC.Compose opbs)), Right (Some (DFC.Compose ppbs))) -> do
      let oBlocks = PE.Blocks blkO opbs
      let pBlocks = PE.Blocks blkP ppbs
      return $! PPa.PatchPair oBlocks pBlocks
    (Left err, _) -> CMC.throwM err
    (_, Left err) -> CMC.throwM err
  where
    blkO = PPa.pOriginal pPair
    blkP = PPa.pPatched pPair

getBlocks ::
  HasCallStack =>
  PPa.BlockPair arch ->
  EquivM sym arch (PE.BlocksPair arch)
getBlocks pPair = do
  Some (DFC.Compose opbs) <- lookupBlocks blkO
  let oBlocks = PE.Blocks blkO opbs
  Some (DFC.Compose ppbs) <- lookupBlocks blkP
  let pBlocks = PE.Blocks blkP ppbs
  return $ PPa.PatchPair oBlocks pBlocks
  where
    blkO = PPa.pOriginal pPair
    blkP = PPa.pPatched pPair

lookupBlocks'
  :: (MS.SymArchConstraints arch, Typeable arch, HasCallStack)
  => PMC.BinaryContext sym arch bin
  -> PB.ConcreteBlock arch bin
  -> Either (PEE.InnerEquivalenceError arch) (Some (DFC.Compose [] (MD.ParsedBlock arch)))
lookupBlocks' binCtx b = do
  case PMC.parsedFunctionContaining addr (PMC.parsedFunctionMap binCtx) of
    Right (funAddr, Some pbm) ->
      case PB.concreteBlockEntry b of
        PB.BlockEntryInitFunction
          | funAddr /= addr -> Left (PEE.LookupNotAtFunctionStart callStack funAddr addr)
        _ -> do
          let result = PMC.parsedBlocksContaining addr pbm
          return $ Some (DFC.Compose result)
    Left addrs -> Left (PEE.NoUniqueFunctionOwner addr addrs)

  where
    addr = PB.concreteAddress b

lookupBlocks ::
  forall sym arch bin.
  HasCallStack =>
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Some (DFC.Compose [] (MD.ParsedBlock arch)))
lookupBlocks b = do
  binCtx <- getBinCtx @bin
  case lookupBlocks' binCtx b of
    Left ierr -> do
      let binRep :: PB.WhichBinaryRepr bin
          binRep = PC.knownRepr
      let err = PEE.EquivalenceError { PEE.errWhichBinary = Just (Some binRep)
                                     , PEE.errStackTrace = Just callStack
                                     , PEE.errEquivError = ierr
                                     }
      CME.throwError err
    Right blocks -> return blocks

segOffToAddr ::
  MC.ArchSegmentOff arch ->
  PA.ConcreteAddress arch
segOffToAddr off = PA.addressFromMemAddr (MM.segoffAddr off)

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
  let PA.ConcreteAddress (MM.MemAddr _base offset) = PB.concreteAddress blk
  liftIO $ do
    ptrOffset <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (toInteger offset))
    pure (CLM.LLVMPointer region ptrOffset)
