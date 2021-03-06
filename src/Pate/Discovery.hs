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
  runDiscovery,
  mkConcreteBlock,
  lookupBlocks,
  getBlocks,
  matchesBlockTarget,
  concreteToLLVM
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( when )
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Except as CME
import qualified Control.Monad.Reader as CMR
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Functor.Compose as DFC
import qualified Data.IntervalMap.Strict as IM
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Traversable as DT
import           Data.Word ( Word64 )

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

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Equivalence as PEq
import qualified Pate.Hints as PH
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
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
  EquivM sym arch [(BlockTarget arch Original, BlockTarget arch Patched)]
discoverPairs bundle = do
  precond <- exactEquivalence (simInO bundle) (simInP bundle)

  blksO <- getSubBlocks (PSS.simInBlock $ simInO $ bundle)
  blksP <- getSubBlocks (PSS.simInBlock $ simInP $ bundle)

  let
    allCalls = [ (blkO, blkP)
               | blkO <- blksO
               , blkP <- blksP
               , compatibleTargets blkO blkP]

  blocks <- getBlocks $ PSS.simPair bundle

  validTargets <- fmap catMaybes $
    DT.forM allCalls $ \(blktO, blktP) -> do
      matches <- matchesBlockTarget bundle blktO blktP
      check <- withSymIO $ \sym -> WI.andPred sym precond matches
      startTimer $ checkSatisfiableWithModel (Minutes 1) "check" check $ \satRes -> do
        let
          emit r = emitEvent (PE.DiscoverBlockPair blocks blktO blktP r)
        case satRes of
          WR.Sat _ -> do
            emit PE.Reachable
            return $ Just $ (blktO, blktP)
          WR.Unsat _ -> do
            emit PE.Unreachable
            return Nothing
          WR.Unknown -> do
            emit PE.InconclusiveTarget
            throwHere InconclusiveSAT
  return validTargets

-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  BlockTarget arch Original ->
  BlockTarget arch Patched ->
  Bool
compatibleTargets blkt1 blkt2 =
  concreteBlockEntry (targetCall blkt1) == concreteBlockEntry (targetCall blkt2) &&
  case (targetReturn blkt1, targetReturn blkt2) of
    (Just blk1, Just blk2) -> concreteBlockEntry blk1 == concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

exactEquivalence ::
  PSS.SimInput sym arch Original ->
  PSS.SimInput sym arch Patched ->
  EquivM sym arch (WI.Pred sym)
exactEquivalence inO inP = withSym $ \sym -> do
  eqRel <- CMR.asks envBaseEquiv
  regsEqs <- liftIO $ zipRegStates (PSS.simInRegs inO) (PSS.simInRegs inP) (PEq.applyRegEquivRelation (PEq.eqRelRegs eqRel))
  regsEq <- liftIO $ WEH.allPreds sym regsEqs
  memEq <- liftIO $ WI.isEq sym (MT.memArr (PSS.simInMem inO)) (MT.memArr (PSS.simInMem inP))
  liftIO $ WI.andPred sym regsEq memEq

matchesBlockTarget ::
  forall sym arch.
  SimBundle sym arch ->
  BlockTarget arch Original ->
  BlockTarget arch Patched ->
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
  KnownBinary bin =>
  ConcreteBlock arch bin ->
  EquivM sym arch [BlockTarget arch bin]
getSubBlocks b = withBinary @bin $ do
  pfm <- parsedFunctionMap <$> getBinCtx @bin
  case Map.assocs $ Map.unions $ fmap snd $ IM.lookupLE i pfm of
    [(_, Some (ParsedBlockMap pbm))] -> do
      let pbs = concat $ IM.elems $ IM.intersecting pbm i
      concat <$> mapM (concreteValidJumpTargets pbs) pbs
    blks -> throwHere $ NoUniqueFunctionOwner i (fst <$> blks)
  where
  start@(ConcreteAddress saddr) = concreteAddress b
  end = ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
  i = IM.OpenInterval start end

concreteValidJumpTargets ::
  forall bin sym arch ids.
  KnownBinary bin =>
  ValidArch arch =>
  [MD.ParsedBlock arch ids] ->
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch bin]
concreteValidJumpTargets allPbs pb = do
  targets <- concreteJumpTargets pb
  thisAddr <- segOffToAddr (MD.pblockAddr pb)
  addrs <- mapM (segOffToAddr . MD.pblockAddr) allPbs
  let
    isTargetExternal btgt = not ((concreteAddress (targetCall btgt)) `elem` addrs)
    isTargetBackJump btgt = (concreteAddress (targetCall btgt)) < thisAddr
    isTargetArch btgt = concreteBlockEntry (targetCall btgt) == BlockEntryPostArch

    isTargetValid btgt = isTargetArch btgt || isTargetExternal btgt || isTargetBackJump btgt
  let validTargets = filter isTargetValid targets
  mapM_ validateBlockTarget validTargets
  return validTargets

validateBlockTarget ::
  KnownBinary bin =>
  BlockTarget arch bin ->
  EquivM sym arch ()
validateBlockTarget tgt = do
  let blk = targetCall tgt
  case concreteBlockEntry blk of
    BlockEntryInitFunction -> do
      (manifestError $ lookupBlocks blk) >>= \case
        Left _ -> throwHere $ InvalidCallTarget $ concreteAddress blk
        Right _ -> return ()
    _ -> return ()

mkConcreteBlock ::
  KnownBinary bin =>
  BlockEntryKind arch ->
  MC.ArchSegmentOff arch ->
  EquivM sym arch (ConcreteBlock arch bin)
mkConcreteBlock k a = case getConcreteBlock a k WI.knownRepr of
  Just blk -> return blk
  _ -> throwHere $ NonConcreteParsedBlockAddress a

mkConcreteBlock' ::
  KnownBinary bin =>
  BlockEntryKind arch ->
  ConcreteAddress arch ->
  ConcreteBlock arch bin
mkConcreteBlock' k a = ConcreteBlock a k WI.knownRepr

concreteNextIPs ::
  ValidArch arch =>
  MC.RegState (MC.ArchReg arch) (MC.Value arch ids) ->
  [ConcreteAddress arch]
concreteNextIPs st = concreteValueAddress $ st ^. MC.curIP

concreteValueAddress ::
  forall arch ids.
  ValidArch arch =>
  MC.Value arch ids (MT.BVType (MC.ArchAddrWidth arch)) ->
  [ConcreteAddress arch]
concreteValueAddress = \case
  MC.RelocatableValue _ addr -> [ConcreteAddress addr]
  MC.BVValue w bv |
    Just WI.Refl <- WI.testEquality w (MM.memWidthNatRepr @(MC.ArchAddrWidth arch)) ->
      [ConcreteAddress (MM.absoluteAddr (MM.memWord (fromIntegral bv)))]
  MC.AssignedValue (MC.Assignment _ rhs) -> case rhs of
    MC.EvalApp (MC.Mux _ _ b1 b2) -> concreteValueAddress b1 ++ concreteValueAddress b2
    _ -> []
  _ -> []

concreteJumpTargets ::
  forall bin sym arch ids.
  KnownBinary bin =>
  ValidArch arch =>
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch bin]
concreteJumpTargets pb = case MD.pblockTermStmt pb of
  MD.ParsedCall st ret -> go (concreteNextIPs st) ret
  MD.PLTStub st _ _ -> case MapF.lookup (MC.ip_reg @(MC.ArchReg arch)) st of
    Just addr -> go (concreteValueAddress addr) Nothing
    _ -> return $ []
  MD.ParsedJump _ tgt -> do
    blk <- mkConcreteBlock BlockEntryJump tgt
    return $ [ BlockTarget blk Nothing ]
  MD.ParsedBranch _ _ t f -> do
    blk_t <- mkConcreteBlock BlockEntryJump t
    blk_f <- mkConcreteBlock BlockEntryJump f
    return $ [ BlockTarget blk_t Nothing, BlockTarget blk_f Nothing ]
  MD.ParsedLookupTable _jt st _ _ -> go (concreteNextIPs st) Nothing
  MD.ParsedArchTermStmt _ st ret -> do
    ret_blk <- mapM (mkConcreteBlock BlockEntryPostArch) ret
    return $ [ BlockTarget (mkConcreteBlock' BlockEntryPostArch next) ret_blk
             | next <- (concreteNextIPs st) ]
  _ -> return []
  where
    go ::
      [ConcreteAddress arch] ->
      Maybe (MC.ArchSegmentOff arch) ->
      EquivM sym arch [BlockTarget arch bin]
    go next_ips ret = do
      ret_blk <- mapM (mkConcreteBlock BlockEntryPostFunction) ret
      return $ [ BlockTarget (mkConcreteBlock' BlockEntryInitFunction next) ret_blk | next <- next_ips ]

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
  ValidArch arch =>
  PB.LoadedELF arch ->
  PH.VerificationHints ->
  CME.ExceptT (EquivalenceError arch) IO ([Word64], MM.MemSegmentOff (MC.ArchAddrWidth arch), ParsedFunctionMap arch)
runDiscovery elf hints = do
  let
    bin = PB.loadedBinary elf
    archInfo = PB.archInfo elf
  entries <- F.toList <$> MBL.entryPoints bin
  let mem = MBL.memoryImage bin
  let (invalidHints, hintedEntries) = F.foldr (addFunctionEntryHints (Proxy @arch) mem) ([], entries) (PH.functionEntries hints)
  pfm <- goDiscoveryState $
    MD.cfgFromAddrs archInfo mem Map.empty hintedEntries []
  return (invalidHints, head entries, pfm)
  where
  goDiscoveryState ds = id
    . fmap (IM.unionsWith Map.union)
    . mapM goSomeDiscoveryFunInfo
    . Map.assocs
    $ ds ^. MD.funInfo
  goSomeDiscoveryFunInfo (entrySegOff, Some dfi) = markEntryPoint entrySegOff <$> goDiscoveryFunInfo dfi
  goDiscoveryFunInfo dfi = fmap (ParsedBlockMap . IM.fromListWith (++)) . sequence $
    [ (\addrs -> (addrs, [pb])) <$> archSegmentOffToInterval blockSegOff (MD.blockSize pb)
    | (blockSegOff, pb) <- Map.assocs (dfi ^. MD.parsedBlocks)
    ]

archSegmentOffToInterval ::
  (ValidArch arch, CME.MonadError (EquivalenceError arch) m) =>
  MC.ArchSegmentOff arch ->
  Int ->
  m (IM.Interval (ConcreteAddress arch))
archSegmentOffToInterval segOff size = case MM.segoffAsAbsoluteAddr segOff of
  Just w -> pure (IM.IntervalCO start (start `addressAddOffset` fromIntegral size))
    where start = concreteFromAbsolute w
  Nothing -> CME.throwError $ equivalenceError $ StrangeBlockAddress segOff


getBlocks ::
  PatchPair arch ->
  EquivM sym arch (PE.BlocksPair arch)
getBlocks pPair = do
  Some (DFC.Compose opbs) <- lookupBlocks blkO
  let oBlocks = PE.Blocks blkO opbs
  Some (DFC.Compose ppbs) <- lookupBlocks blkP
  let pBlocks = PE.Blocks blkP ppbs
  return $ PE.BlocksPair oBlocks pBlocks
  where
    blkO = pOrig pPair
    blkP = pPatched pPair

lookupBlocks ::
  forall sym arch bin.
  KnownBinary bin =>
  ConcreteBlock arch bin ->
  EquivM sym arch (Some (DFC.Compose [] (MD.ParsedBlock arch)))
lookupBlocks b = do
  binCtx <- getBinCtx @bin
  let pfm = parsedFunctionMap binCtx
  case Map.assocs $ Map.unions $ fmap snd $ IM.lookupLE i pfm of
    [(start', Some (ParsedBlockMap pbm))] -> do
      case concreteBlockEntry b of
        BlockEntryInitFunction -> do
          funAddr <- segOffToAddr start'
          when (funAddr /= start) $
            throwHere $ LookupNotAtFunctionStart start
        _ -> return ()
      let result = concat $ IM.elems $ IM.intersecting pbm i
      return $ Some (DFC.Compose result)
    blks -> throwHere $ NoUniqueFunctionOwner i (fst <$> blks)
  where
  start@(ConcreteAddress addr) = concreteAddress b
  end = ConcreteAddress (MM.MemAddr (MM.addrBase addr) maxBound)
  i = IM.OpenInterval start end

segOffToAddr ::
  MC.ArchSegmentOff arch ->
  EquivM sym arch (ConcreteAddress arch)
segOffToAddr off = concreteFromAbsolute <$>
  liftMaybe (MM.segoffAsAbsoluteAddr off) (NonConcreteParsedBlockAddress off)

liftMaybe :: Maybe a -> InnerEquivalenceError arch -> EquivM sym arch a
liftMaybe Nothing e = throwHere e
liftMaybe (Just a) _ = pure a

concreteToLLVM ::
  ConcreteBlock arch bin ->
  EquivM sym arch (CLM.LLVMPtr sym (MC.ArchAddrWidth arch))
concreteToLLVM blk = withSym $ \sym -> do
  -- we assume a distinct region for all executable code
  region <- CMR.asks envPCRegion
  let addr = absoluteAddress (concreteAddress blk)
  liftIO $ do
    offset <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (toInteger addr))
    pure (CLM.LLVMPointer region offset)
