{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.Validity (
    validInitState
  , validRegister
  , validConcreteReads
  ) where

import           Control.Applicative ( liftA2 )
import qualified Control.Monad.Reader as CMR
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Sequence as Seq
import           GHC.TypeLits
import qualified Data.Word.Indexed as W
import qualified What4.Interface as W4

import qualified Data.Macaw.BinaryLoader.PPC as TOC
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Loader.Wrapper as PLW
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR

wLit :: (1 <= w) => W.W w -> EquivM sym arch (W4.SymBV sym w)
wLit w = withSymIO $ \sym -> W4.bvLit sym (W.rep w) (BVS.mkBV (W.rep w) (W.unW w))

functionSegOffs ::
  PPa.BlockPair arch ->
  EquivM sym arch (MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)
functionSegOffs pPair = do
  PPa.PatchPair (PE.Blocks _ (pblkO:_)) (PE.Blocks _ (pblkP:_)) <- PD.getBlocks pPair
  return $ (MD.pblockAddr pblkO, MD.pblockAddr pblkP)

getCurrentTOCs :: PA.HasTOCReg arch => EquivM sym arch (W.W (MM.ArchAddrWidth arch), W.W (MM.ArchAddrWidth arch))
getCurrentTOCs = do
  -- (tocO, tocP) <- CMR.asks envTocs
  PLW.SomeLoadedBinary binO <- CMR.asks (binary . originalCtx . envCtx)
  PLW.SomeLoadedBinary binP <- CMR.asks (binary . rewrittenCtx . envCtx)
  let tocO = TOC.getTOC binO
  let tocP = TOC.getTOC binP
  curFuncs <- CMR.asks envCurrentFunc
  (addrO, addrP) <- functionSegOffs curFuncs
  wO <- case TOC.lookupTOC tocO addrO of
    Just w -> return w
    Nothing -> throwHere $ PEE.MissingTOCEntry addrO
  wP <- case TOC.lookupTOC tocP addrP of
    Just w -> return w
    Nothing -> throwHere $ PEE.MissingTOCEntry addrP
  return $ (wO, wP)


validInitState ::
  Maybe (PPa.BlockPair arch) ->
  SimState sym arch PB.Original ->
  SimState sym arch PB.Patched ->
  EquivM sym arch (AssumptionFrame sym)
validInitState mpPair stO stP = do
  fmap mconcat $ PRe.zipRegStates (simRegs stO) (simRegs stP) $ \r vO vP -> do
    validO <- validRegister (fmap PPa.pOriginal mpPair) vO r
    validP <- validRegister (fmap PPa.pPatched mpPair) vP r
    return $ validO <> validP

validRegister ::
  forall bin sym arch tp.
  PB.KnownBinary bin =>
  -- | if this register is an initial state, the corresponding
  -- starting block
  Maybe (PB.ConcreteBlock arch bin) ->
  PSR.MacawRegEntry sym tp ->
  MM.ArchReg arch tp ->
  EquivM sym arch (AssumptionFrame sym)
validRegister mblockStart entry r = withSym $ \sym ->
  case PRe.registerCase (PSR.macawRegRepr entry) r of
    PRe.RegIP -> case mblockStart of
      Just blockStart -> do
        ptrO <- PD.concreteToLLVM blockStart
        liftIO $ macawRegBinding sym entry (PSR.ptrToEntry ptrO)
      Nothing -> return $ mempty
    PRe.RegSP -> do
      stackRegion <- CMR.asks envStackRegion
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      iRegion <- liftIO $ W4.natToInteger sym region
      iStackRegion <- liftIO $ W4.natToInteger sym stackRegion
      return $ exprBinding iRegion iStackRegion
    PRe.RegBV -> liftIO $ do
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      zero <- W4.intLit sym 0
      iRegion <- W4.natToInteger sym region
      return $ exprBinding iRegion zero
    PRe.RegTOC -> do
      globalRegion <- CMR.asks envGlobalRegion
      (tocO, tocP) <- getCurrentTOCs
      tocBV <- case W4.knownRepr :: PB.WhichBinaryRepr bin of
        PB.OriginalRepr -> wLit tocO
        PB.PatchedRepr -> wLit tocP
      let targetToc = CLM.LLVMPointer globalRegion tocBV
      liftIO $ macawRegBinding sym entry (PSR.ptrToEntry targetToc)
    _ -> return $ mempty

-- | Reads from immutable data have known results.
-- We collect all the reads that occurred during the trace, and then
-- assert that those values are necessarily equivalent to the concrete
-- value from the binary
validConcreteReads ::
  forall bin sym arch.
  PB.KnownBinary bin =>
  SimOutput sym arch bin ->
  EquivM sym arch (AssumptionFrame sym)
validConcreteReads stOut = withSym $ \sym -> do
  binCtx <- getBinCtx @bin
  PLW.SomeLoadedBinary lb <- return (binary binCtx)
  let
    binmem = MBL.memoryImage lb

    go :: Seq.Seq (MT.MemOp sym (MM.ArchAddrWidth arch)) -> EquivM sym arch (AssumptionFrame sym)
    go mops = do
      flatops <- fmap F.toList $ liftIO $ MT.flatMemOps sym mops
      fmap mconcat $ mapM readConcrete flatops

    readConcrete ::
      MT.MemOp sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (AssumptionFrame sym)
    readConcrete (MT.MemOp (CLM.LLVMPointer reg off) dir _ sz val end) = do
      case (W4.asNat reg, W4.asBV off, dir) of
        (Just 0, Just off', MT.Read) -> do
          let
            addr :: MM.MemAddr (MM.ArchAddrWidth arch) =
              MM.absoluteAddr (MM.memWord (fromIntegral (BVS.asUnsigned off')))
          W4.LeqProof <- return $ W4.leqMulPos (W4.knownNat @8) sz
          let bits = W4.natMultiply (W4.knownNat @8) sz
          case doStaticRead @arch binmem addr bits end of
            Just bv -> liftIO $ do
              let CLM.LLVMPointer _ bvval = val
              lit_val <- W4.bvLit sym bits bv
              -- FIXME: update when memory model has regions
              -- unclear what to assert about the region
              return $ exprBinding bvval lit_val
            Nothing -> return $ mempty
        _ -> return $ mempty
    readConcrete (MT.MergeOps _ seq1 seq2) = liftA2 (<>) (go seq1) (go seq2)
  go (MT.memSeq $ simOutMem $ stOut)

doStaticRead ::
  forall arch w .
  MM.Memory (MM.ArchAddrWidth arch) ->
  MM.MemAddr (MM.ArchAddrWidth arch) ->
  W4.NatRepr w ->
  MM.Endianness ->
  Maybe (BVS.BV w)
doStaticRead mem addr w end = case MM.asSegmentOff mem addr of
  Just segoff | MMP.isReadonly $ MM.segmentFlags $ MM.segoffSegment segoff ->
    fmap (BVS.mkBV w) $
    case (W4.intValue w, end) of
      (8, _) -> liftErr $ MM.readWord8 mem addr
      (16, MM.BigEndian) -> liftErr $ MM.readWord16be mem addr
      (16, MM.LittleEndian) -> liftErr $ MM.readWord16le mem addr
      (32, MM.BigEndian) -> liftErr $ MM.readWord32be mem addr
      (32, MM.LittleEndian) -> liftErr $ MM.readWord32le mem addr
      (64, MM.BigEndian) -> liftErr $ MM.readWord64be mem addr
      (64, MM.LittleEndian) -> liftErr $ MM.readWord64le mem addr
      _ -> Nothing
  _ -> Nothing
  where
    liftErr :: Integral a => Either e a -> Maybe Integer
    liftErr (Left _) = Nothing
    liftErr (Right a) = Just (fromIntegral a)
