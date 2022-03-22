{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Pate.Verification.Validity (
    validInitState
  , validRegister
  , validConcreteReads
  ) where

import qualified Control.Monad.Reader as CMR
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import           Data.Functor.Const
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Memory as PM
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import qualified Pate.Register.Traversal as PRt
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR

validInitState ::
  Maybe (PPa.BlockPair arch) ->
  SimState sym arch PB.Original ->
  SimState sym arch PB.Patched ->
  EquivM sym arch (AssumptionFrame sym)
validInitState mpPair stO stP = do
  fmap PRt.collapse $ PRt.zipWithRegStatesM (simRegs stO) (simRegs stP) $ \r vO vP -> do
    validO <- validRegister (fmap PPa.pOriginal mpPair) vO r
    validP <- validRegister (fmap PPa.pPatched mpPair) vP r
    return $ Const $ validO <> validP

validRegister ::
  forall bin sym arch tp.
  PB.KnownBinary bin =>
  -- | if this register is an initial state, the corresponding
  -- starting block
  Maybe (PB.ConcreteBlock arch bin) ->
  PSR.MacawRegEntry sym tp ->
  MM.ArchReg arch tp ->
  EquivM sym arch (AssumptionFrame sym)
validRegister mblockStart entry r = withSym $ \sym -> do
  PA.SomeValidArch (PA.validArchDedicatedRegisters -> hdr) <- CMR.asks envValidArch
  case PRe.registerCase hdr (PSR.macawRegRepr entry) r of
    PRe.RegIP -> case mblockStart of
      Just blockStart -> do
        ptrO <- PD.concreteToLLVM blockStart
        liftIO $ macawRegBinding sym entry (PSR.ptrToEntry ptrO)
      Nothing -> return $ mempty
    PRe.RegSP -> do
      stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
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
    PRe.RegDedicated dr -> do
      ctx <- CMR.asks envCtx
      let binRepr = W4.knownRepr :: PB.WhichBinaryRepr bin
      liftIO $ PA.dedicatedRegisterValidity hdr sym ctx binRepr entry dr
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
  let binmem = MBL.memoryImage $ PMC.binary binCtx
  stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
  readOps <- liftIO (MT.getReadOps sym (simOutMem stOut))
  mconcat <$> liftIO (mapM (readConcrete sym stackRegion binmem) (F.toList readOps))

 where
   readConcrete ::
     sym ->
     W4.SymNat sym ->
     MM.Memory (MM.ArchAddrWidth arch) ->
     MT.MemOp sym (MM.ArchAddrWidth arch) ->
     IO (AssumptionFrame sym)
   readConcrete sym stackRegion binmem (MT.MemOp (CLM.LLVMPointer reg off) dir _ sz (CLM.LLVMPointer _blkval bvval) end) = do
      isStack <- W4.natEq sym stackRegion reg
      case (W4.asConstantPred isStack, W4.asBV off, dir) of
        (Just False, Just off', MT.Read) -> do
          let mw :: MM.MemWord (MM.ArchAddrWidth arch)
              mw = MM.memWord (fromIntegral (BVS.asUnsigned off'))
          W4.LeqProof <- return $ W4.leqMulPos (W4.knownNat @8) sz
          let bits = W4.natMultiply (W4.knownNat @8) sz
          case doStaticRead @arch binmem mw bits end of
            Just bv -> liftIO $ do
              lit_val <- W4.bvLit sym bits bv
              -- FIXME: update when memory model has regions
              -- unclear what to assert about the region
              return $ exprBinding bvval lit_val
            Nothing -> return $ mempty
        _ -> return $ mempty


doStaticRead ::
  forall arch w .
  PA.ValidArch arch =>
  MM.Memory (MM.ArchAddrWidth arch) ->
  MM.MemWord (MM.ArchAddrWidth arch) ->
  W4.NatRepr w ->
  MM.Endianness ->
  Maybe (BVS.BV w)
doStaticRead mem mw w end = case PM.resolveAbsoluteAddress mem mw of
  Just segoff | MMP.isReadonly $ MM.segmentFlags $ MM.segoffSegment segoff ->
    let addr = MM.segoffAddr segoff in
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
