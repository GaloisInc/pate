{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Arch (
  SomeValidArch(..),
  ValidRepr(..),
  ArchLoader(..),
  ValidArchData(..),
  ValidArch(..),
  DedicatedRegister,
  HasDedicatedRegister(..),
  RegisterDisplay(..),
  fromRegisterDisplay,
  StubOverride(..),
  StateTransformer(..),
  ArchStubOverrides(..),
  mkMallocOverride,
  mkClockOverride,
  mkWriteOverride,
  mkDefaultStubOverride,
  mkDefaultStubOverrideArg,
  mkNOPStub,
  mkObservableOverride,
  lookupStubOverride,
  defaultStubOverride,
  withStubOverride,
  mergeLoaders,
  idStubOverride,
  serializeRegister,
  mkReadOverride,
  noMemChunkModify,
  modifyConcreteChunk,
  MemChunkModify,
  mkEventOverride,
  mkMallocOverride',
  mkArgPassthroughOverride,
  MemLocation(..),
  freshAtLocation
  ) where

import           Control.Lens ( (&), (.~), (^.) )

import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Kind as DK
import qualified Data.Map as Map
import qualified Data.Text as T
import           Data.Typeable ( Typeable )
import           GHC.TypeLits ( type (<=) )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Data.ElfEdit as E
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFGSlice as MCS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Types as LCT
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.AssumptionSet as PAS
import qualified Pate.Address as PAd
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.Monad.Context as PMC
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.SimState as PS
import qualified Pate.Solver as PSo
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Concretize as PVC

import qualified What4.Interface as W4 hiding ( integerToNat )
import qualified What4.Concrete as W4
import qualified What4.ExprHelpers as W4 ( integerToNat )
import qualified What4.UninterpFns as W4U
import qualified What4.JSON as W4S

import Pate.Config (PatchData)
import Data.Macaw.AbsDomain.AbsState (AbsBlockState)
import Pate.Address (ConcreteAddress)
import qualified Data.ElfEdit as EEP
import qualified Data.Parameterized.List as P
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Aeson as JSON
import           Data.Aeson ( (.=) )
import Data.Parameterized.Classes (ShowF(..))
import qualified Pate.PatchPair as PPa
import Data.Parameterized.WithRepr (withRepr)
import Data.Parameterized.Classes
import qualified Control.Monad.IO.Class as IO
import qualified System.IO as IO
import Data.Functor.Const
import qualified What4.ExprHelpers as WEH
import Numeric.Natural
import qualified What4.Expr.ArrayUpdateMap as AUM
import qualified Data.Parameterized.TraversableF as TF
import Data.Maybe
import Pate.Memory
import qualified Pate.ExprMappable as PEM
import Control.Monad (forM)

-- | The type of architecture-specific dedicated registers
--
-- Dedicated registers are registers whose purpose is fixed by an ABI, and whose
-- value never changes between two variants (i.e., original and patched
-- binaries).
--
-- For example, the most common PowerPC 64 ABI stores the Table of Contents
-- (TOC) pointer in r2; while this can change when switching modules at
-- run-time, it never varies between two variants. This enables us to assert
-- that it should always be equal, while also tracking its known concrete values
-- (which simplifies other proof obligations).
--
-- Each architecture backend will provide its own type for this; if it is not
-- needed, it can be instantiated as 'Data.Void.Void'
type family DedicatedRegister arch :: LCT.CrucibleType -> DK.Type

-- | Functions for identifying and working with architecture-specific dedicated registers
--
-- Note that this is data instead of a class because it varies by ABI (and not just architecture)
data HasDedicatedRegister arch =
  HasDedicatedRegister { asDedicatedRegister :: forall tp . MC.ArchReg arch tp -> Maybe (DedicatedRegister arch (MS.ToCrucibleType tp))
                       -- ^ Determine whether or not a register is a 'DedicatedRegister'
                       , dedicatedRegisterValidity :: forall sym bin tp . (LCB.IsSymInterface sym) => sym -> PMC.EquivalenceContext sym arch -> PB.WhichBinaryRepr bin -> PSR.MacawRegEntry sym tp -> DedicatedRegister arch (MS.ToCrucibleType tp) -> IO (PAS.AssumptionSet sym)
                       -- ^ Compute an assumption frame for the given arch-specific 'DedicatedRegister'
                       }

-- | An indicator of how a register should be displayed
--
-- The ADT tag carries the semantics of the register (e.g., if it is a normal
-- register or a hidden register).  The payloads contain the proper rendering of
-- the register in a human-readable form (or whatever else the caller wants).
--
-- Note that the order of the constructors is intentional, as we want "normal"
-- registers to be sorted to the top of the pile
data RegisterDisplay a = Normal a
                       -- ^ A normal user-level register
                       | Architectural a
                       -- ^ A register that represents architectural-level state not visible to the user
                       | Hidden
                       -- ^ An implementation detail that should not be shown to the user
                       deriving (Eq, Ord, Show, Functor)

fromRegisterDisplay :: RegisterDisplay a -> Maybe a
fromRegisterDisplay rd =
  case rd of
    Normal a -> Just a
    Architectural a -> Just a
    Hidden -> Nothing



class
  ( Typeable arch
  , MBL.BinaryLoader arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
  , MS.SymArchConstraints arch
  , MS.GenArchInfo PMT.MemTraceK arch
  , MC.ArchConstraints arch
  , 16 <= MC.ArchAddrWidth arch
  , MCS.HasArchEndCase arch
  , Integral (EEP.ElfWordType (MC.ArchAddrWidth arch))
  , W4S.W4SerializableFC (MC.ArchReg arch)
  , PEM.ExprFoldableFC (MC.ArchReg arch)
  ) => ValidArch arch where
  
  type ArchConfigOpts arch
  -- | Registers which are used for "raw" bitvectors (i.e. they are not
  -- used for pointers). These are assumed to always have region 0.
  rawBVReg :: forall tp. MC.ArchReg arch tp -> Bool
  -- | Determine how a register should be displayed to a user in reports and an
  -- interactive context
  displayRegister :: forall tp . MC.ArchReg arch tp -> RegisterDisplay String
  -- | From a name of formal argument parameters, determine the name of the
  -- parameter in the given register (if any)
  --
  -- FIXME: To be correct, this really needs to account for the types of
  -- arguments (e.g., large arguments are on the stack, while floating point
  -- arguments are in FP registers). Longer term, this should use the abide
  -- library
  argumentNameFrom :: forall tp . [T.Text] -> MC.ArchReg arch tp -> Maybe T.Text

  binArchInfo :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch)) -> MI.ArchitectureInfo arch

  -- register should be propagated during discovery
  discoveryRegister :: forall tp. MC.ArchReg arch tp -> Bool

  -- parsing registers from user input
  readRegister :: String -> Maybe (Some (MC.ArchReg arch))

  uninterpretedArchStmt :: MC.ArchStmt arch (MC.Value arch ids) -> Bool

  archClassifierWrapper :: forall ids. MI.BlockClassifier arch ids -> MI.BlockClassifier arch ids
  archClassifierWrapper = id

  -- overrides the default block classifier for the architecture
  archClassifier :: MI.ArchitectureInfo arch -> (forall ids. MI.BlockClassifier arch ids)
  archClassifier = MI.archClassifier

  -- | Rewrite an architecture-dependent terminal statement into
  -- an architecture-independent terminal statement,
  -- which represents an over-approximation of the architecture
  -- terminator
  archExtractArchTerms ::
    forall ids.
    MC.ArchTermStmt arch (MC.Value arch ids) ->
    MC.RegState (MC.ArchReg arch) (MC.Value arch ids) ->
    Maybe (MC.ArchSegmentOff arch) ->
    Maybe (MD.ParsedTermStmt arch ids)
  archExtractArchTerms = \ _ _ _ -> Nothing

  archSymReturnAddress ::
    forall sym v bin. W4.IsSymExprBuilder sym => sym -> PS.SimState sym arch v bin -> IO (CLM.LLVMPtr sym (MD.ArchAddrWidth arch))

serializeRegister :: ValidArch arch => MC.ArchReg arch tp -> W4S.W4S sym JSON.Value
serializeRegister r = case displayRegister r of
  Normal r_n -> return $ JSON.object [ "reg" .= r_n ]
  Architectural r_a -> return $ JSON.object [ "arch_reg" .= r_a ]
  Hidden -> return $ JSON.object [ "hidden_reg" .= showF r ]


data ValidArchData arch =
  ValidArchData { validArchSyscallDomain :: PVE.ExternalDomain PVE.SystemCall arch
                , validArchFunctionDomain :: PVE.ExternalDomain PVE.ExternalCall arch
                , validArchDedicatedRegisters :: HasDedicatedRegister arch
                , validArchArgumentMapping :: PVO.ArgumentMapping arch
                , validArchOrigExtraSymbols :: Map.Map BS.ByteString (BVS.BV (MC.ArchAddrWidth arch))
                -- ^ Extra symbols obtained by unspecified means
                --
                -- For example, these could be PLT stub symbols for ELF binaries
                , validArchPatchedExtraSymbols :: Map.Map BS.ByteString (BVS.BV (MC.ArchAddrWidth arch))
                , validArchStubOverrides :: ArchStubOverrides arch
                , validArchInitAbs :: PB.MkInitialAbsState arch
                -- ^ variant of Macaw's mkInitialAbsState that's tuned to
                -- our override mechanisms
                , validArchExtractPrecond ::
                    AbsBlockState (MC.ArchReg arch) {- ^ initial state at function entry point -} ->
                    MC.ArchSegmentOff arch {- ^ address for this block -} ->
                    AbsBlockState (MC.ArchReg arch) {- ^ state for this block -} ->
                    Maybe (Either String (MC.ArchBlockPrecond arch))
                -- ^ variant of Data.Macaw.Architecture.Info.extractBlockPrecond that
                --   also takes the initial function state. If this returns a 'Just' result, it is used
                --   instead of the result of 'extractBlockPrecond'
                }

-- | A stub is allowed to make arbitrary modifications to the symbolic state
--   Currently this is used to define the semantics for PLT stubs, but in principle
--   could be used to represent any function that we want to manually define semantics
--   for rather than include in the analysis.
data StubOverride arch =
  StubOverride
    (forall sym.
      LCB.IsSymInterface sym =>
      sym ->
      MI.ArchitectureInfo arch ->
      PVC.WrappedSolver sym IO ->
      IO (StateTransformer sym arch))

-- | In general the stub override may use both the original and patched states as its input, producing a pair
--   of post-states representing the stub semantics. However the 'StateTransformer' pattern captures the
--   typical case where a stub operates on each state independently.
data StateTransformer sym arch =
    StateTransformer2 (forall v. PPa.PatchPair (PS.SimState sym arch v) -> IO (PPa.PatchPair (PS.SimState sym arch v)))
  | StateTransformer (forall bin v. PB.KnownBinary bin => PS.SimState sym arch v bin -> IO (PS.SimState sym arch v bin))

mkStubOverride :: forall arch.
  (forall sym bin v. LCB.IsSymInterface sym => PB.KnownBinary bin => sym -> PS.SimState sym arch v bin -> IO (PS.SimState sym arch v bin)) ->
  StubOverride arch
mkStubOverride f = StubOverride $ \sym _ _ -> return $ StateTransformer $ \st -> f sym st

idStubOverride :: StubOverride arch
idStubOverride = mkStubOverride $ \_ -> return

withStubOverride ::
  LCB.IsSymInterface sym =>
  sym ->
  MI.ArchitectureInfo arch ->
  PVC.WrappedSolver sym IO ->
  StubOverride arch ->
  ((PPa.PatchPair (PS.SimState sym arch v) -> IO (PPa.PatchPair (PS.SimState sym arch v))) -> IO a) ->
  IO a
withStubOverride sym archInfo wsolver (StubOverride ov) f = do
  ov sym archInfo wsolver >>= \case
    StateTransformer2 ov' -> f ov'
    StateTransformer ov' -> 
      let ov'' stPair = case stPair of
            PPa.PatchPair stO stP -> PPa.PatchPair <$> ov' stO <*> ov' stP
            PPa.PatchPairSingle bin st  -> withRepr bin $ PPa.PatchPairSingle bin <$> ov' st 
      in f ov''

data ArchStubOverrides arch =
  ArchStubOverrides (StubOverride arch) (PB.FunctionSymbol -> Maybe (StubOverride arch))

lookupStubOverride ::
  ValidArchData arch -> PB.FunctionSymbol -> Maybe (StubOverride arch)
lookupStubOverride va nm = let ArchStubOverrides _ ov = validArchStubOverrides va in
  ov nm

defaultStubOverride ::
  ValidArchData arch -> StubOverride arch
defaultStubOverride va = let ArchStubOverrides _default _ = validArchStubOverrides va in _default

-- | Defines an override for @malloc@ that returns a 0-offset pointer in the
--   region defined by 'PS.simMaxRegion', and then increments that region.
--   Each @malloc@ call therefore returns a pointer in a region that is globally
--   unique.
--   For simplicity we can simply return a pointer with a concrete offset of 0, as
--   this can be easily propagated in the value domain but cannot be introspected.
--   The override takes two registers: the register used to pass in the length of the
--   allocated region, and the register used to store the resulting pointer.
--   NOTE: Currently the region length is unused, as the memory model as no way to represent
--   restrictions on the size of regions.
mkMallocOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ length argument (unused currently ) -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ register for fresh pointer -} ->
  StubOverride arch
mkMallocOverride _rLen rOut = mkStubOverride $ \sym st -> do
  (fresh_ptr, st') <- freshAlloc sym Nothing st
  return (st' { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ fresh_ptr) })

mkMallocOverride' ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  Typeable arch =>
  Maybe (MemLocation (MC.ArchAddrWidth arch)) ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ write fresh pointer here -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ register for fresh pointer -} ->
  StubOverride arch
mkMallocOverride' bufOverride rPtrLoc rOut = StubOverride $ \sym archInfo _wsolver -> do
  alloc_success <- W4.freshConstant sym (W4.safeSymbol "alloc_success") W4.BaseBoolRepr
  return $ StateTransformer $ \(st :: PS.SimState sym arch v bin) -> do
    let w_mem = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
    let ptr = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue rPtrLoc

    (fresh_ptr, st') <- case bufOverride of
      Just ov -> do
        (fresh_ptr, st') <- freshAtLocation sym st (MI.archEndianness archInfo) (Just 4) ov
        return (PSR.ptrToEntry fresh_ptr, st' )
      Nothing -> freshAlloc sym Nothing st

    -- IO.liftIO $ IO.putStrLn (show $ (PS.simRegs st) ^. MC.boundValue rPtrLoc)
          --ptrOffset <- W4.bvLit sym w_mem (BVS.mkBV w_mem (toInteger bufferOv))
          --region <- W4.natLit sym 0
          --let ptr = (CLM.LLVMPointer region ptrOffset)
    --let memRepr = PMT.memWidthMemRepr (MI.archEndianness archInfo)  w_mem 
    --mem' <- PMT.writeMemState @_ @arch sym (W4.truePred sym) (PMT.memState $ PS.simMem st) ptr memRepr (PSR.macawRegValue fresh_ptr)
    --return (st' { PS.simMem = (PS.simMem st){PMT.memState = mem'}, PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ fresh_ptr) })
    
    nullPtr <- IO.liftIO $ CLM.mkNullPointer sym w_mem

    ptr' <- IO.liftIO $ PMT.muxPtr sym alloc_success (PSR.macawRegValue fresh_ptr) nullPtr
    return (st' { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ (PSR.ptrToEntry ptr')) })

  -- | Return a freshly-allocated pointer with an optional region override.
--   New max region is set to the given region + 1 if it is greater than the current max
--   region (i.e. the new max region is guaranted to not clash with the returned pointer)
freshAlloc ::
  forall sym arch v bin.
  LCB.IsSymInterface sym =>
  MS.SymArchConstraints arch =>
  sym ->
  Maybe Integer ->
  PS.SimState sym arch v bin ->
  IO (PSR.MacawRegEntry sym (MT.BVType (MC.ArchAddrWidth arch)), PS.SimState sym arch v bin)
freshAlloc sym mregion st = do
  let mr = PS.simMaxRegion st
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  this_region <- case mregion of
    Just region -> W4.intLit sym region
    Nothing -> return $ PS.unSE mr
  zero <- W4.bvLit sym w (BVS.mkBV w 0)
  next_region_nat <- W4.integerToNat sym this_region
  let fresh_ptr = PSR.ptrToEntry (CLM.LLVMPointer next_region_nat zero)
  next_region <- PS.forScopedExpr sym mr $ \sym' mr' -> do
    cur_max <- case mregion of
      Just region -> do
        region_sym <- W4.intLit sym' region
        W4.intMax sym' mr' region_sym
      Nothing -> return mr'
    one <- W4.intLit sym' 1
    W4.intAdd sym' cur_max one
  return (fresh_ptr, st { PS.simMaxRegion = next_region })


-- | Defines an override for @clock@ that returns a value representing the current time.
--   Takes a single register used to store the return value.
--- NOTE: Currently this just returns a concrete value of 0. Ideally we should take
--  the same approach as @malloc@ and increment some nonce to make @clock@ calls distinct
--  but provably equal between the programs provided they happen in the same order.
mkClockOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkClockOverride rOut = StubOverride $ \sym _ _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol "current_time") (W4.BaseBVRepr w)
  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })

applyConcreteOverride :: 
  LCB.IsSymInterface sym =>
  1 <= ptrW =>
  MC.MemWidth ptrW =>
  sym -> 
  PB.WhichBinaryRepr bin ->
  PPa.PatchPairC (Maybe (MC.MemWord ptrW)) ->
  PSR.MacawRegEntry sym (MT.BVType ptrW) ->
  IO (PSR.MacawRegEntry sym (MT.BVType ptrW))
applyConcreteOverride sym bin overridePair e = case PPa.getC bin overridePair of
  Just (Just override) -> do
    let ptrW = PSR.macawRegBVWidth e
    ptrOffset <- W4.bvLit sym ptrW (BVS.mkBV ptrW (toInteger override))
    region <- W4.natLit sym 0
    let ptr = (CLM.LLVMPointer region ptrOffset)
    return $ e { PSR.macawRegValue = ptr }
  _ -> return e


mkObservableOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  T.Text {- ^ name of call -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return -} ->
  [MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch))] {- ^ args -} ->
  StubOverride arch
mkObservableOverride nm return_reg arg_regs = StubOverride $ \sym _archInfo _wsolver -> do
  let w_mem = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  -- FIXME: this is wrong, since this value needs to read from memory
  
  return $ StateTransformer $ \st -> do
    args <- forM arg_regs $ \r -> do
      let (CLM.LLVMPointer _reg r_val) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue r
      return $ r_val

    Some argsCtx <- return $ Ctx.fromList (map Some args)
    let reprsCtx = TFC.fmapFC W4.exprType argsCtx
    bv_fn <- W4U.mkUninterpretedSymFn sym ("written_" ++ show nm) reprsCtx (W4.BaseBVRepr w_mem)

    let mem = PS.simMem st
    mem' <- PMT.addExternalCallEvent sym nm argsCtx True mem 
    let st' = st { PS.simMem = mem' }
    zero_nat <- W4.natLit sym 0
    fresh_bv <- W4.applySymFn sym bv_fn argsCtx
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st' { PS.simRegs = ((PS.simRegs st') & (MC.boundValue return_reg) .~ ptr ) })

mkEventOverride ::
  forall arch ptrW.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  ptrW ~ (MC.ArchAddrWidth arch) =>
  T.Text {- ^ name of call -} ->
  (forall sym. LCB.IsSymInterface sym => sym -> PMT.MemChunk sym ptrW -> IO (W4.SymBV sym ptrW)) {- ^ compute return value for read chunk -} ->
  (MC.MemWord (MC.ArchAddrWidth arch)) {- ^ concrete length to read -} ->
  MC.ArchReg arch (MT.BVType ptrW) {- ^ buf -} ->
  MC.ArchReg arch (MT.BVType ptrW) {- ^ return register -} ->
  StubOverride arch
mkEventOverride nm readChunk len buf_reg rOut = StubOverride $ \(sym :: sym) _archInfo _wsolver -> return $ StateTransformer $ \(st :: PS.SimState sym arch v bin) -> do
  -- let (bin :: PB.WhichBinaryRepr bin) = knownRepr
  let ptrW = MC.memWidthNatRepr @ptrW
  --(CLM.LLVMPointer _ len_bv) <- PSR.macawRegValue <$> (applyConcreteOverride sym bin lenOverridePair $ (PS.simRegs st) ^. MC.boundValue len_reg)
  
  --(fresh_buf, st') <- IO.liftIO $ freshAlloc sym (Just 4) st
  let fresh_buf = (PS.simRegs st) ^. MC.boundValue buf_reg
  let st' = st

  let buf_ptr = PSR.macawRegValue fresh_buf
  let mem = PS.simMem st
  len_sym <- W4.bvLit sym ptrW (BVS.mkBV ptrW (fromIntegral len))
  bytes_chunk <- PMT.readChunk sym (PMT.memState mem) buf_ptr len_sym
  written <- readChunk sym bytes_chunk
  mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> written) True mem
  result <- PSR.bvToEntry sym written 
  return (st' { PS.simMem = mem', PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ result ) })


newtype MemChunkModify ptrW =
  MemChunkModify { mkMemChunk :: (forall sym. LCB.IsSymInterface sym => sym -> PMT.MemChunk sym ptrW -> IO (PMT.MemChunk sym ptrW)) }

noMemChunkModify :: MemChunkModify ptrW
noMemChunkModify = MemChunkModify $ \_ chunk -> return chunk

modifyConcreteChunk ::
  1 <= ptrW =>
  Integral x =>
  MC.Endianness ->
  W4.NatRepr ptrW ->
  x {- ^ concrete contents (clamped to number of bytes ) -} ->
  Natural {- ^ number of bytes  -} ->
  Natural {- ^ offset into base chunk  -} ->
  MemChunkModify ptrW
modifyConcreteChunk endianness ptrW x bytes offset = MemChunkModify $ \sym chunk -> do
  offsetBV <- W4.bvLit sym ptrW (BVS.mkBV ptrW (fromIntegral offset))
  chunk' <- PMT.concreteMemChunk sym endianness ptrW x bytes
  PMT.copyMemChunkInto sym chunk offsetBV chunk' 

-- Indirect pointers with a concrete base
data MemLocation ptrW =
    MemPointer (MC.MemWord ptrW)
  | MemIndPointer (MemLocation ptrW)  (MC.MemWord ptrW)

-- Create an indirect pointer by creating a fresh allocation for each level of indirection 
freshAtLocation ::
  forall sym arch ptrW v bin.
  LCB.IsSymInterface sym =>
  MS.SymArchConstraints arch =>
  Typeable arch =>
  ptrW ~ MD.ArchAddrWidth arch =>
  sym ->
  PS.SimState sym arch v bin ->
  MC.Endianness ->
  Maybe Integer {- ^ override for starting region -} ->
  MemLocation ptrW ->
  IO ( CLM.LLVMPtr sym ptrW, PS.SimState sym arch v bin)
freshAtLocation sym st endianness mregion loc = do
  (base, st') <- freshAlloc sym mregion st
  st'' <- go (fmap (+1) mregion) loc (PSR.macawRegValue base) st'
  return (PSR.macawRegValue base, st'')
  where
    go :: 
      Maybe Integer ->
      MemLocation ptrW ->
      CLM.LLVMPtr sym ptrW ->
      PS.SimState sym arch v bin ->
      IO (PS.SimState sym arch v bin)
    go mregion' loc' val st' = case loc' of
      MemPointer mw -> do
        let w_mem = MC.memWidthNatRepr @ptrW
        ptrOffset <- W4.bvLit sym w_mem (BVS.mkBV w_mem (fromIntegral mw))
        region <- W4.natLit sym 0
        let ptr = CLM.LLVMPointer region ptrOffset
        let memRepr = PMT.memWidthMemRepr endianness w_mem 
        mem' <- PMT.writeMem sym ptr val memRepr (PS.simMem st')
        --mem' <- PMT.writeMemState @_ @arch sym (W4.truePred sym) (PMT.memState $ PS.simMem st) ptr memRepr val
        return $ (st' { PS.simMem = mem' })
      MemIndPointer loc'' locOffset -> do
        let w_mem = MC.memWidthNatRepr @ptrW
        (fresh_loc_ptr, st'') <- freshAlloc sym mregion' st'
        st''' <- go (fmap (+1) mregion') loc'' (PSR.macawRegValue fresh_loc_ptr) st''
        let (CLM.LLVMPointer region ptrOffset) = (PSR.macawRegValue fresh_loc_ptr)
        offset_bv <- W4.bvLit sym w_mem (BVS.mkBV w_mem (fromIntegral locOffset))
        ptrOffset' <- W4.bvAdd sym ptrOffset offset_bv
        let ptr = (CLM.LLVMPointer region ptrOffset')
        let memRepr = PMT.memWidthMemRepr endianness w_mem 
        mem' <- PMT.writeMem sym ptr val memRepr (PS.simMem st''')
        --mem' <- PMT.writeMemState @_ @arch sym (W4.truePred sym) (PMT.memState $ PS.simMem st''') ptr memRepr val
        return $ st''' { PS.simMem = mem' }

resolveMemLocation ::
  forall sym ptrW.
  W4.IsSymExprBuilder sym =>
  MC.MemWidth ptrW =>
  sym ->
  PMT.MemTraceImpl sym ptrW ->
  MC.Endianness ->
  MemLocation ptrW ->
  IO (CLM.LLVMPtr sym ptrW)
resolveMemLocation sym mem endianness loc  = case loc of
  MemPointer mw -> do
    let w_mem = MC.memWidthNatRepr @ptrW
    ptrOffset <- W4.bvLit sym w_mem (BVS.mkBV w_mem (fromIntegral mw))
    region <- W4.natLit sym 0
    let ptr = (CLM.LLVMPointer region ptrOffset)
    let memRepr = PMT.memWidthMemRepr endianness w_mem 
    PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) ptr memRepr
  MemIndPointer loc' locOffset -> do
    let w_mem = MC.memWidthNatRepr @ptrW
    (CLM.LLVMPointer region ptrOffset) <- resolveMemLocation sym mem endianness loc'
    offset_bv <- W4.bvLit sym w_mem (BVS.mkBV w_mem (fromIntegral locOffset))
    ptrOffset' <- W4.bvAdd sym ptrOffset offset_bv
    let ptr = (CLM.LLVMPointer region ptrOffset')
    let memRepr = PMT.memWidthMemRepr endianness w_mem 
    PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) ptr memRepr

-- | Stub that reads the same uninterpreted chunk into both
--   original and patched programs, modulo optionally overwriting the uninterpreted
--   bytes with contents. Does nothing if the number of available bytes is zero or less.
mkReadOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  Typeable arch =>
  T.Text {- ^ name of call -} ->
  PPa.PatchPairC (MemChunkModify (MC.ArchAddrWidth arch)) {- ^ mutator for incoming symbolic data -} ->
  PPa.PatchPairC (Maybe (MemLocation (MC.ArchAddrWidth arch))) {- ^ concrete override for buffer address (pointer to buffer pointer) -} ->
    PPa.PatchPairC (Maybe (MC.MemWord (MC.ArchAddrWidth arch))) {- ^ concrete override for length -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ source (i.e. file descriptor, socket, etc) -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ buf -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ len -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkReadOverride nm chunkOverrides bufferOverrides lenOverrides src_reg buf_reg len_reg rOut = StubOverride $ \(sym :: sym) archInfo wsolver -> return $ StateTransformer2 $ \ stPair -> do
  let w_mem = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  let bv_repr = W4.BaseBVRepr w_mem
  let byte_repr = W4.BaseBVRepr (W4.knownNat @8)
  -- undefined number of actual available bytes from the read "source"
  -- FIXME: formally this should be an interpreted function on the source register, not just an arbitrary shared value
  -- FIXME: this does not capture the fact that usually the return value is signed, where negative values represent
  -- various error conditions (aside from simply having no more content available).

  -- FIXME: this makes "bytes_available" globally unique, which is not quite right. We need a model of
  -- the input stream and have this be a function of reading a particular part of that stream.

  bytes_available_fn <- W4U.mkUninterpretedSymFn sym (show nm ++ "_bytes_available") Ctx.empty W4.BaseBoolRepr
  bytes_available <- W4.applySymFn sym bytes_available_fn Ctx.empty 
  -- W4.freshConstant sym (W4.safeSymbol "bytes_available") W4.BaseBoolRepr
  zero <- IO.liftIO $ W4.bvLit sym w_mem (BVS.zero w_mem)
  -- for simplicity we assume that the symbolic chunk is exactly as large as the requested length (the max
  -- length of both sides)
  -- we then make the entire write into memory conditional on the symbolic predicate 'bytes_available'
  -- FIXME: this is an over-simplification to reduce the state explosion into exactly two cases: either
  -- we get all of the requested bytes or we don't get any
  -- One idea for representing the case where we have fewer than expected but nonzero bytes would be to
  -- have each of the individual bytes written to memory conditionally either from the chunk or simply read
  -- back from memory. This allows us to still represent this as a single large write.
  available_bytes_ <- PPa.runPatchPairT $ PPa.joinPatchPred (\x y -> IO.liftIO $ WEH.bvUMax sym x y) $ \bin -> do
      st <- PPa.get bin stPair
      (CLM.LLVMPointer _ len_bv) <- IO.liftIO $ (PSR.macawRegValue <$> (applyConcreteOverride sym bin lenOverrides $ (PS.simRegs st) ^. MC.boundValue len_reg))
      return len_bv
  available_bytes <- IO.liftIO $ PVC.resolveSingletonSymbolicAsDefault wsolver available_bytes_
    
  let arr_repr = W4.BaseArrayRepr (Ctx.singleton bv_repr) byte_repr

  -- FIXME: as with "bytes_available" this should not be globally unique, but rather a function
  -- of where in the stream we're reading from
  chunk_arr_fn <- W4U.mkUninterpretedSymFn sym (show nm ++ "_undefined_read") Ctx.empty arr_repr
  chunk_arr <- IO.liftIO $ W4.applySymFn sym chunk_arr_fn Ctx.empty
  --chunk_arr <- IO.liftIO $ W4.freshConstant sym (W4.safeSymbol "undefined_read")  arr_repr
  let chunk = PMT.MemChunk chunk_arr zero available_bytes
  PPa.runPatchPairT $ PPa.forBins $ \bin -> do
    --chunk_arr <- IO.liftIO $ W4.freshConstant sym W4.emptySymbol arr_repr
    --let chunk = PMT.MemChunk chunk_arr zero available_bytes
    st <- PPa.get bin stPair
    chunk' <- case PPa.getC bin chunkOverrides of
      Just ov -> IO.liftIO $ mkMemChunk ov sym chunk
      Nothing -> return chunk
    let src = (PS.simRegs st) ^. MC.boundValue src_reg

    -- FIXME: this region is picked arbitrarily and concretely so that we
    -- can find this buffer again when we call the corresponding override


    -- FIXME: we should be able to deduce the address by examining
    -- the buffer expression itself
    -- here we invent a fresh buffer pointer (instead of using the
    -- given one) so we know that it's necessarily disjoint from anything else

    -- fresh_buf, st') <- IO.liftIO $ freshAlloc sym (Just 4) st
    (buf, st'') <- case PPa.getC bin bufferOverrides of
      Just (Just bufferOv) -> IO.liftIO $ do
        (fresh_buf, st') <- freshAtLocation sym st (MI.archEndianness archInfo) (Just 4) bufferOv
        return $ (PSR.ptrToEntry fresh_buf, st')
      _ -> do
        return ((PS.simRegs st) ^. MC.boundValue buf_reg, st)

    IO.liftIO $ readTransformer sym archInfo src buf rOut bytes_available chunk' st''


{-
  return $ readTransformer sym wsolver src_reg buf_reg len_reg rOut $ \bin _ -> case PPa.getC bin chunkOverrides of
    Just mkr -> do
      -- only apply the override if some content was returned 
      -- NB: otherwise this override will force there to always be content available to
      -- read, which incorrectly will cause this stub to avoid legitimate program paths
      -- which handle reaching the end-of-input
      return chunk
      -- nonzero_contents <- W4.bvUlt sym zero available_bytes
      -- chunk' <- mkMemChunk mkr sym chunk
      -- PMT.muxMemChunk sym nonzero_contents chunk' chunk
    Nothing -> return chunk
-}

readTransformer ::
  forall sym arch bin v.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  LCB.IsSymInterface sym =>
  sym ->
  MI.ArchitectureInfo arch ->
  PSR.MacawRegEntry sym (MT.BVType (MC.ArchAddrWidth arch)) {- ^ source (i.e. file descriptor, socket, etc) -} ->
  PSR.MacawRegEntry sym (MT.BVType (MC.ArchAddrWidth arch)) {- ^ buf -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  W4.Pred sym {- ^ condition for read -} ->
  PMT.MemChunk sym (MC.ArchAddrWidth arch) ->
  PS.SimState sym arch v bin ->
  IO (PS.SimState sym arch v bin)
readTransformer sym archInfo _src_val buf rOut cond chunk st = do
  let ptrW = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  -- let (bin :: PB.WhichBinaryRepr bin) = knownRepr
  -- let src_val = (PS.simRegs st) ^. MC.boundValue src_reg
  -- chunk <- mkChunk bin src_val
  -- let (CLM.LLVMPointer _ len_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue len_reg
  --len_bv' <- PVC.resolveSingletonSymbolicAsDefault wsolver len_bv
  let buf_ptr = PSR.macawRegValue buf
  -- let buf_ptr = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue buf_reg
  let mem = PS.simMem st
  mem' <- IO.liftIO $ PMT.writeChunk sym (MI.archEndianness archInfo) chunk buf_ptr cond mem
  zero <- IO.liftIO $ W4.bvLit sym ptrW (BVS.zero ptrW)
  -- either the chunk is written or it's not and we return zero bytes written
  written <- IO.liftIO $ W4.baseTypeIte sym cond (PMT.memChunkLen chunk) zero
  zero_nat <- IO.liftIO $ W4.natLit sym 0
  let written_result = PSR.ptrToEntry (CLM.LLVMPointer zero_nat written)
  -- FIXME: currently these are all unsigned values, but likely this return value will be treated as signed
  -- where negative values represent different error conditions
  return (st { PS.simMem = mem', PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ written_result ) })

--  SymExpr sym (BaseArrayType (Ctx.EmptyCtx Ctx.::> BaseBVType ptrW) (BaseBVType 8))
mkWriteOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  T.Text {- ^ name of call -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ fd -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ buf -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ len -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkWriteOverride nm fd_reg buf_reg flen rOut = StubOverride $ \sym archInfo wsolver -> do
  let w_mem = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  return $ StateTransformer $ \st -> do
    let buf_ptr = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue buf_reg

    let (CLM.LLVMPointer _ len_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue flen
    let (CLM.LLVMPointer _ fd_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue fd_reg
    let (CLM.LLVMPointer _ buf_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue buf_reg
    len_bv' <- PVC.resolveSingletonSymbolicAsDefault wsolver len_bv
    (st',sz) <- case W4.asConcrete len_bv' of
      Just (W4.ConcreteBV _ lenC)
        | Just (Some w) <- W4.someNat (BVS.asUnsigned lenC)
        , Just W4.LeqProof <- W4.isPosNat w -> do
        let mem = PS.simMem st
        -- endianness doesn't really matter, as long as we're consistent
        let memrepr = MC.BVMemRepr w (MI.archEndianness archInfo)
        (CLM.LLVMPointer region val_bv) <- PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) buf_ptr memrepr
        mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> fd_bv Ctx.:> val_bv Ctx.:> W4.natToIntegerPure region) True mem
        -- globally-unique
        bv_fn <- W4U.mkUninterpretedSymFn sym (show nm ++ "sz") (Ctx.empty Ctx.:> (W4.exprType val_bv)) (W4.BaseBVRepr w_mem)
        sz <- W4.applySymFn sym bv_fn (Ctx.empty Ctx.:> val_bv)
        return $ (st { PS.simMem = mem' },sz)
      _ -> do
        let mem = PS.simMem st
        bytes_chunk <- PMT.readChunk sym (PMT.memState mem) buf_ptr len_bv
        let memrepr = MC.BVMemRepr (W4.knownNat @8) (MI.archEndianness archInfo)
        (CLM.LLVMPointer _region first_byte) <- PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) buf_ptr memrepr
        one <- W4.bvLit sym w_mem (BVS.mkBV w_mem 1)
        len_minus_one <- W4.bvSub sym len_bv one
        last_idx <- W4.bvAdd sym buf_bv len_minus_one
        last_byte <- W4.arrayLookup sym (PMT.memChunkArr bytes_chunk) (Ctx.empty Ctx.:> last_idx)
        mem' <- PMT.addExternalCallWrite sym nm bytes_chunk (Ctx.empty Ctx.:> fd_bv ) mem
        -- this is used in the case where there is a symbolic length, in lieu of
        -- making the symbolic length depends on the entire contents of the read value,
        -- we only make it depend on the first byte and last byte
        bv_fn <- W4U.mkUninterpretedSymFn sym (show nm ++ "sz_chunk")
          (Ctx.empty Ctx.:> W4.BaseBVRepr w_mem Ctx.:> (W4.exprType first_byte) Ctx.:> (W4.exprType last_byte) ) (W4.BaseBVRepr w_mem)
        sz <- W4.applySymFn sym bv_fn (Ctx.empty Ctx.:> len_bv Ctx.:> first_byte Ctx.:> last_byte)
        return $ (st { PS.simMem = mem' },sz)

    zero_nat <- W4.natLit sym 0
    -- we're returning a symbolic result representing the number of bytes written, so
    -- we clamp this explicitly to the given write length
    zero_ptr <- W4.bvLit sym w_mem (BVS.mkBV w_mem 0)
    sz_is_bounded <- W4.bvUle sym len_bv' sz
    bounded_sz <- W4.baseTypeIte sym sz_is_bounded sz zero_ptr
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat bounded_sz)
    return (st' { PS.simRegs = ((PS.simRegs st') & (MC.boundValue rOut) .~ ptr ) })



-- | Default override returns the same arbitrary value for both binaries
mkDefaultStubOverride ::
  forall arch.
  MS.SymArchConstraints arch =>
  String -> 
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkDefaultStubOverride nm rOut = StubOverride $ \sym _ _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol nm) (W4.BaseBVRepr w)
  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })

-- | Default override returns the same arbitrary value for both binaries
mkArgPassthroughOverride ::
  forall arch.
  MS.SymArchConstraints arch =>
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ argument register -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkArgPassthroughOverride rArg rOut = StubOverride $ \_ _ _ -> return $ StateTransformer $ \st -> do
  let arg = (PS.simRegs st) ^. MC.boundValue rArg
  return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ arg) })

-- | Default override returns the same arbitrary value for both binaries, based on the input
--   registers
mkDefaultStubOverrideArg ::
  forall arch.
  MS.SymArchConstraints arch =>
  ValidArch arch =>
  String ->
  [Some (MC.ArchReg arch)] {- ^ argument registers -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkDefaultStubOverrideArg nm rArgs rOut = StubOverride $ \sym _ _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)

  return $ StateTransformer $ \st -> do
    vals <- mapM (\(Some r) -> getType sym (PS.simRegs st ^. MC.boundValue r)) rArgs
    Some vals_ctx <- return $ Ctx.fromList vals
    -- globally unique function
    result_fn <- W4U.mkUninterpretedSymFn sym nm (TFC.fmapFC W4.exprType vals_ctx) (W4.BaseBVRepr w)
    fresh_bv <- W4.applySymFn sym result_fn vals_ctx
    let mem0 = PS.simMem st
    -- add unobservable event, so this call appears in the trace
    mem1 <- case fromRegisterDisplay (displayRegister rOut) of
      Just rOutNm -> do
        -- TODO: this is a quick solution to indicate where the result of
        -- the call was saved. Ideally there would be a formal slot in the
        -- event to store this information.
        let nm' = rOutNm ++ " <- " ++ nm
        IO.liftIO $ PMT.addExternalCallEvent sym (T.pack nm') vals_ctx False mem0
      Nothing -> IO.liftIO $ PMT.addExternalCallEvent sym (T.pack nm) vals_ctx False mem0
    ptr <- IO.liftIO $ PSR.bvToEntry sym fresh_bv
    -- add a register event to mark the register update
    mem2 <- IO.liftIO $ PMT.addRegEvent sym (PMT.RegOp $ MapF.singleton rOut ptr) mem1
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr), PS.simMem = mem2 })
  where
    getType :: 
      W4.IsExprBuilder sym => 
      sym -> 
      PSR.MacawRegEntry sym tp -> 
      IO (Some (W4.SymExpr sym))
    getType sym r = case PSR.macawRegRepr r of
      CLM.LLVMPointerRepr{} -> do
        let CLM.LLVMPointer reg off = PSR.macawRegValue r
        let iRegion = W4.natToIntegerPure reg
        Some <$> W4.mkStruct sym (Ctx.empty Ctx.:> iRegion Ctx.:> off)
      LCT.BoolRepr -> return $ Some $ PSR.macawRegValue r
      LCT.StructRepr Ctx.Empty -> Some <$> W4.mkStruct sym Ctx.empty
      x -> error $ "mkDefaultStubOverrideArg: unsupported type" ++ show x

-- | No-op stub
mkNOPStub ::
  forall arch.
  MS.SymArchConstraints arch =>
  String ->
  StubOverride arch
mkNOPStub _nm = StubOverride $ \_sym _ _ -> return $ StateTransformer $ \st -> return st

-- | A witness to the validity of an architecture, along with any
-- architecture-specific data required for the verifier
--
-- The first external domain handles domains for system calls, while the second
-- handles domains for external library calls
data SomeValidArch arch where
  SomeValidArch :: (ValidArch arch) => ValidArchData arch -> SomeValidArch arch

-- | Needed to produce evidence for 'Pate.TraceTree' that both type parameters are valid
data ValidRepr (k :: (DK.Type, DK.Type)) where
  ValidRepr :: forall sym arch. (PSo.ValidSym sym, ValidArch arch) => sym -> SomeValidArch arch -> ValidRepr '(sym, arch)

-- | Create a 'PA.SomeValidArch' from parsed ELF files
data ArchLoader err =
  ArchLoader (forall w.
              PatchData ->
              E.ElfMachine ->
              E.ElfHeaderInfo w ->
              E.ElfHeaderInfo w ->
              Either err (Some SomeValidArch)
             )

instance (ValidArch arch, PSo.ValidSym sym, rv ~ MC.ArchReg arch) => MC.PrettyRegValue rv (PSR.MacawRegEntry sym) where
  ppValueEq r tp = case fromRegisterDisplay (displayRegister r) of
    Just r_str -> Just (PP.pretty r_str <> ":" <+> PP.pretty (show tp))
    Nothing -> Nothing

-- | Merge loaders by taking the first successful result (if it exists)
mergeLoaders ::
  ArchLoader err -> ArchLoader err -> ArchLoader err
mergeLoaders (ArchLoader l1) (ArchLoader l2) = ArchLoader $ \pd m i1 i2 ->
  case l1 pd m i1 i2 of
    Left _ -> l2 pd m i1 i2
    Right a -> Right a



