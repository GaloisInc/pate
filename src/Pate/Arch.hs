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

{-# OPTIONS_GHC -fno-warn-orphans #-}

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
  mkDefaultStubOverride',
  mkDefaultStubOverrideArg,
  mkNOPStub,
  mkObservableOverride,
  lookupStubOverride,
  defaultStubOverride,
  withStubOverride,
  mergeLoaders,
  idStubOverride,
  serializeRegister
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
      PVC.WrappedSolver sym IO ->
      IO (StateTransformer sym arch))

data StateTransformer sym arch =
  StateTransformer (forall v bin. PB.KnownBinary bin => PS.SimState sym arch v bin -> IO (PS.SimState sym arch v bin))

mkStubOverride :: forall arch.
  (forall sym bin v.W4.IsSymExprBuilder sym => PB.KnownBinary bin => sym -> PS.SimState sym arch v bin -> IO (PS.SimState sym arch v bin)) ->
  StubOverride arch
mkStubOverride f = StubOverride $ \sym _ -> return $ StateTransformer (\st -> f sym st)

idStubOverride :: StubOverride arch
idStubOverride = mkStubOverride $ \_ -> return

withStubOverride ::
  LCB.IsSymInterface sym =>
  sym ->
  PVC.WrappedSolver sym IO ->
  StubOverride arch ->
  ((forall bin. PB.KnownBinary bin => PS.SimState sym arch v bin -> IO (PS.SimState sym arch v bin)) -> IO a) ->
  IO a
withStubOverride sym wsolver (StubOverride ov) f = do
  StateTransformer ov' <- ov sym wsolver
  f ov'


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
  let mr = PS.simMaxRegion st
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  mr_nat <- W4.integerToNat sym (PS.unSE mr)
  zero <- W4.bvLit sym w (BVS.mkBV w 0)
  let fresh_ptr = PSR.ptrToEntry (CLM.LLVMPointer mr_nat zero)
  mr_inc <- PS.forScopedExpr sym mr $ \sym' mr' -> do
    one <- W4.intLit sym' 1
    W4.intAdd sym' mr' one
  return (st { PS.simMaxRegion = mr_inc, PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ fresh_ptr) })

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
mkClockOverride rOut = StubOverride $ \sym _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol "current_time") (W4.BaseBVRepr w)
  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })

mkObservableOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  T.Text {- ^ name of call -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ r0 -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ r1 -} ->
  StubOverride arch
mkObservableOverride nm r0_reg r1_reg = StubOverride $ \sym _wsolver -> do
  let w_mem = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  let bv_repr = W4.BaseBVRepr w_mem

  -- FIXME: this is wrong, since this value needs to read from memory
  bv_fn <- W4U.mkUninterpretedSymFn sym ("written_" ++ show nm) (Ctx.empty Ctx.:> bv_repr) (W4.BaseBVRepr w_mem)
  return $ StateTransformer $ \st -> do
    let (CLM.LLVMPointer _ r1_val) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue r1_reg
    let mem = PS.simMem st
    mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> r1_val) mem
    let st' = st { PS.simMem = mem' }
    zero_nat <- W4.natLit sym 0
    fresh_bv <- W4.applySymFn sym bv_fn (Ctx.empty Ctx.:> r1_val) 
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st' { PS.simRegs = ((PS.simRegs st') & (MC.boundValue r0_reg) .~ ptr ) })

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
mkWriteOverride nm fd_reg buf_reg flen rOut = StubOverride $ \sym wsolver -> do
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
        let memrepr = MC.BVMemRepr w MC.LittleEndian
        (CLM.LLVMPointer region val_bv) <- PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) buf_ptr memrepr
        mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> fd_bv Ctx.:> val_bv Ctx.:> W4.natToIntegerPure region) mem
        -- globally-unique
        bv_fn <- W4U.mkUninterpretedSymFn sym (show nm ++ "sz") (Ctx.empty Ctx.:> (W4.exprType val_bv)) (W4.BaseBVRepr w_mem)
        sz <- W4.applySymFn sym bv_fn (Ctx.empty Ctx.:> val_bv)
        return $ (st { PS.simMem = mem' },sz)
      _ -> do
        let mem = PS.simMem st
        bytes_chunk <- PMT.readChunk sym (PMT.memState mem) buf_ptr len_bv
        let memrepr = MC.BVMemRepr (W4.knownNat @8) MC.LittleEndian
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
mkDefaultStubOverride nm rOut = StubOverride $ \sym _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol nm) (W4.BaseBVRepr w)
  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })

-- | Default override always returns the same arbitrary value
mkDefaultStubOverride' ::
  forall arch.
  MS.SymArchConstraints arch =>
  String -> 
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkDefaultStubOverride' nm rOut = StubOverride $ \sym _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  -- globally unique function
  result_fn <- W4U.mkUninterpretedSymFn sym nm Ctx.empty (W4.BaseBVRepr w)
  fresh_bv <- W4.applySymFn sym result_fn Ctx.empty
  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })

-- | Default override returns the same arbitrary value for both binaries, based on the input
--   registers
mkDefaultStubOverrideArg ::
  forall arch.
  MS.SymArchConstraints arch =>
  String ->
  [Some (MC.ArchReg arch)] {- ^ argument registers -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkDefaultStubOverrideArg nm rArgs rOut = StubOverride $ \sym _ -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)

  return $ StateTransformer $ \st -> do
    zero_nat <- W4.natLit sym 0
    vals <- mapM (\(Some r) -> getType sym (PS.simRegs st ^. MC.boundValue r)) rArgs
    Some vals_ctx <- return $ Ctx.fromList vals
    -- globally unique function
    result_fn <- W4U.mkUninterpretedSymFn sym nm (TFC.fmapFC W4.exprType vals_ctx) (W4.BaseBVRepr w)
    fresh_bv <- W4.applySymFn sym result_fn vals_ctx
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ ptr) })
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
mkNOPStub _nm = StubOverride $ \_sym _ -> return $ StateTransformer $ \st -> return st

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



