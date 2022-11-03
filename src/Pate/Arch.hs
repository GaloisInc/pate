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
  mkObservableOverride,
  lookupStubOverride,
  defaultStubOverride,
  withStubOverride,
  mergeLoaders,
  idStubOverride
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
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFGSlice as MCS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Types as LCT
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.AssumptionSet as PAS
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
  ) => ValidArch arch where
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
  ArchStubOverrides (StubOverride arch) (Map.Map BS.ByteString (StubOverride arch))

lookupStubOverride ::
  ValidArchData arch -> BS.ByteString -> Maybe (StubOverride arch)
lookupStubOverride va nm = let ArchStubOverrides _ ov = validArchStubOverrides va in
  Map.lookup nm ov

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
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol "written") (W4.BaseBVRepr w_mem)
  return $ StateTransformer $ \st -> do
    let (CLM.LLVMPointer _ r1_val) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue r1_reg
    let mem = PS.simMem st
    mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> PMT.SymBV' r1_val) mem
    let st' = st { PS.simMem = mem' }
    zero_nat <- W4.natLit sym 0
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
  -- TODO: must be less than len
  fresh_bv <- W4.freshConstant sym (W4.safeSymbol "written") (W4.BaseBVRepr w_mem)
  return $ StateTransformer $ \st -> do
    let buf_ptr = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue buf_reg

    let (CLM.LLVMPointer _ len_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue flen
    let (CLM.LLVMPointer _ fd_bv) = PSR.macawRegValue $ (PS.simRegs st) ^. MC.boundValue fd_reg
    len_bv' <- PVC.resolveSingletonSymbolicAsDefault wsolver len_bv
    st' <- case W4.asConcrete len_bv' of
      Just (W4.ConcreteBV _ lenC)
        | Just (Some w) <- W4.someNat (BVS.asUnsigned lenC)
        , Just W4.LeqProof <- W4.isPosNat w -> do
        let mem = PS.simMem st
        -- endianness doesn't really matter, as long as we're consistent
        let memrepr = MC.BVMemRepr w MC.LittleEndian
        (CLM.LLVMPointer _ val_bv) <- PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) buf_ptr memrepr
        --FIXME: ignores regions
        mem' <- PMT.addExternalCallEvent sym nm (Ctx.empty Ctx.:> PMT.SymBV' fd_bv Ctx.:> PMT.SymBV' val_bv) mem
        return $ st { PS.simMem = mem' }
      _ ->
        -- FIXME: what to do for non-concrete write lengths?
        return st
    zero_nat <- W4.natLit sym 0
    let ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat fresh_bv)
    
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
              E.ElfMachine ->
              E.ElfHeaderInfo w ->
              E.ElfHeaderInfo w ->
              Either err (Some SomeValidArch)
             )

instance (ValidArch arch, PSo.ValidSym sym, rv ~ MC.ArchReg arch) => MC.PrettyRegValue rv (PSR.MacawRegEntry sym) where
  ppValueEq r tp = case fromRegisterDisplay (displayRegister r) of
    Just r_str -> Just (PP.pretty r_str <> PP.pretty ":" <+> PP.pretty (show tp))
    Nothing -> Nothing

-- | Merge loaders by taking the first successful result (if it exists)
mergeLoaders ::
  ArchLoader err -> ArchLoader err -> ArchLoader err
mergeLoaders (ArchLoader l1) (ArchLoader l2) = ArchLoader $ \m i1 i2 ->
  case l1 m i1 i2 of
    Left _ -> l2 m i1 i2
    Right a -> Right a



