{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Arch (
  SomeValidArch(..),
  ArchLoader(..),
  ValidArchData(..),
  ValidArch(..),
  DedicatedRegister,
  HasDedicatedRegister(..),
  RegisterDisplay(..),
  fromRegisterDisplay,
  StubOverride(..),
  ArchStubOverrides(..),
  mkMallocOverride,
  mkClockOverride,
  lookupStubOverride,
  mergeLoaders
  ) where

import           Control.Lens ( (&), (.~) )

import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Kind as DK
import qualified Data.Map as Map
import qualified Data.Text as T
import           Data.Typeable ( Typeable )
import           GHC.TypeLits ( type (<=) )
import           Data.Parameterized.Some ( Some(..) )

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
import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.Monad.Context as PMC
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.SimState as PS
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO

import qualified What4.Interface as W4

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
                }

-- | A PLT stub is allowed to make arbitrary modifications to the symbolic state
data StubOverride arch =
  StubOverride
    (forall sym v bin.
      W4.IsSymExprBuilder sym =>
      PB.KnownBinary bin =>
      sym ->
      PS.SimState sym arch v bin ->
      IO (PS.SimState sym arch v bin))

data ArchStubOverrides arch =
  ArchStubOverrides (Map.Map BS.ByteString (StubOverride arch))

lookupStubOverride ::
  ValidArchData arch -> BS.ByteString -> Maybe (StubOverride arch)
lookupStubOverride va nm = let ArchStubOverrides ov = validArchStubOverrides va in
  Map.lookup nm ov

mkMallocOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ length argument (unused currently ) -} ->
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ register for fresh pointer -} ->
  StubOverride arch
mkMallocOverride _rLen rOut = StubOverride $ \sym st -> do
  let mr = PS.simMaxRegion st
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  mr_nat <- W4.integerToNat sym (PS.unSE mr)
  zero <- W4.bvLit sym w (BVS.mkBV w 2)
  let fresh_ptr = PSR.ptrToEntry (CLM.LLVMPointer mr_nat zero)
  mr_inc <- PS.forScopedExpr sym mr $ \sym' mr' -> do
    one <- W4.intLit sym' 1
    W4.intAdd sym' mr' one
  return (st { PS.simMaxRegion = mr_inc, PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ fresh_ptr) })

mkClockOverride ::
  forall arch.
  16 <= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch)) {- ^ return register -} ->
  StubOverride arch
mkClockOverride rOut = StubOverride $ \sym st -> do
  let w = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
  zero_bv <- W4.bvLit sym w (BVS.mkBV w 0)
  zero_nat <- W4.natLit sym 0
  let zero_ptr = PSR.ptrToEntry (CLM.LLVMPointer zero_nat zero_bv)
  return (st { PS.simRegs = ((PS.simRegs st) & (MC.boundValue rOut) .~ zero_ptr) })


-- | A witness to the validity of an architecture, along with any
-- architecture-specific data required for the verifier
--
-- The first external domain handles domains for system calls, while the second
-- handles domains for external library calls
data SomeValidArch arch where
  SomeValidArch :: (ValidArch arch) => ValidArchData arch -> SomeValidArch arch

-- | Create a 'PA.SomeValidArch' from parsed ELF files
data ArchLoader err =
  ArchLoader (forall w.
              E.ElfMachine ->
              E.ElfHeaderInfo w ->
              E.ElfHeaderInfo w ->
              Either err (Some SomeValidArch)
             )

-- | Merge loaders by taking the first successful result (if it exists)
mergeLoaders ::
  ArchLoader err -> ArchLoader err -> ArchLoader err
mergeLoaders (ArchLoader l1) (ArchLoader l2) = ArchLoader $ \m i1 i2 ->
  case l1 m i1 i2 of
    Left _ -> l2 m i1 i2
    Right a -> Right a
