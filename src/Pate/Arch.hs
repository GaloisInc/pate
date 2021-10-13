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
  ArchConstraints(..),
  ValidArch(..),
  DedicatedRegister,
  HasDedicatedRegister(..),
  RegisterDisplay(..),
  fromRegisterDisplay
  ) where

import qualified Data.Kind as DK
import           Data.Typeable ( Typeable )
import           GHC.TypeLits ( type (<=) )

import qualified Data.ElfEdit as E
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Types as LCT

import qualified Pate.Binary as PB
import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.Monad.Context as PMC
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.ExternalCall as PVE

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
                       , dedicatedRegisterValidity :: forall sym bin tp . (LCB.IsSymInterface sym) => sym -> PMC.EquivalenceContext sym arch -> PB.WhichBinaryRepr bin -> PSR.MacawRegEntry sym tp -> DedicatedRegister arch (MS.ToCrucibleType tp) -> IO (PS.AssumptionFrame sym)
                       -- ^ Compute an assumption frame for the given arch-specific 'DedicatedRegister'
                       }

class
  ( MC.MemWidth (MC.ArchAddrWidth arch)
  , MBL.BinaryLoader arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
  , E.ElfWidthConstraints (MC.ArchAddrWidth arch)
  , MS.SymArchConstraints arch
  , 16 <= MC.RegAddrWidth (MC.ArchReg arch)
  ) => ArchConstraints arch where
  binArchInfo :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch)) -> MI.ArchitectureInfo arch

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
  ) => ValidArch arch where
  -- | Registers which are used for "raw" bitvectors (i.e. they are not
  -- used for pointers). These are assumed to always have region 0.
  rawBVReg :: forall tp. MC.ArchReg arch tp -> Bool
  -- | Determine how a register should be displayed to a user in reports and an
  -- interactive context
  displayRegister :: forall tp . MC.ArchReg arch tp -> RegisterDisplay String

-- | A witness to the validity of an architecture, along with any
-- architecture-specific data required for the verifier
--
-- The first external domain handles domains for system calls, while the second
-- handles domains for external library calls
data SomeValidArch arch where
  SomeValidArch :: (ValidArch arch, ArchConstraints arch)
                => PVE.ExternalDomain PVE.SystemCall arch
                -> PVE.ExternalDomain PVE.ExternalCall arch
                -> HasDedicatedRegister arch
                -> SomeValidArch arch
