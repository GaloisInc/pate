{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Arch (
  SomeValidArch(..),
  ArchConstraints(..),
  ValidArch(..),
  RegisterDisplay(..),
  fromRegisterDisplay,
  HasTOCDict(..),
  HasTOCReg(..),
  withTOCCases
  ) where

import           Data.Typeable ( Typeable )
import           GHC.TypeLits ( type (<=) )

import qualified Data.ElfEdit as E
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.PPC as TOC (HasTOC(..))
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT

import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.Verification.ExternalCall as PVE

class
  ( MC.MemWidth (MC.ArchAddrWidth arch)
  , MBL.BinaryLoader arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
  , E.ElfWidthConstraints (MC.ArchAddrWidth arch)
  , MS.SymArchConstraints arch
  , 16 <= MC.RegAddrWidth (MC.ArchReg arch)
  ) => ArchConstraints arch where
  binArchInfo :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch)) -> MI.ArchitectureInfo arch

class TOC.HasTOC arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch)) => HasTOCReg arch where
  toc_reg :: MC.ArchReg arch (MT.BVType (MC.ArchAddrWidth arch))

data HasTOCDict arch where
  HasTOCDict :: HasTOCReg arch => HasTOCDict arch

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
  -- | an optional witness that the architecture has a table of contents
  tocProof :: Maybe (HasTOCDict arch)
  -- | Registers which are used for "raw" bitvectors (i.e. they are not
  -- used for pointers). These are assumed to always have region 0.
  rawBVReg :: forall tp. MC.ArchReg arch tp -> Bool
  -- | Determine how a register should be displayed to a user in reports and an
  -- interactive context
  displayRegister :: forall tp . MC.ArchReg arch tp -> RegisterDisplay String

withTOCCases ::
  forall proxy arch a.
  ValidArch arch =>
  proxy arch ->
  a ->
  ((HasTOCReg arch, TOC.HasTOC arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))) => a) ->
  a
withTOCCases _ noToc hasToc = case tocProof @arch of
  Just HasTOCDict -> hasToc
  Nothing -> noToc

-- | A witness to the validity of an architecture, along with any
-- architecture-specific data required for the verifier
--
-- The first external domain handles domains for system calls, while the second
-- handles domains for external library calls
data SomeValidArch arch where
  SomeValidArch :: (ValidArch arch, ArchConstraints arch)
                => PVE.ExternalDomain PVE.SystemCall arch
                -> PVE.ExternalDomain PVE.ExternalCall arch
                -> SomeValidArch arch
