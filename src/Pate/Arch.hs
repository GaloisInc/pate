{-# LANGUAGE DataKinds #-}
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
