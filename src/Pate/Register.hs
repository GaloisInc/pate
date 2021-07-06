{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Register (
  RegisterCase(..)
  , registerCase
  ) where

import qualified Data.Parameterized.Classes as PC
import           Data.Proxy ( Proxy(..) )

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA

-- | Helper for doing a case-analysis on registers
data RegisterCase arch tp where
  -- | instruction pointer
  RegIP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | stack pointer
  RegSP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | table of contents register (if defined)
  RegTOC :: PA.HasTOCReg arch => RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | non-specific bitvector (zero-region pointer) register
  RegBV :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific pointer register
  RegGPtr :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific non-pointer reguster
  RegElse :: RegisterCase arch tp

registerCase ::
  forall arch tp.
  PA.ValidArch arch =>
  CC.TypeRepr (MS.ToCrucibleType tp) ->
  MM.ArchReg arch tp ->
  RegisterCase arch (MS.ToCrucibleType tp)
registerCase repr r = case PC.testEquality r (MM.ip_reg @(MM.ArchReg arch)) of
  Just PC.Refl -> RegIP
  _ -> case PC.testEquality r (MM.sp_reg @(MM.ArchReg arch)) of
    Just PC.Refl -> RegSP
    _ -> PA.withTOCCases (Proxy @arch) nontoc $
      case PC.testEquality r (PA.toc_reg @arch) of
        Just PC.Refl -> RegTOC
        _ -> nontoc
  where
    nontoc :: RegisterCase arch (MS.ToCrucibleType tp)
    nontoc = case repr of
      CLM.LLVMPointerRepr{} -> case PA.rawBVReg r of
        True -> RegBV
        False -> RegGPtr
      _ -> RegElse
