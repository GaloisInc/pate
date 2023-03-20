{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Register (
    RegisterCase(..)
  , registerCase
  ) where

import qualified Data.Parameterized.Classes as PC

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import qualified Pate.ExprMappable as PEM

-- | Helper for doing a case-analysis on registers
data RegisterCase arch tp where
  -- | instruction pointer
  RegIP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | stack pointer
  RegSP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | non-specific bitvector (zero-region pointer) register
  RegBV :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific pointer register
  RegGPtr :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific non-pointer register
  RegElse :: RegisterCase arch tp
  -- | A dedicated register whose value is determined by the ABI (see
  -- 'PA.DedicatedRegister' for details)
  RegDedicated :: PA.DedicatedRegister arch tp -> RegisterCase arch tp

registerCase ::
  forall arch tp.
  PA.ValidArch arch =>
  PA.HasDedicatedRegister arch ->
  CC.TypeRepr (MS.ToCrucibleType tp) ->
  MM.ArchReg arch tp ->
  RegisterCase arch (MS.ToCrucibleType tp)
registerCase hdr repr r =
  if | Just PC.Refl <- PC.testEquality r (MM.ip_reg @(MM.ArchReg arch)) -> RegIP
     | Just PC.Refl <- PC.testEquality r (MM.sp_reg @(MM.ArchReg arch)) -> RegSP
     | Just dr <- PA.asDedicatedRegister hdr r -> RegDedicated dr
     | CLM.LLVMPointerRepr {} <- repr ->
       case PA.rawBVReg r of
         True -> RegBV
         False -> RegGPtr
     | otherwise -> RegElse