{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64, PPC.PPC32 )
where

import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()

import qualified Pate.Arch as PA

instance PA.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info

instance PA.ArchConstraints PPC.PPC32 where
  binArchInfo = PPC.ppc32_linux_info

instance PA.HasTOCReg PPC.PPC64 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PA.HasTOCReg PPC.PPC32 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PA.ValidArch PPC.PPC32 where
  tocProof = Just PA.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False

instance PA.ValidArch PPC.PPC64 where
  tocProof = Just PA.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
