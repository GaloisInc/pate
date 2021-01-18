{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64, PPC.PPC32 )
where

import qualified Pate.Binary as PB
import qualified Pate.Types as PT
import qualified Pate.Monad as PM
import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()


instance PB.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info

instance PB.ArchConstraints PPC.PPC32 where
  binArchInfo = PPC.ppc32_linux_info

instance PT.HasTOCReg PPC.PPC64 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PT.HasTOCReg PPC.PPC32 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PM.ValidArch PPC.PPC32 where
  tocProof = Just PT.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False

instance PM.ValidArch PPC.PPC64 where
  tocProof = Just PT.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
