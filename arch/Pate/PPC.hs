{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64, PPC.PPC32 )
where

import qualified Pate.Binary as PB
import qualified Pate.Monad as PM
import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()


instance PB.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info

instance PB.ArchConstraints PPC.PPC32 where
  binArchInfo = PPC.ppc32_linux_info

-- | Calling convention details, see:
--
-- https://www.ibm.com/support/knowledgecenter/en/ssw_aix_72/assembler/idalangref_reg_use_conv.html
instance PM.ValidArch PPC.PPC64 where
  toc_reg = Just (PPC.PPC_GP (PPC.GPR 2))

-- | The 32 bit and 64 bit architectures have the same calling convention
instance PM.ValidArch PPC.PPC32 where
  toc_reg = Just (PPC.PPC_GP (PPC.GPR 2))
