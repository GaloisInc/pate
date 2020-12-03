{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC
  ( PPC.PPC64 )
where

import           Data.Type.Equality
import qualified Pate.Binary as PB
import qualified Pate.Monad as PM
import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()


instance PB.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info


instance PM.ValidArch PPC.PPC64 where
  toc_reg = Just (PPC.PPC_GP (PPC.GPR 2))
