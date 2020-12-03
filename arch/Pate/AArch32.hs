{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 ( SA.AArch32 ) where

import           Data.Parameterized.Some ( Some(..) )
import           Data.Type.Equality

import qualified SemMC.Architecture.AArch32 as SA
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Language.ASL.Globals as ASL
import qualified Data.Macaw.ARM as ARM
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import           Data.Macaw.AArch32.Symbolic ()
import qualified Data.Parameterized.NatRepr as NR
import qualified Pate.Binary as PB
import qualified Pate.Monad as PM

instance PB.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PM.ValidArch SA.AArch32 where
  -- FIXME: generalize this properly for ARM
  toc_reg = Nothing
