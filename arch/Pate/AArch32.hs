{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 ( SA.AArch32 ) where

import qualified SemMC.Architecture.AArch32 as SA
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Data.Macaw.ARM as ARM
import           Data.Macaw.AArch32.Symbolic ()
import qualified Pate.Binary as PB
import qualified Pate.Monad as PM

instance PB.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PM.ValidArch SA.AArch32 where
  -- FIXME: generalize this properly for ARM
  tocProof = Nothing
