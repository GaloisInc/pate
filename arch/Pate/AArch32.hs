{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 ( SA.AArch32 ) where

import qualified SemMC.Architecture.AArch32 as SA
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Data.Macaw.ARM as ARM
import           Data.Macaw.AArch32.Symbolic ()

import qualified Pate.Arch as PA

instance PA.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PA.ValidArch SA.AArch32 where
  -- FIXME: generalize this properly for ARM
  tocProof = Nothing
  -- FIXME: define these
  rawBVReg _r = False
