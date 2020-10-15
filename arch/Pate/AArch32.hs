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

import qualified Pate.Binary as PB
import qualified Pate.Monad as PM

instance PB.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PM.ValidArch SA.AArch32 where
  funCallStable reg =
    case reg of
      ARMReg.ARMGlobalBV ref
        -- Local registers (caller save)
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R4") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R5") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R5") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R6") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R7") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R8") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R9") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R10") -> True
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R11") -> True
        -- Stack pointer
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R13") -> True
        -- Link register
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R14") -> True
      _ -> False
  funCallArg reg =
    Some reg `elem` [ Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0"))
                    , Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1"))
                    , Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2"))
                    , Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3"))
                    ]
  funCallIP reg =
    case reg of
      ARMReg.ARMGlobalBV ref
        | Just Refl <- testEquality ref (ASL.knownGlobalRef @"_R14") -> Just Refl
      _ -> Nothing
