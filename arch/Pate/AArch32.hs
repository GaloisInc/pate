{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 (
    SA.AArch32
  , handleSystemCall
  , handleExternalCall
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified What4.Interface as WI

import qualified SemMC.Architecture.AArch32 as SA
import           Data.Macaw.BinaryLoader.AArch32 ()

import qualified Data.Macaw.ARM as ARM
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import           Data.Macaw.AArch32.Symbolic ()
import qualified Language.ASL.Globals as ASL

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Verification.ExternalCall as PVE

instance PA.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PA.ValidArch SA.AArch32 where
  -- FIXME: generalize this properly for ARM
  tocProof = Nothing
  -- FIXME: define these
  rawBVReg _r = False
  displayRegister = display

-- | For the ARM architecture, we want to hide a few details of the translation
-- that aren't actually user visible.  We also want to ensure that some of the
-- magical architecture detail registers (e.g., @__Sleeping@) are sorted lower
-- than the interesting registers.
display :: ARMReg.ARMReg tp -> PA.RegisterDisplay String
display reg =
  case reg of
    ARMReg.ARMDummyReg -> PA.Hidden
    ARMReg.ARMGlobalBV ASL.MemoryRef -> PA.Hidden
    ARMReg.ARMGlobalBV (ASL.GPRRef gr) -> ASL.withGPRRef gr $ \nr -> PA.Normal ("r" ++ show (PN.natValue nr))
    ARMReg.ARMGlobalBV (ASL.SIMDRef sr) -> ASL.withSIMDRef sr $ \nr -> PA.Normal ("v" ++ show (PN.natValue nr))
    ARMReg.ARMGlobalBV ref -> PA.Architectural (show (ASL.globalRefSymbol ref))
    ARMReg.ARMGlobalBool ref -> PA.Architectural (show (ASL.globalRefSymbol ref))

-- | The Linux syscall convention uses r0-r5 for registers, with r7 containing the system call number
handleSystemCall :: PVE.ExternalDomain PVE.SystemCall SA.AArch32
handleSystemCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = Map.fromList [ (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R5")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R7")), WI.truePred sym)
                               ]
  return $ PES.StatePred { PES.predRegs = regDomain
                         , PES.predStack = PEM.memPredTrue sym
                         , PES.predMem = PEM.memPredTrue sym
                         }

-- | The Linux calling convention uses r0-r3 for arguments
--
-- This happens to handle arguments passed on the stack correctly because it
-- requires stack equivalence.
--
-- FIXME: This does *not* capture equivalence for the values read from pointers
-- passed in registers; that would require either analyzing and summarizing the
-- external calls or providing manual summaries for known callees
--
-- FIXME: This does not account for floating point registers
handleExternalCall :: PVE.ExternalDomain PVE.ExternalCall SA.AArch32
handleExternalCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = Map.fromList [ (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")), WI.truePred sym)
                               , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R11")), WI.truePred sym)
                               ]
  return $ PES.StatePred { PES.predRegs = regDomain
                         , PES.predStack = PEM.memPredTrue sym
                         , PES.predMem = PEM.memPredTrue sym
                         }
