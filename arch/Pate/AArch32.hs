{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 (
    SA.AArch32
  , handleSystemCall
  , handleExternalCall
  , hasDedicatedRegister
  , argumentMapping
  ) where

import           Control.Lens ( (^?) )
import qualified Control.Lens as L
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import           Data.Void ( Void, absurd )
import qualified What4.Interface as WI

import qualified Data.Macaw.AArch32.Symbolic as DMAS
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.AArch32 as SA

import qualified Data.Macaw.ARM as ARM
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import           Data.Macaw.AArch32.Symbolic ()
import qualified Language.ASL.Globals as ASL

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Panic as PP
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO

data NoRegisters (tp :: LCT.CrucibleType) = NoRegisters Void

type instance PA.DedicatedRegister SA.AArch32 = NoRegisters

hasDedicatedRegister :: PA.HasDedicatedRegister SA.AArch32
hasDedicatedRegister =
  PA.HasDedicatedRegister { PA.asDedicatedRegister = const Nothing
                          , PA.dedicatedRegisterValidity = \_ _ _ _ (NoRegisters v) -> absurd v
                          }

instance PA.ArchConstraints SA.AArch32 where
  binArchInfo = const ARM.arm_linux_info

instance PA.ValidArch SA.AArch32 where
  -- FIXME: define these
  rawBVReg _r = False
  displayRegister = display
  argumentNameFrom = argumentNameFrom

argumentNameFrom
  :: [T.Text]
  -> ARMReg.ARMReg tp
  -> Maybe T.Text
argumentNameFrom names reg
  | ARMReg.ARMGlobalBV (ASL.GPRRef gr) <- reg =
    ASL.withGPRRef gr $ \nr ->
      let num = PN.natValue nr
      in if | num >= 0 && num <= 3 -> names ^? L.traversed . L.index (fromIntegral num)
            | otherwise -> Nothing
  | otherwise = Nothing

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
                               ]
  return $ PES.StatePred { PES.predRegs = regDomain
                         , PES.predStack = PEM.memPredTrue sym
                         , PES.predMem = PEM.memPredTrue sym
                         }

argumentMapping :: PVO.ArgumentMapping SA.AArch32 sym
argumentMapping =
  PVO.ArgumentMapping { PVO.functionIntegerArgumentRegisters = \actualsRepr registerFile ->
                          let ptrWidth = PN.knownNat @32
                              lookupReg r = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth) (LCS.unRV (DMAS.lookupReg r registerFile))
                              regList = map lookupReg [ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
                                                      , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
                                                      , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
                                                      , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
                                                      ]
                          in PVO.buildArgumentRegisterAssignment ptrWidth actualsRepr regList
                      , PVO.functionReturnRegister = \retRepr override registerFile ->
                          case retRepr of
                            LCT.UnitRepr -> override >> return registerFile
                            LCLM.LLVMPointerRepr w
                              | Just PC.Refl <- PC.testEquality w (PN.knownNat @32) -> do
                                  result <- override
                                  let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
                                  return $! DMAS.updateReg r0 (const (LCS.RV result)) registerFile
                            _ -> PP.panic PP.AArch32 "argumentMapping" ["Unsupported return value type: " ++ show retRepr]
                      }
