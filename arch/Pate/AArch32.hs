{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.AArch32 (
    SA.AArch32
  , handleSystemCall
  , handleExternalCall
  , hasDedicatedRegister
  , argumentMapping
  , stubOverrides
  ) where

import           Control.Lens ( (^?), (^.), (&), (.~) )
import qualified Control.Lens as L
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Set as Set
import qualified Data.Text as T
import           Data.Void ( Void, absurd )
import qualified What4.Interface as WI
import qualified Data.Map as Map

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.AArch32.Symbolic as DMAS
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.AArch32 as SA

import qualified Data.Macaw.ARM as ARM
import qualified Data.Macaw.ARM.Arch as MAA
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import           Data.Macaw.AArch32.Symbolic ()
import qualified Language.ASL.Globals as ASL

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
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


hackyExtractBlockPrecond
  :: MC.ArchSegmentOff SA.AArch32
  -> MA.AbsBlockState (MC.ArchReg SA.AArch32)
  -> Either String (MC.ArchBlockPrecond SA.AArch32)
hackyExtractBlockPrecond _ absState =
  case absState ^. MA.absRegState . MC.boundValue (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) of
    MA.FinSet (Set.toList -> [bi]) -> Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = bi == 1 })
    MA.FinSet {} -> Left "Multiple FinSet values for PSTATE_T"
    MA.StridedInterval {} -> Left "StridedInterval where PSTATE_T expected"
    MA.SubValue {} -> Left "SubValue where PSTATE_T expected"
    MA.TopV -> Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = False })

-- | A modified version of the AArch32 code discovery configuration
--
-- This is an unfortunate (and hopefully temporary) hack to deal with some
-- issues relating to Thumb code discovery in macaw-aarch32. This is safe as
-- long as your program does not use Thumb mode (and, more specifically, as long
-- as it doesn't issue a mode switch in the middle of a thumb function).
--
-- See Note [Thumb Code Discovery Hacks] for details
hacky_arm_linux_info :: MAI.ArchitectureInfo SA.AArch32
hacky_arm_linux_info =
  ARM.arm_linux_info { MAI.extractBlockPrecond = hackyExtractBlockPrecond }

instance PA.ValidArch SA.AArch32 where
  -- FIXME: define these
  rawBVReg _r = False
  displayRegister = display
  argumentNameFrom = argumentNameFrom
  binArchInfo = const hacky_arm_linux_info


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
  let regDomain = PER.fromList $
        [ (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R5")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R7")), WI.truePred sym)
        ]
  return $ PED.EquivalenceDomain { PED.eqDomainRegisters = regDomain
                                 , PED.eqDomainStackMemory = PEM.universal sym
                                 , PED.eqDomainGlobalMemory = PEM.universal sym
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
  let regDomain = PER.fromList $
        [ (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")), WI.truePred sym)
        , (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")), WI.truePred sym)
        ]
  return $ PED.EquivalenceDomain { PED.eqDomainRegisters = regDomain
                                 , PED.eqDomainStackMemory = PEM.universal sym
                                 , PED.eqDomainGlobalMemory = PEM.universal sym
                                 }

argumentMapping :: PVO.ArgumentMapping SA.AArch32
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

stubOverrides :: PA.ArchStubOverrides SA.AArch32
stubOverrides = PA.ArchStubOverrides $
  Map.fromList
    [ (BSC.pack "malloc", PA.mkMallocOverride r0 r0) ]
  where
    r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")

instance MCS.HasArchTermEndCase MAA.ARMTermStmt where
  archTermCase = \case
    MAA.ReturnIf{} -> MCS.MacawBlockEndReturn
    MAA.ReturnIfNot{} -> MCS.MacawBlockEndReturn

{- Note [Thumb Code Discovery Hacks]

The underlying problem here is that macaw's code discovery configuration is not
quite expressive enough to handle AArch32 completely (doing so safely is a huge
problem that would technically require whole program analysis or context
dependent analysis).

The proximate error is that calls issued via @blx@ (branch with possible mode
switch) can break code discovery at the return address. There are a number of
issues that all collide here:

1. When the address being jumped to is symbolic (e.g., read from memory), the
   abstract interpretation has no idea what the value of PSTATE_T will be (since
   it can't tell if the low bit is set or not)

2. Because PSTATE_T is symbolic at the call site, it is symbolic at the start of
   the return site, which causes 'extractBlockPrecond' to fail (in the default
   macaw-aarch32)

3. Even if that could be resolved, it would be wrong to take the PSTATE_T at the
   call as the PSTATE_T in the return block, as the callee is *highly* likely to
   switch the mode back (but is not required to do so)

All told, macaw is not currently set up to handle this.  The most desirable
outcome would probably be to preserve the PSTATE_T from before the @blx@
instruction, but we don't have a good way to do that.

This hack just defaults PSTATE_T to ARM mode if it can't tell what it should be,
which is unsafe in general, but fine under the caveats:

- The program does not use Thumb mode at all
- The program does not issue a @blx@ instruction (or similar) in the middle of a function

-}
