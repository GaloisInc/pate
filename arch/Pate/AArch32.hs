{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Pate.AArch32 (
    SA.AArch32
  , AArch32Opts(..)
  , handleSystemCall
  , handleExternalCall
  , hasDedicatedRegister
  , argumentMapping
  , stubOverrides
  , archLoader
  ) where

import           Control.Lens ( (^?), (^.) )
import qualified Control.Lens as L
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit.Prim as EEP
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
import qualified Data.Macaw.Memory.LoadCommon as MML
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
import qualified Pate.Block as PB
import qualified Pate.Discovery.PLT as PLT
import qualified Pate.ExprMappable as PEM
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Panic as PP
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Domain as PD
import Data.List (nub)
import Pate.Config
import qualified Data.Parameterized.Map as MapF
import qualified Pate.Address as PA
import Data.Macaw.ARM.Identify (conditionalCallClassifier, conditionalReturnClassifier, wrapClassifierForPstateT)
import Control.Applicative
import qualified Data.Macaw.Discovery as MD
import qualified What4.JSON as W4S
import qualified Pate.SimState as PS
import qualified Data.Macaw.ARM.ARMReg as AR
import qualified Pate.SimulatorRegisters as PSr

data NoRegisters (tp :: LCT.CrucibleType) = NoRegisters Void

type instance PA.DedicatedRegister SA.AArch32 = NoRegisters

hasDedicatedRegister :: PA.HasDedicatedRegister SA.AArch32
hasDedicatedRegister =
  PA.HasDedicatedRegister { PA.asDedicatedRegister = const Nothing
                          , PA.dedicatedRegisterValidity = \_ _ _ _ (NoRegisters v) -> absurd v
                          }

-- | Variant of normal extractBlockPrecond that takes the initial value of the PSTATE_T flag from the beginning of
--   the function instead of the beginning of the block. This captures the assumption that within a function there are
--   no mode switches, and when function calls return (even if they switch modes) they always restore the PSTATE_T flag
hackyExtractBlockPrecond
  :: MA.AbsBlockState (MC.ArchReg SA.AArch32)
  -> MC.ArchSegmentOff SA.AArch32
  -> MA.AbsBlockState (MC.ArchReg SA.AArch32)
  -> Maybe (Either String (MC.ArchBlockPrecond SA.AArch32))
hackyExtractBlockPrecond absState _ _ = Just $
  case absState ^. MA.absRegState . MC.boundValue (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) of
    -- FIXME: always set the PSTATE_T flag to true
    --_ -> Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = True })
    MA.FinSet (Set.toList -> [bi]) -> Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = bi == 1 })
    MA.FinSet s -> Left ("Multiple FinSet values for PSTATE_T" ++ (show s))
    MA.StridedInterval {} -> Left "StridedInterval where PSTATE_T expected"
    MA.SubValue {} -> Left "SubValue where PSTATE_T expected"
    MA.TopV -> Left "TopV where PSTATE_T expected" {- Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = False }) -}


-- | A modified version of the AArch32 code discovery configuration
--
-- This is an unfortunate (and hopefully temporary) hack to deal with some
-- issues relating to Thumb code discovery in macaw-aarch32. This is safe as
-- long as your program does not use Thumb mode (and, more specifically, as long
-- as it doesn't issue a mode switch in the middle of a thumb function).
--
-- See Note [Thumb Code Discovery Hacks] for details
-- FIXME: this is subsumed by applying hackyExtractBlockPrecond later in the pipeline (see: 'Pate.Discovery.ParsedFunctions')
hacky_arm_linux_info :: MAI.ArchitectureInfo SA.AArch32
hacky_arm_linux_info =
  ARM.arm_linux_info

instance W4S.W4Serializable sym (ARMReg.ARMReg tp) where
  w4Serialize = PA.serializeRegister

instance W4S.W4SerializableF sym ARMReg.ARMReg where
instance (W4S.W4SerializableFC ARMReg.ARMReg) where

instance PEM.ExprFoldable sym (ARMReg.ARMReg tp) where
  foldExpr _ _ _ = return

instance PEM.ExprFoldableF sym ARMReg.ARMReg where
instance (PEM.ExprFoldableFC ARMReg.ARMReg) where

instance PA.ValidArch SA.AArch32 where
  type ArchConfigOpts SA.AArch32 = AArch32Opts SA.AArch32
  -- FIXME: define these
  rawBVReg _r = False
  displayRegister = display
  argumentNameFrom = argumentNameFrom
  binArchInfo = const hacky_arm_linux_info
  discoveryRegister reg =
       Some reg == (Some (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")))
  readRegister = \case
    "r0" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
    "r1" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
    "r2" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
    "r3" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
    "r4" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4")
    -- TODO
    "sp" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R13")
    "r13" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R13")
    "pc" -> Just $ Some $ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_PC")
    _ -> Nothing
  -- currently the only arch-specific (non-terminal) statements we have are
  -- uninterpreted
  uninterpretedArchStmt _ = True

  archClassifier _ =
        conditionalCallClassifier
    <|> conditionalReturnClassifier
    <|> MD.branchClassifier
    <|> MD.noreturnCallClassifier
    <|> MD.callClassifier
    <|> MD.returnClassifier
    <|> MD.jumpTableClassifier
    <|> MD.pltStubClassifier
    <|> MD.directJumpClassifier
    <|> MD.tailCallClassifier

  archClassifierWrapper = wrapClassifierForPstateT

  archExtractArchTerms = \term st mret -> Just $ case term of
    MAA.CallIf{} -> MD.ParsedCall st mret
    MAA.CallIfNot{} -> MD.ParsedCall st mret
    MAA.ReturnIf{} -> MD.ParsedReturn st
    MAA.ReturnIfNot{} -> MD.ParsedReturn st

  archSymReturnAddress _sym simSt = do
    let rs = PS.simRegs simSt
    return $ PSr.macawRegValue $ rs ^. MC.boundValue AR.arm_LR

data AArch32Opts arch = AArch32Opts { thumbMode :: Bool }

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
  return $ (PD.universalDomain sym){ PED.eqDomainRegisters = regDomain }

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
  return $ (PD.universalDomain sym){ PED.eqDomainRegisters = regDomain }

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
stubOverrides = 
  PA.ArchStubOverrides (PA.mkDefaultStubOverride "__pate_stub" r0 ) $ \fs ->
    case PB.fnSymBase fs of
      -- FIXME: multiple variants of this constructor
      "basic_string" -> Just $ PA.mkDefaultStubOverride "basic_string" r0
      "print" -> Just $ PA.mkObservableOverride "print" r0 [r0]
      _ -> lookup (PB.fnSymBase fs) override_list
  where
    override_list =
      [ ("malloc", PA.mkMallocOverride r0 r0)
      -- FIXME: arguments are interpreted differently for calloc
      , ("calloc", PA.mkMallocOverride r0 r0)
      -- FIXME: arguments are interpreted differently for reallolc
      , ("realloc", PA.mkMallocOverride r0 r0)
      , ("clock", PA.mkClockOverride r0)
      , ("write", PA.mkWriteOverride "write" r0 r1 r2 r0)
      -- FIXME: fixup arguments for fwrite (len = size * nmemb)
      , ("fwrite", PA.mkWriteOverride "fwrite" r3 r0 r1 r0)
      , ("printf", PA.mkObservableOverride "printf" r0 [r0,r1])
      , ("puts", PA.mkObservableOverride "puts" r0 [r0,r1])
      -- fixme: double check this
      , ("ceilf", PA.mkDefaultStubOverrideArg "ceilf" [Some v0] r0)
      -- FIXME: check abi for args
      , ("fread", PA.mkDefaultStubOverrideArg "fread" [Some r0, Some r1, Some r2, Some r4] r0)
      -- FIXME: default stubs below here
      -- , ("sync", PA.mkDefaultStubOverrideArg "sync" [Some r0] r0)
      -- , ("dirCache", PA.mkDefaultStubOverrideArg "dirCache" [Some r0] r0)
      -- FIXME: reads from the stack as well
      , ("timestamp", PA.mkDefaultStubOverrideArg "timestamp" [Some r0, Some r1, Some r2, Some r3] r0)
      , ("usb_serial_getchar", PA.mkDefaultStubOverride "usb_serial_getchar" r0)
      , ("usb_serial_available", PA.mkDefaultStubOverride "usb_serial_available" r0)
      , ("usb_serial_write", PA.mkWriteOverride "usb_serial_write" r0 r0 r1 r0)
      , ("strlen", PA.mkDefaultStubOverrideArg "strlen" [Some r0] r0)
      , ("println", PA.mkWriteOverride "println" r0 r0 r1 r0)
      , ("strcmp", PA.mkDefaultStubOverrideArg "strcmp" [Some r0, Some r1] r0)
      , ("strncpy", PA.mkDefaultStubOverrideArg "strncpy" [Some r0, Some r1] r0)
      , ("random", PA.mkDefaultStubOverrideArg "random" [Some r0] r0)
      ] ++
      (map mkDefault $
        [ "memcpy" -- FIXME: needs implementation
        , "memset" -- FIXME: needs implementation
        , "gettimeofday" -- FIXME: needs implementation
        , "getopt"
        , "fprintf"
        , "open"
        , "atoi"
        , "openat"
        , "__errno_location"
        , "ioctl"
        , "fopen"
        , "ERR_print_errors_fp"
        , "RAND_bytes"
        , "close"
        , "fclose"
        , "lseek"
        , "strcpy"
        , "sleep"
        , "socket"
        , "setsockopt"
        , "bind"
        , "select"
        , "free"
        , "sigfillset"
        , "sigaction"
        , "setitimer"
        , "read"
        -- PLT Stubs
        , "EVP_CIPHER_CTX_new"
        , "EVP_DecryptInit_ex"
        , "EVP_DecryptUpdate"
        , "EVP_DecryptFinal_ex"
        , "EVP_EncryptInit_ex"
        , "EVP_EncryptUpdate"
        , "EVP_EncryptFinal_ex"
        , "EVP_CIPHER_CTX_free"
        , "EVP_aes_256_cbc"
        , "BIO_dump_fp"
        ])
    mkDefault nm = (nm, PA.mkDefaultStubOverride nm r0)

    r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
    r1 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
    r2 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
    r3 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
    r4 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4")

    v0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_V0")
    v1 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_V1")
    v2 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_V2")
    --r3 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")

instance MCS.HasArchTermEndCase MAA.ARMTermStmt where
  archTermCase = \case
    MAA.ReturnIf{} -> MCS.MacawBlockEndReturn
    MAA.ReturnIfNot{} -> MCS.MacawBlockEndReturn
    MAA.CallIf{} -> MCS.MacawBlockEndCall
    MAA.CallIfNot{} -> MCS.MacawBlockEndCall

getArchOpts :: PatchData -> Maybe (AArch32Opts SA.AArch32)
getArchOpts pd = case nub (archOpts pd) of
  ["thumb"] -> Just (AArch32Opts True)
  [] -> Just (AArch32Opts False)
  _ -> Nothing

-- | PLT stub information for ARM32 relocation types.
--
-- When we bump the macaw submodule to bring in the changes from
-- https://github.com/GaloisInc/macaw/pull/320, we can delete the code below and
-- import it from macaw-aarch32 instead.
armPLTStubInfo :: PLT.PLTStubInfo EEP.ARM32_RelocationType
armPLTStubInfo = PLT.PLTStubInfo
  { PLT.pltFunSize     = 20
  , PLT.pltStubSize    = 12
  , PLT.pltGotStubSize = error "Unexpected .plt.got section in ARM32 binary"
  }

archLoader :: PA.ArchLoader PEE.LoadError
archLoader = PA.ArchLoader $ \pd em origHdr patchedHdr ->
  case (em, EEP.headerClass (EEP.header origHdr)) of
    (EEP.EM_ARM, EEP.ELFCLASS32) -> case getArchOpts pd of
      Just opts ->
        let vad = PA.ValidArchData { PA.validArchSyscallDomain = handleSystemCall
                                  , PA.validArchFunctionDomain = handleExternalCall
                                  , PA.validArchDedicatedRegisters = hasDedicatedRegister
                                  , PA.validArchArgumentMapping = argumentMapping
                                  , PA.validArchOrigExtraSymbols =
                                      PLT.pltStubSymbols' armPLTStubInfo MML.defaultLoadOptions origHdr
                                  , PA.validArchPatchedExtraSymbols =
                                      PLT.pltStubSymbols' armPLTStubInfo MML.defaultLoadOptions patchedHdr
                                  , PA.validArchStubOverrides = stubOverrides
                                  , PA.validArchInitAbs = case thumbMode opts of
                                      False -> PB.defaultMkInitialAbsState
                                      True -> PB.MkInitialAbsState (\_ _ -> MapF.singleton (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) (MA.FinSet (Set.singleton 1)))
                                  , PA.validArchExtractPrecond = hackyExtractBlockPrecond
                                  }
        in Right (Some (PA.SomeValidArch vad))
      Nothing -> Left (PEE.InvalidArchOpts (archOpts pd))
    _ -> Left (PEE.UnsupportedArchitecture em)

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
