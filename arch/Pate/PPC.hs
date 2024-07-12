{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC (
    PPC.PPC64
  , PPC.PPC32
  , PPC.AnyPPC
  , handleSystemCall
  , handleExternalCall
  , ppc64HasDedicatedRegister
  , ppc32HasDedicatedRegister
  , argumentMapping
  , stubOverrides
  , archLoader
  )
where

import           Control.Lens ( (^.), (^?) )
import qualified Control.Lens as L
import           Control.Applicative ( (<|>), Const (..) )
import qualified Control.Monad.Catch as CMC
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit.Prim as EEP
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import qualified Data.Map as Map
import           Data.Void ( Void, absurd )
import           Data.Word ( Word8 )
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits
import qualified What4.Interface as WI

import qualified Data.Macaw.BinaryLoader.PPC as TOC
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.Types as MT
import qualified Data.Word.Indexed as W
import qualified Dismantle.PPC as PPC
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.PPC as SP

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PB
import qualified Pate.Block as PBl
import qualified Pate.Discovery as PD
import qualified Pate.Discovery.PLT as PLT
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Event as PE
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Domain as PD

import           Pate.TraceTree
import Data.Macaw.CFG.Core
import qualified What4.JSON as W4S
import qualified Data.Macaw.CFG as MC
import qualified Pate.SimState as PS
import qualified Data.Parameterized.Map as MapF
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Set as Set
import qualified Pate.Memory.MemTrace as PMT
import Data.Data (Typeable)

-- | There is just one dedicated register on ppc64
data PPC64DedicatedRegister tp where
  -- | The Table of Contents register; note that we capture that it is a 64 bit
  -- register since it holds a pointer
  RegTOC :: (tp ~ CLM.LLVMPointerType 64) => PPC64DedicatedRegister tp

type instance PA.DedicatedRegister PPC.PPC64 = PPC64DedicatedRegister

-- | PowerPC 64 (at least in the most common ABI, represented by this function)
-- has a single dedicated register: r2 is the Table of Contents (TOC), which is
-- populated by the kernel on startup.
ppc64AsDedicatedRegister :: PPC.PPCReg PPC.V64 tp -> Maybe (PPC64DedicatedRegister (MS.ToCrucibleType tp))
ppc64AsDedicatedRegister reg =
  case reg of
    PPC.PPC_GP (PPC.GPR 2) -> Just RegTOC
    _ -> Nothing

-- | Look up the TOC for the function currently being analyzed
--
-- The returned value is the concrete address that would be in r2 at the
-- start of the function
getCurrentTOC
  :: (HasCallStack)
  => PMC.EquivalenceContext sym PPC.PPC64
  -> PB.WhichBinaryRepr bin
  -> IO (W.W 64)
getCurrentTOC ctx binRepr = PPa.runPatchPairT $ do
  ctx' <- PPa.get binRepr (PMC.binCtxs ctx)
  blks <- noTracing $ PD.getBlocks' ctx (ctx ^. PMC.currentFunc)
  PE.Blocks _ _ (pblk:_) <- PPa.get binRepr blks
  let
    toc = TOC.getTOC (PMC.binary ctx')
    addr = MD.pblockAddr pblk
  case TOC.lookupTOC toc addr of
    Just w -> return w
    Nothing -> CMC.throwM (PEE.MissingTOCEntry @PPC.PPC64 addr)

ppc64DedicatedRegisterFrame
  :: forall sym tp bin
   . (CB.IsSymInterface sym)
  => sym
  -> PMC.EquivalenceContext sym PPC.PPC64
  -> PB.WhichBinaryRepr bin
  -> PSR.MacawRegEntry sym tp
  -> PPC64DedicatedRegister (MS.ToCrucibleType tp)
  -> IO (PAS.AssumptionSet sym)
ppc64DedicatedRegisterFrame sym ctx binRepr entry dr =
  case dr of
    RegTOC -> do
      tocW <- getCurrentTOC ctx binRepr
      tocBV <- WI.bvLit sym PN.knownNat (BVS.mkBV PN.knownNat (W.unW tocW))
      let targetTOC = CLM.LLVMPointer (PMC.globalRegion ctx) tocBV
      return $ PAS.macawRegBinding sym entry (PSR.ptrToEntry targetTOC)

-- | A dedicated register handler for the most common PPC64 ABI that uses a
-- Table of Contents (TOC) register
ppc64HasDedicatedRegister :: PA.HasDedicatedRegister PPC.PPC64
ppc64HasDedicatedRegister =
  PA.HasDedicatedRegister { PA.asDedicatedRegister = ppc64AsDedicatedRegister
                          , PA.dedicatedRegisterValidity = ppc64DedicatedRegisterFrame
                          }

-- | This is a wrapper around 'Void' with the necessary type parameter
data NoRegisters (tp :: LCT.CrucibleType) = NoRegisters Void

type instance PA.DedicatedRegister PPC.PPC32 = NoRegisters

ppc32HasDedicatedRegister :: PA.HasDedicatedRegister PPC.PPC32
ppc32HasDedicatedRegister =
  PA.HasDedicatedRegister { PA.asDedicatedRegister = const Nothing
                          , PA.dedicatedRegisterValidity = \_ _ _ _ (NoRegisters v) -> absurd v
                          }

instance forall v sym tp. SP.KnownVariant v => W4S.W4Serializable sym (PPC.PPCReg v tp) where
  w4Serialize = case SP.knownVariant @v of
    PPC.V32Repr -> PA.serializeRegister
    PPC.V64Repr -> PA.serializeRegister

instance SP.KnownVariant v => W4S.W4SerializableF sym (PPC.PPCReg v) where
instance SP.KnownVariant v => W4S.W4SerializableFC (PPC.PPCReg v) where

instance PA.ValidArch PPC.PPC32 where
  type ArchConfigOpts PPC.PPC32 = ()
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    PPC.PPC_LNK -> True
    _ -> False
  displayRegister = display
  argumentNameFrom = argumentNameFromGeneric
  binArchInfo = const PPC.ppc32_linux_info
  discoveryRegister = const False
  -- FIXME: TODO
  readRegister _ = Nothing
  uninterpretedArchStmt _ = False
  archSymReturnAddress _sym simSt = do
    let rs = PS.simRegs simSt
    return $ PSR.macawRegValue $ rs ^. MC.boundValue PPC.PPC_LNK

instance PA.ValidArch PPC.PPC64 where
  type ArchConfigOpts PPC.PPC64 = ()
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
  displayRegister = display
  argumentNameFrom = argumentNameFromGeneric
  binArchInfo = PPC.ppc64_linux_info
  discoveryRegister = const False
  -- FIXME: TODO
  readRegister _ = Nothing
  uninterpretedArchStmt _ = False
  archClassifierWrapper cl = PPC.ppcReadPCClassifier <|> cl
  archSymReturnAddress _sym simSt = do
    let rs = PS.simRegs simSt
    return $ PSR.macawRegValue $ rs ^. MC.boundValue PPC.PPC_LNK

-- | Determine the argument name for the argument held in the given register.
--
-- In PPC32 and PPC64, arguments are passed in r3-r10, with r3 getting the first
-- argument (i.e., r3 is at index 0 in the list of argument names).
argumentNameFromGeneric
  :: [T.Text]
  -> PPC.PPCReg v tp
  -> Maybe T.Text
argumentNameFromGeneric names reg
  | PPC.PPC_GP (PPC.GPR n) <- reg
  , n >= 3 && n <= 10 = names ^? L.traversed . L.index (fromIntegral n - 3)
  | otherwise = Nothing

-- | All of the PPC registers in use in macaw are user-level registers (except
-- for PC, but we want to show that anyway)
display :: PPC.PPCReg v tp -> PA.RegisterDisplay String
display = PA.Normal <$> PC.showF

gpr :: (1 <= SP.AddrWidth v) => Word8 -> PPC.PPCReg v (MT.BVType (SP.AddrWidth v))
gpr = PPC.PPC_GP . PPC.GPR

handleSystemCall :: (1 <= SP.AddrWidth v, SP.KnownVariant v, MM.MemWidth (SP.AddrWidth v)) =>
  PVE.ExternalDomain PVE.SystemCall (PPC.AnyPPC v)
handleSystemCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = PER.fromList $
        [ (Some (gpr 0), WI.truePred sym) -- syscall number
        , (Some (gpr 3), WI.truePred sym)
        , (Some (gpr 4), WI.truePred sym)
        , (Some (gpr 5), WI.truePred sym)
        , (Some (gpr 6), WI.truePred sym)
        , (Some (gpr 7), WI.truePred sym)
        , (Some (gpr 8), WI.truePred sym)
        , (Some (gpr 9), WI.truePred sym) -- FIXME: Only on PPC32
        ]
  return $ (PD.universalDomain sym){ PED.eqDomainRegisters = regDomain }

-- | PowerPC passes arguments in r3-r10
--
-- FIXME: This does not yet account for floating point registers
handleExternalCall :: (1 <= SP.AddrWidth v, SP.KnownVariant v, MM.MemWidth (SP.AddrWidth v)) =>
  PVE.ExternalDomain PVE.ExternalCall (PPC.AnyPPC v)
handleExternalCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = PER.fromList $
        [ (Some (gpr 3), WI.truePred sym)
        , (Some (gpr 4), WI.truePred sym)
        , (Some (gpr 5), WI.truePred sym)
        , (Some (gpr 6), WI.truePred sym)
        , (Some (gpr 7), WI.truePred sym)
        , (Some (gpr 8), WI.truePred sym)
        , (Some (gpr 9), WI.truePred sym)
        , (Some (gpr 10), WI.truePred sym)
        ]
  return $ (PD.universalDomain sym) { PED.eqDomainRegisters = regDomain }

argumentMapping :: (1 <= SP.AddrWidth v) => PVO.ArgumentMapping (PPC.AnyPPC v)
argumentMapping = undefined


specializedBufferWrite :: forall arch v. (arch ~ PPC.AnyPPC v, 16 <= SP.AddrWidth v, MS.SymArchConstraints arch) => PA.StubOverride arch
specializedBufferWrite = 
    PA.mkEventOverride "CFE_SB_TransmitBuffer" mkEvent 0x30 (gpr 3) (gpr 3)
    where
      mkEvent :: CB.IsSymInterface sym => sym -> PMT.MemChunk sym (MC.ArchAddrWidth arch) -> IO (WI.SymBV sym (MC.ArchAddrWidth arch))
      mkEvent sym chunk = do
        let ptrW = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)
        let concreteExpect :: Integer = 0x300
        offset <- WI.bvLit sym ptrW (BVS.mkBV ptrW 4)
        let bytes = WI.knownNat @2
        PMT.BytesBV _ bv <- PMT.readFromChunk sym MC.BigEndian chunk offset bytes
        let bits = WI.bvWidth bv
        expect_value <- WI.bvLit sym bits (BVS.mkBV bits concreteExpect)
        is_expect <- WI.isEq sym bv expect_value
        zero <- WI.bvLit sym ptrW (BVS.zero ptrW)
        expect_value' <- WI.bvLit sym ptrW (BVS.mkBV ptrW concreteExpect)
        -- if we the bytes are as expected then return them
        -- otherise, return zero
        WI.baseTypeIte sym is_expect expect_value' zero

-- FIXME: flags to make it equal?
specializeSocketRead :: forall arch v. (Typeable arch, arch ~ PPC.AnyPPC v, 16 <= SP.AddrWidth v, MS.SymArchConstraints arch) => PA.StubOverride arch
specializeSocketRead = 
    PA.mkReadOverride "OS_SocketRecvFrom" (PPa.PatchPairSingle PB.PatchedRepr (Const f)) addrs lengths (gpr 3) (gpr 4) (gpr 5) (gpr 3)
    where
      addrs :: PPa.PatchPairC (Maybe (PA.MemLocation (MC.ArchAddrWidth arch)))
      addrs = PPa.PatchPairC (Just (PA.MemIndPointer (PA.MemPointer 0x00013044) 0x7c)) (Just (PA.MemIndPointer (PA.MemPointer 0x00013044) 0x7c))

      lengths :: PPa.PatchPairC (Maybe (MC.MemWord (MC.ArchAddrWidth arch)))
      lengths = PPa.PatchPairC (Just 0x30) (Just 0x30)

      f :: PA.MemChunkModify (MC.ArchAddrWidth arch)
      f = PA.modifyConcreteChunk MC.BigEndian WI.knownNat (0x300 :: Integer) 2 4

-- FIXME: clagged directly from ARM, registers may not be correct
stubOverrides :: (Typeable (PPC.AnyPPC v), MS.SymArchConstraints (PPC.AnyPPC v), 1 <= SP.AddrWidth v, 16 <= SP.AddrWidth v) => PA.ArchStubOverrides (PPC.AnyPPC v)
stubOverrides = PA.ArchStubOverrides (PA.mkDefaultStubOverride "__pate_stub" r3 ) $ \fs ->
  lookup (PBl.fnSymBase fs) override_list
  where
    override_list =
      [ ("malloc", PA.mkMallocOverride r3 r3)
      -- FIXME: arguments are interpreted differently for calloc
      , ("calloc", PA.mkMallocOverride r3 r3)
      -- FIXME: arguments are interpreted differently for reallolc
      , ("realloc", PA.mkMallocOverride r3 r3)
      , ("clock", PA.mkClockOverride r3)
      , ("write", PA.mkWriteOverride "write" r3 r4 r5 r3)
      -- FIXME: fixup arguments for fwrite
      , ("fwrite", PA.mkWriteOverride "fwrite" r3 r4 r5 r3)
      , ("printf", PA.mkObservableOverride "printf" r3 r4)
      
      -- FIXME: added for relaySAT challenge problem
      , ("CFE_SB_AllocateMessageBuffer", PA.mkMallocOverride' (Just (PA.MemIndPointer (PA.MemPointer 0x00013044) 0x7c)) r3 r3)
      , ("OS_SocketRecvFrom", specializeSocketRead)
      , ("CFE_SB_TransmitBuffer", specializedBufferWrite)
      -- END relaySAT

      -- FIXME: default stubs below here
      ] ++
      (map mkDefault $
        [ "getopt"
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
        , "puts"
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
        , "memcpy" -- FIXME: needs implementation
        , "__floatsidf" -- FIXME: lets us ignore float operations
        , "__extendsfdf2" -- FIXME: lets us ignore float operations 
        , "__gtdf2" -- FIXME: lets us ignore float operations
        , "ceil" -- FIXME: more floating point hacks
        , "FLEXCAN_DRV_Send" -- FIXME: IO stub
        ]
      ) ++
      (map mkNOPStub $ [
          "console_debugln"
        , "console_debugf"
        , "console_printf" -- FIXME: observable?
        , "console_printf_data" -- FIXME: observable?
        , "console_println" -- FIXME: observable?
        , "console_error" -- FIXME: observable?
        , "console_print" -- FIXME: observable?
        , "CFE_EVS_SendEvent"
        , "CFE_ES_PerfLogAdd"
        ])

    mkNOPStub nm = (nm, PA.mkNOPStub nm)
    mkDefault nm = (nm, PA.mkDefaultStubOverride nm r3)

    -- r0 = gpr 0
    -- r1 = gpr 1
    -- r2 = gpr 2
    r3 = gpr 3
    r4 = gpr 4
    r5 = gpr 5
    -- r6 = gpr 6
    -- r7 = gpr 7


instance MCS.HasArchTermEndCase (PPC.PPCTermStmt v) where
  archTermCase = \case
    PPC.PPCSyscall -> MCS.MacawBlockEndCall
    _ -> MCS.MacawBlockEndArch

-- | PLT stub information for PPC32 relocation types.
--
-- WARNING: These heuristics are based on the layout of a particular demo
-- binary's @.plt@ section, and as such, these heuristics are unlikely to work
-- for other binaries. In particular, @gcc@ generates @.plt@ sections without
-- a function named @.plt@, and it generates stubs that are 4 bytes in size,
-- so these heuristics won't work at all for ordinary @gcc@-compiled binaries.
ppc32PLTStubInfo :: PLT.PLTStubInfo EEP.PPC32_RelocationType
ppc32PLTStubInfo = PLT.PLTStubInfo
  { PLT.pltFunSize     = 72
  , PLT.pltStubSize    = 8
  , PLT.pltGotStubSize = error "Unexpected .plt.got section in PPC32 binary"
  }

archLoader :: PA.ArchLoader PEE.LoadError
archLoader = PA.ArchLoader $ \_pd em origHdr patchedHdr ->
  case (em, EEP.headerClass (EEP.header origHdr)) of
    (EEP.EM_PPC, EEP.ELFCLASS32) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = handleSystemCall
                                 , PA.validArchFunctionDomain = handleExternalCall
                                 , PA.validArchDedicatedRegisters = ppc32HasDedicatedRegister
                                 , PA.validArchArgumentMapping = argumentMapping
                                 , PA.validArchOrigExtraSymbols =
                                      PLT.pltStubSymbols' ppc32PLTStubInfo MML.defaultLoadOptions origHdr
                                 , PA.validArchPatchedExtraSymbols =
                                      PLT.pltStubSymbols' ppc32PLTStubInfo MML.defaultLoadOptions patchedHdr
                                 , PA.validArchStubOverrides = stubOverrides
                                 , PA.validArchInitAbs = PBl.defaultMkInitialAbsState
                                 , PA.validArchExtractPrecond = \_ _ _ -> Nothing
                                 }
      in Right (Some (PA.SomeValidArch vad))
    (EEP.EM_PPC64, _) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = handleSystemCall
                                 , PA.validArchFunctionDomain = handleExternalCall
                                 , PA.validArchDedicatedRegisters = ppc64HasDedicatedRegister
                                 , PA.validArchArgumentMapping = argumentMapping
                                 , PA.validArchOrigExtraSymbols = mempty
                                 , PA.validArchPatchedExtraSymbols = mempty
                                 , PA.validArchStubOverrides = stubOverrides
                                 , PA.validArchInitAbs = PBl.defaultMkInitialAbsState
                                 , PA.validArchExtractPrecond = \_ _ _ -> Nothing
                                 }
      in Right (Some (PA.SomeValidArch vad))

    _ -> Left (PEE.UnsupportedArchitecture em)
