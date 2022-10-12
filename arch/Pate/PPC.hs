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
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Event as PE
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Override as PVO

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
getCurrentTOC ctx binRepr = do
  PE.Blocks _ _ (pblk:_) <- PPa.getPair' binRepr <$> PD.getBlocks' ctx (ctx ^. PMC.currentFunc)
  let
    toc = TOC.getTOC (PMC.binary $ PPa.getPair' binRepr (PMC.binCtxs ctx))
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

instance PA.ValidArch PPC.PPC32 where
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
  displayRegister = display
  argumentNameFrom = argumentNameFromGeneric
  binArchInfo = const PPC.ppc32_linux_info
  discoveryRegister = const False

instance PA.ValidArch PPC.PPC64 where
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
  return $ PED.EquivalenceDomain { PED.eqDomainRegisters = regDomain
                                 , PED.eqDomainStackMemory = PEM.universal sym
                                 , PED.eqDomainGlobalMemory = PEM.universal sym
                                 }

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
  return $ PED.EquivalenceDomain { PED.eqDomainRegisters = regDomain
                                 , PED.eqDomainStackMemory = PEM.universal sym
                                 , PED.eqDomainGlobalMemory = PEM.universal sym
                                 }

argumentMapping :: (1 <= SP.AddrWidth v) => PVO.ArgumentMapping (PPC.AnyPPC v)
argumentMapping = undefined

stubOverrides :: (MS.SymArchConstraints (PPC.AnyPPC v), 1 <= SP.AddrWidth v, 16 <= SP.AddrWidth v) => PA.ArchStubOverrides (PPC.AnyPPC v)
stubOverrides = PA.ArchStubOverrides (PA.mkDefaultStubOverride r0) $
  Map.fromList
    [ (BSC.pack "malloc", PA.mkMallocOverride r0 r0)
    , (BSC.pack "clock", PA.mkClockOverride r0)  ]
  where
    r0 = gpr 0

instance MCS.HasArchTermEndCase (PPC.PPCTermStmt v) where
  archTermCase = \case
    PPC.PPCSyscall -> MCS.MacawBlockEndCall
    _ -> MCS.MacawBlockEndArch


archLoader :: PA.ArchLoader PEE.LoadError
archLoader = PA.ArchLoader $ \em origHdr _patchedHdr ->
  case (em, EEP.headerClass (EEP.header origHdr)) of
    (EEP.EM_PPC, _) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = handleSystemCall
                                 , PA.validArchFunctionDomain = handleExternalCall
                                 , PA.validArchDedicatedRegisters = ppc32HasDedicatedRegister
                                 , PA.validArchArgumentMapping = argumentMapping
                                 , PA.validArchOrigExtraSymbols = mempty
                                 , PA.validArchPatchedExtraSymbols = mempty
                                 , PA.validArchStubOverrides = stubOverrides
                                 , PA.validArchInitAbs = PBl.defaultMkInitialAbsState
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
                                 }
      in Right (Some (PA.SomeValidArch vad))

    _ -> Left (PEE.UnsupportedArchitecture em)
