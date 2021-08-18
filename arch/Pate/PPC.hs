{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC (
    PPC.PPC64
  , PPC.PPC32
  , PPC.AnyPPC
  , handleSystemCall
  , handleExternalCall
  , ppc64HasDedicatedRegister
  , ppc32HasDedicatedRegister
  )
where

import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as CMC
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Void ( Void, absurd )
import           Data.Word ( Word8 )
import           GHC.TypeLits
import qualified What4.Interface as WI

import qualified Data.Macaw.BinaryLoader.PPC as TOC
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Word.Indexed as W
import qualified Dismantle.PPC as PPC
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.PPC as SP

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Event as PE
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.ExternalCall as PVE

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
  :: PMC.EquivalenceContext sym PPC.PPC64
  -> PB.WhichBinaryRepr bin
  -> IO (W.W 64)
getCurrentTOC ctx binRepr = do
  PPa.PatchPair (PE.Blocks _ (pblkO:_)) (PE.Blocks _ (pblkP:_)) <- PD.getBlocks' ctx (ctx ^. PMC.currentFunc)
  let (toc, addr) = case binRepr of
        PB.OriginalRepr -> (TOC.getTOC (PMC.binary (PMC.originalCtx ctx)), MD.pblockAddr pblkO)
        PB.PatchedRepr -> (TOC.getTOC (PMC.binary (PMC.rewrittenCtx ctx)), MD.pblockAddr pblkP)
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
  -> IO (PS.AssumptionFrame sym)
ppc64DedicatedRegisterFrame sym ctx binRepr entry dr =
  case dr of
    RegTOC -> do
      tocW <- getCurrentTOC ctx binRepr
      tocBV <- WI.bvLit sym PN.knownNat (BVS.mkBV PN.knownNat (W.unW tocW))
      let targetTOC = CLM.LLVMPointer (PMC.globalRegion ctx) tocBV
      PS.macawRegBinding sym entry (PSR.ptrToEntry targetTOC)

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

instance PA.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info

instance PA.ArchConstraints PPC.PPC32 where
  binArchInfo = PPC.ppc32_linux_info

instance PA.ValidArch PPC.PPC32 where
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
  displayRegister = display

instance PA.ValidArch PPC.PPC64 where
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False
  displayRegister = display

-- | All of the PPC registers in use in macaw are user-level registers (except
-- for PC, but we want to show that anyway)
display :: PPC.PPCReg v tp -> PA.RegisterDisplay String
display = PA.Normal <$> PC.showF

gpr :: (1 <= SP.AddrWidth v) => Word8 -> PPC.PPCReg v (MT.BVType (SP.AddrWidth v))
gpr = PPC.PPC_GP . PPC.GPR

handleSystemCall :: (1 <= SP.AddrWidth v) => PVE.ExternalDomain PVE.SystemCall (PPC.AnyPPC v)
handleSystemCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = Map.fromList [ (Some (gpr 0), WI.truePred sym) -- syscall number
                               , (Some (gpr 3), WI.truePred sym)
                               , (Some (gpr 4), WI.truePred sym)
                               , (Some (gpr 5), WI.truePred sym)
                               , (Some (gpr 6), WI.truePred sym)
                               , (Some (gpr 7), WI.truePred sym)
                               , (Some (gpr 8), WI.truePred sym)
                               , (Some (gpr 9), WI.truePred sym) -- FIXME: Only on PPC32
                               ]
  return $ PES.StatePred { PES.predRegs = regDomain
                         , PES.predStack = PEM.memPredTrue sym
                         , PES.predMem = PEM.memPredTrue sym
                         }

-- | PowerPC passes arguments in r3-r10
--
-- FIXME: This does not yet account for floating point registers
handleExternalCall :: (1 <= SP.AddrWidth v) => PVE.ExternalDomain PVE.ExternalCall (PPC.AnyPPC v)
handleExternalCall = PVE.ExternalDomain $ \sym -> do
  let regDomain = Map.fromList [ (Some (gpr 3), WI.truePred sym)
                               , (Some (gpr 4), WI.truePred sym)
                               , (Some (gpr 5), WI.truePred sym)
                               , (Some (gpr 6), WI.truePred sym)
                               , (Some (gpr 7), WI.truePred sym)
                               , (Some (gpr 8), WI.truePred sym)
                               , (Some (gpr 9), WI.truePred sym)
                               , (Some (gpr 10), WI.truePred sym)
                               ]
  return $ PES.StatePred { PES.predRegs = regDomain
                         , PES.predStack = PEM.memPredTrue sym
                         , PES.predMem = PEM.memPredTrue sym
                         }
