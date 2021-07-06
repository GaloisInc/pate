{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.PPC (
    PPC.PPC64
  , PPC.PPC32
  , PPC.AnyPPC
  , handleSystemCall
  , handleExternalCall
  )
where

import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import           Data.Word ( Word8 )
import           GHC.TypeLits
import qualified What4.Interface as WI

import qualified Data.Macaw.PPC as PPC
import qualified Dismantle.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.Types as MT
import qualified SemMC.Architecture.PPC as SP

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Verification.ExternalCall as PVE

instance PA.ArchConstraints PPC.PPC64 where
  binArchInfo = PPC.ppc64_linux_info

instance PA.ArchConstraints PPC.PPC32 where
  binArchInfo = PPC.ppc32_linux_info

instance PA.HasTOCReg PPC.PPC64 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PA.HasTOCReg PPC.PPC32 where
  toc_reg = PPC.PPC_GP (PPC.GPR 2)

instance PA.ValidArch PPC.PPC32 where
  tocProof = Just PA.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False

instance PA.ValidArch PPC.PPC64 where
  tocProof = Just PA.HasTOCDict
  rawBVReg r = case r of
    PPC.PPC_FR _ -> True
    PPC.PPC_CR -> True
    PPC.PPC_FPSCR -> True
    PPC.PPC_VSCR -> True
    PPC.PPC_XER -> True
    _ -> False

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
