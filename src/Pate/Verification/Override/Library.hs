{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.Override.Library (
    overrides
  , ovMalloc
  , ovCalloc
  , ovFree
  , ovMemcpy
  , ovMemcpyChk
  , ovMemset
  , ovMemsetChk
  , ovPerror
  , ovStackChkFail
  , ovFwrite
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.Types as LCT

import qualified Pate.Verification.Override as PVO

-- | All overrides defined for the inline-callee symbolic execution phase
--
-- Note that all of the overrides in this module use unadorned names.  Our
-- symbols for PLT stubs have more complex names (e.g., @malloc\@plt@). The
-- logic to ensure that these overrides can be applied both for unadorned
-- symbols and PLT stubs is handled when the overrides are registered.
overrides
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> [PVO.SomeOverride arch sym]
overrides memVar = [ ovMalloc memVar
                   , ovCalloc memVar
                   , ovFree memVar
                   , ovMemcpy memVar
                   , ovMemcpyChk memVar
                   , ovMemset memVar
                   , ovMemsetChk memVar
                   , ovPerror
                   , ovStackChkFail
                   , ovFwrite
                   , ovAbort
                   ]

ovFree :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovFree memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "free"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCT.UnitRepr
                      , PVO.functionOverride = doFree memVar
                      }

doFree
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret ()
doFree memVar sym (Ctx.Empty Ctx.:> ptr) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    mem' <- LCLM.doFree sym mem (LCS.regValue ptr)
    return ((), mem')

ovMalloc :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMalloc memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "malloc"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMalloc memVar
                      }

doMalloc
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doMalloc memVar sym (Ctx.Empty Ctx.:> nBytes) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    loc <- WP.plSourceLoc <$> WI.getCurrentProgramLoc sym
    let display = "<malloc at " ++ show loc ++ ">"
    sz <- LCLM.projectLLVM_bv sym (LCS.regValue nBytes)
    LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable display mem sz LCLD.noAlignment

ovCalloc :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovCalloc memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "calloc"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doCalloc memVar
                      }

doCalloc
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doCalloc memVar sym (Ctx.Empty Ctx.:> nmemb Ctx.:> size) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    loc <- WP.plSourceLoc <$> WI.getCurrentProgramLoc sym
    let display = "<calloc at " ++ show loc ++ ">"
    nmembBV <- LCLM.projectLLVM_bv sym (LCS.regValue nmemb)
    sizeBV <- LCLM.projectLLVM_bv sym (LCS.regValue size)
    nBytesBV <- WI.bvMul sym nmembBV sizeBV
    LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable display mem nBytesBV LCLD.noAlignment

ovMemcpy :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMemcpy memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "memcpy"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMemcpy memVar
                      }

-- A checked memcpy that takes an additional destlen parameter
--
-- Note that this override does *not* perform the check explicitly and just
-- reuses the underlying memcpy; the memory model will flag memory errors.
ovMemcpyChk :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMemcpyChk memVar =
  case ovMemcpy memVar of
    PVO.SomeOverride ov -> PVO.SomeOverride (ov { PVO.functionName = "__memcpy_chk" })

doMemcpy
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doMemcpy memVar sym (Ctx.Empty Ctx.:> dest Ctx.:> src Ctx.:> nBytes) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    nBytesBV <- LCLM.projectLLVM_bv sym (LCS.regValue nBytes)
    mem' <- LCLM.doMemcpy sym ?ptrWidth mem False (LCS.regValue dest) (LCS.regValue src) nBytesBV
    return (LCS.regValue dest, mem')

ovMemset :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMemset memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "memset"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMemset memVar
                      }

ovMemsetChk :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMemsetChk memVar =
  case ovMemset memVar of
    PVO.SomeOverride ov -> PVO.SomeOverride (ov { PVO.functionName = "__memset_chk" })


doMemset
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType 32 Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doMemset memVar sym (Ctx.Empty Ctx.:> dest Ctx.:> val Ctx.:> nBytes) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    nBytesBV <- LCLM.projectLLVM_bv sym (LCS.regValue nBytes)
    valBV <- LCLM.projectLLVM_bv sym (LCS.regValue val)
    fillByteBV <- WI.bvTrunc sym (PN.knownNat @8) valBV
    mem' <- LCLM.doMemset sym ?ptrWidth mem (LCS.regValue dest) fillByteBV nBytesBV
    return (LCS.regValue dest, mem')

-- | A no-op @fwrite@ that always indicates success by reporting that it wrote
-- the number of bytes requested
ovFwrite :: (LCLM.HasPtrWidth w) => PVO.SomeOverride arch sym
ovFwrite = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "fwrite"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doFwrite
                      }

doFwrite
  :: (LCLM.HasPtrWidth w, LCB.IsSymInterface sym)
  => sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doFwrite sym (Ctx.Empty Ctx.:> _ptr Ctx.:> size Ctx.:> nmemb Ctx.:> _) = liftIO $ do
  sizeBV <- LCLM.projectLLVM_bv sym (LCS.regValue size)
  nmembBV <- LCLM.projectLLVM_bv sym (LCS.regValue nmemb)
  LCLM.llvmPointer_bv sym =<< WI.bvMul sym sizeBV nmembBV

-- | An override that does nothing
--
-- It can be used on C functions with any argument lists, since it just declines
-- to parse any of them and makes no updates to the register state
noOp :: WF.FunctionName
     -> PVO.Override sym LCT.EmptyCtx ext LCT.UnitType
noOp name = PVO.Override { PVO.functionName = name
                         , PVO.functionArgsRepr = Ctx.Empty
                         , PVO.functionRetRepr = LCT.UnitRepr
                         , PVO.functionOverride = \_ _ -> return ()
                         }

ovPerror  :: PVO.SomeOverride arch sym
ovPerror = PVO.SomeOverride (noOp "perror")

ovStackChkFail :: PVO.SomeOverride arch sym
ovStackChkFail = PVO.SomeOverride (noOp "__stack_chk_fail")

-- | A no-op abort - we could change this to actually stop symbolic execution (or at least abort a branch)
ovAbort :: PVO.SomeOverride arch sym
ovAbort = PVO.SomeOverride (noOp "abort")
