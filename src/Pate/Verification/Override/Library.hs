{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Pate.Verification.Override.Library (
    OverrideConfig(..)
  , overrides
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
import qualified What4.Protocol.Online as WPO

import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.Types as LCT

import qualified Pate.Verification.Concretize as PVC
import qualified Pate.Verification.Override as PVO

-- | Data necessary to fully instantiate the overrides
data OverrideConfig sym w =
  OverrideConfig { ocMemVar :: LCS.GlobalVar LCLM.Mem
                 -- ^ The Crucible global variable corresponding to the memory
                 -- model implementation
                 , ocPointerMap :: DMSM.MemPtrTable sym w
                 }

-- | All overrides defined for the inline-callee symbolic execution phase
--
-- Note that all of the overrides in this module use unadorned names.  Our
-- symbols for PLT stubs have more complex names (e.g., @malloc\@plt@). The
-- logic to ensure that these overrides can be applied both for unadorned
-- symbols and PLT stubs is handled when the overrides are registered.
overrides
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> [PVO.SomeOverride arch sym]
overrides ovCfg = [ ovMalloc ovCfg
                   , ovCalloc ovCfg
                   , ovFree ovCfg
                   , ovMemcpy ovCfg
                   , ovMemcpyChk ovCfg
                   , ovMemset ovCfg
                   , ovMemsetChk ovCfg
                   , ovPerror
                   , ovStackChkFail
                   , ovFwrite
                   , ovAbort
                   ]

ovFree
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions)
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovFree ovCfg = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "free"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCT.UnitRepr
                      , PVO.functionOverride = doFree (ocMemVar ovCfg)
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

ovMalloc
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions)
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovMalloc ovCfg = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "malloc"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMalloc (ocMemVar ovCfg)
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
    (ptr, mem') <- LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable display mem sz LCLD.noAlignment
    return (ptr, mem')

ovCalloc
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions)
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovCalloc ovCfg = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "calloc"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doCalloc (ocMemVar ovCfg)
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

ovMemcpy
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovMemcpy ovCfg = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "memcpy"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMemcpy ovCfg
                      }

-- A checked memcpy that takes an additional destlen parameter
--
-- Note that this override does *not* perform the check explicitly and just
-- reuses the underlying memcpy; the memory model will flag memory errors.
ovMemcpyChk
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovMemcpyChk ovCfg =
  case ovMemcpy ovCfg of
    PVO.SomeOverride ov -> PVO.SomeOverride (ov { PVO.functionName = "__memcpy_chk" })

doMemcpy
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doMemcpy ovCfg sym (Ctx.Empty Ctx.:> (LCS.regValue -> dest) Ctx.:> (LCS.regValue -> src) Ctx.:> (LCS.regValue -> nBytes)) =
  LCSO.modifyGlobal (ocMemVar ovCfg) $ \mem -> liftIO $ do
    let mapPtr = DMSM.mapRegionPointers (ocPointerMap ovCfg) sym mem

    destPtr <- mapPtr (LCLM.llvmPointerBlock dest) (LCLM.llvmPointerOffset dest)
    srcPtr <- mapPtr (LCLM.llvmPointerBlock src) (LCLM.llvmPointerOffset src)

    destPtr' <- PVC.resolveSingletonPointer sym destPtr
    srcPtr' <- PVC.resolveSingletonPointer sym srcPtr

    nBytesBV <- LCLM.projectLLVM_bv sym nBytes

    mem' <- LCLM.doMemcpy sym ?ptrWidth mem False destPtr' srcPtr' nBytesBV
    return (destPtr', mem')

ovMemset
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovMemset ovCfg = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "memset"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                                         Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                                                         Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMemset ovCfg
                      }

ovMemsetChk
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> PVO.SomeOverride arch sym
ovMemsetChk ovCfg =
  case ovMemset ovCfg of
    PVO.SomeOverride ov -> PVO.SomeOverride (ov { PVO.functionName = "__memset_chk" })


doMemset
  :: ( LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     )
  => OverrideConfig sym w
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCLM.LLVMPointerType 32 Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
doMemset ovCfg sym (Ctx.Empty Ctx.:> (LCS.regValue -> dest) Ctx.:> (LCS.regValue -> val) Ctx.:> (LCS.regValue -> nBytes)) =
  LCSO.modifyGlobal (ocMemVar ovCfg) $ \mem -> liftIO $ do
    let mapPtr = DMSM.mapRegionPointers (ocPointerMap ovCfg) sym mem

    destPtr <- mapPtr (LCLM.llvmPointerBlock dest) (LCLM.llvmPointerOffset dest)
    destPtr' <- PVC.resolveSingletonPointer sym destPtr

    valBV <- LCLM.projectLLVM_bv sym val
    fillByteBV <- WI.bvTrunc sym (PN.knownNat @8) valBV

    nBytesBV <- LCLM.projectLLVM_bv sym nBytes
    mem' <- LCLM.doMemset sym ?ptrWidth mem destPtr' fillByteBV nBytesBV
    return (destPtr', mem')

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
