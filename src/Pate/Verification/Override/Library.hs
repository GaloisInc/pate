{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.Override.Library (
    overrides
  , ovMalloc
  , ovFree
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Parameterized.Context as Ctx
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
overrides
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym)
  => LCS.GlobalVar LCLM.Mem
  -> [PVO.SomeOverride arch sym]
overrides memVar = [ ovMalloc memVar
                   , ovFree memVar
                   ]

ovFree :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovFree memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "free"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCT.UnitRepr
                      , PVO.functionOverride = doFree memVar
                      }

doFree
  :: (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, LCB.IsSymInterface sym)
  => LCS.GlobalVar LCLM.Mem
  -> sym
  -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext rtp args ret ()
doFree memVar sym (Ctx.Empty Ctx.:> ptr) =
  LCSO.modifyGlobal memVar $ \mem -> liftIO $ do
    mem' <- LCLM.doFree sym mem (LCS.regValue ptr)
    return ((), mem')

ovMalloc :: (LCLM.HasPtrWidth w) => LCS.GlobalVar LCLM.Mem -> PVO.SomeOverride arch sym
ovMalloc memVar = PVO.SomeOverride ov
  where
    ov = PVO.Override { PVO.functionName = "malloc"
                      , PVO.functionArgsRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionRetRepr = LCLM.LLVMPointerRepr ?ptrWidth
                      , PVO.functionOverride = doMalloc memVar
                      }

doMalloc
  :: (LCLM.HasPtrWidth w, LCB.IsSymInterface sym)
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
