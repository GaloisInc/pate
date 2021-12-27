{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-- | A crucible extension for macaw IR using the trace memory model
--
-- This high-level interface is used during symbolic execution to implement the
-- trace-based machine code memory model.  This layer of code manages an
-- instance of the 'TraceMemoryModel' data structure implemented by
-- Pate.Memory.Trace.MemTrace module.  /This/ layer of code implements the
-- policy for what operations are valid and what they mean, while the
-- 'TraceMemoryModel' is the low-level memory log trace data structure.
module Pate.Memory.Trace (
  macawTraceExtensions
  ) where

import           Control.Lens ( (^.), (&), (%~) )
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )
import qualified What4.Interface as WI

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Data.Macaw.Symbolic.MemOps as DMSM
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Pate.Memory.Trace.MemTrace as PMTM
import qualified Pate.Memory.Trace.Undefined as PMTU
import qualified Pate.Panic as PP

doPtrToBits
  :: ( LCB.IsSymInterface sym
     , 1 <= w
     )
  => PMTU.UndefinedPtrOps sym
  -> sym
  -> LCLM.LLVMPtr sym w
  -> IO (WI.SymBV sym w)
doPtrToBits undefPtrOps sym ptr@(LCLM.LLVMPointer base offset) =
  case WI.asNat base of
    Just 0 -> return offset
    _ -> do
      cond <- WI.natEq sym base =<< WI.natLit sym 0
      case WI.asConstantPred cond of
        Just True -> return offset
        _ -> do
          LCB.assert sym cond (LCS.AssertFailureSimError "doPtrToBits" "Pointer region is not zero")
          undef <- PMTU.undefPtrOff undefPtrOps sym ptr
          WI.bvIte sym cond offset undef

-- | The custom evaluation function for macaw expressions
--
-- We only need to override the pointer to bitvector operation, as we need
-- control over validity side conditions.
evalMacawExpr
  :: ( LCB.IsSymInterface sym
     )
  => PMTU.UndefinedPtrOps sym
  -> sym
  -> LCS.IntrinsicTypes sym
  -> (Int -> String -> IO ())
  -- ^ Log function for Crucible (unused)
  -> LCSE.CrucibleState p sym ext rtp blocks r ctx
  -> (forall utp . f utp -> IO (LCS.RegValue sym utp))
  -- ^ The function that converts from a macaw expr to a crucible expr
  -> DMS.MacawExprExtension arch f tp
  -> IO (LCS.RegValue sym tp)
evalMacawExpr undefPtrOps sym intrinsics logFn crucState f expr =
  case expr of
    DMS.PtrToBits _w x -> doPtrToBits undefPtrOps sym =<< f x
    _ -> DMS.evalMacawExprExtension sym intrinsics logFn crucState f expr

getGlobalVar
  :: (HasCallStack)
  => LCS.CrucibleState s sym ext rtp blocks r ctx
  -> LCS.GlobalVar mem
  -> IO (LCS.RegValue sym mem)
getGlobalVar cst gv =
  case LCSG.lookupGlobal gv (cst ^. LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals) of
    Just val -> return val
    Nothing -> PP.panic PP.MemoryModel "getGlobalVar" ["Missing expected global variable: " ++ show gv]

setGlobalVar
  :: LCS.CrucibleState s sym ext rtp blocks r ctx
  -> LCS.GlobalVar mem
  -> LCS.RegValue sym mem
  -> LCS.CrucibleState s sym ext rtp blocks r ctx
setGlobalVar cst gv val = cst & LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals %~ LCSG.insertGlobal gv val

-- | The custom evaluation function for macaw statements
--
-- We need to override most of these, but especially the memory model value
execMacawStmt
  :: ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , HasCallStack
     , mem ~ PMTM.MemoryTrace arch
     )
  => DMS.MacawArchEvalFn sym mem arch
  -> PMTU.UndefinedPtrOps sym
  -> LCS.GlobalVar mem
  -> DMS.GlobalMap sym mem (DMC.ArchAddrWidth arch)
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
execMacawStmt (DMSB.MacawArchEvalFn archStmtFn) undefPtrOps memVar globalMap stmt crucState = do
  let sym = crucState ^. LCSE.stateSymInterface
  case stmt of
    DMS.MacawReadMem _addrWidth memRepr (LCS.regValue -> addr) -> do
      memImpl0 <- getGlobalVar crucState memVar
      -- NOTE: There are no provisions here for resolving constants or pointers
      -- constructed from global values (e.g., properly building pointers on ARM
      -- where the real address is computed as an offset from the PC using an
      -- offset table embedded in the .text section.
      --
      -- This is really important to ensure that multiple references to the same
      -- memory location in a slice are consistent.
      --
      -- Note that, to do that, we need to populate the read-only portion of
      -- memory with initial contents
      (res, memImpl1) <- PMTM.readMemory sym addr memRepr memImpl0
      return (res, setGlobalVar crucState memVar memImpl1)

    DMS.MacawCondReadMem _addrWidth memRepr (LCS.regValue -> cond) (LCS.regValue -> addr) (LCS.regValue -> def) -> do
      memImpl0 <- getGlobalVar crucState memVar
      (res, memImpl1) <- PMTM.readMemoryConditional sym cond addr memRepr def memImpl0
      return (res, setGlobalVar crucState memVar memImpl1)

    DMS.MacawWriteMem _addrWidth memRepr (LCS.regValue -> addr) (LCS.regValue -> value) -> do
      memImpl0 <- getGlobalVar crucState memVar
      memImpl1 <- PMTM.writeMemory sym addr memRepr value memImpl0
      return ((), setGlobalVar crucState memVar memImpl1)

    DMS.MacawCondWriteMem _addrWidth memRepr (LCS.regValue -> cond) (LCS.regValue -> addr) (LCS.regValue -> val) -> do
      memImpl0 <- getGlobalVar crucState memVar
      memImpl1 <- PMTM.writeMemoryConditional sym cond addr memRepr val memImpl0
      return ((), setGlobalVar crucState memVar memImpl1)

    DMS.MacawGlobalPtr _w addr -> DMSM.doGetGlobal crucState memVar globalMap addr

    DMS.PtrEq _w (LCS.regValue -> (LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> (LCLM.LLVMPointer yRegion yOffset)) -> do
      regionEq <- WI.natEq sym xRegion yRegion
      offsetEq <- WI.bvEq sym xOffset yOffset
      p <- WI.andPred sym regionEq offsetEq
      return (p, crucState)

    DMS.PtrLeq _w (LCS.regValue -> (LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> (LCLM.LLVMPointer yRegion yOffset)) -> do
      p <- WI.bvUle sym xOffset yOffset
      return (p, crucState)

    DMS.PtrLt _w (LCS.regValue -> (LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> (LCLM.LLVMPointer yRegion yOffset)) -> do
      p <- WI.bvUlt sym xOffset yOffset
      return (p, crucState)

    DMS.PtrMux _w (LCS.regValue -> cond) (LCS.regValue -> x) (LCS.regValue -> y) -> do
      ptr <- LCLM.muxLLVMPtr sym cond x y
      return (ptr, crucState)

    DMS.PtrAdd _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
      isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
      region <- WI.natIte sym isXRegionZero yRegion xRegion
      offset <- WI.bvAdd sym xOffset yOffset

      return (LCLM.LLVMPointer region offset, crucState)

    DMS.PtrSub _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
      isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
      region <- WI.natIte sym isXRegionZero yRegion xRegion
      offset <- WI.bvSub sym xOffset yOffset

      return (LCLM.LLVMPointer region offset, crucState)

    DMS.PtrAnd _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
      isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
      region <- WI.natIte sym isXRegionZero yRegion xRegion
      offset <- WI.bvAndBits sym xOffset yOffset

      return (LCLM.LLVMPointer region offset, crucState)

    DMS.PtrXor _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
      isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
      region <- WI.natIte sym isXRegionZero yRegion xRegion
      offset <- WI.bvXorBits sym xOffset yOffset

      return (LCLM.LLVMPointer region offset, crucState)

    DMS.PtrTrunc w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
      offset' <- WI.bvTrunc sym w offset
      return (LCLM.LLVMPointer region offset', crucState)

    DMS.PtrUExt w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
      offset' <- WI.bvZext sym w offset
      return (LCLM.LLVMPointer region offset', crucState)

    DMS.MacawArchStmtExtension archStmt -> archStmtFn memVar globalMap archStmt crucState

    DMS.MacawArchStateUpdate {} -> return ((), crucState)
    DMS.MacawInstructionStart {} -> return ((), crucState)

    DMS.MacawFreshSymbolic {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["Fresh values are not supported in the compositional verification extension"]
    DMS.MacawLookupFunctionHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["Function calls are not supported in the compositional verification extension"]
    DMS.MacawLookupSyscallHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["System calls are not supported in the compositional verification extension"]

macawTraceExtensions
  :: ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , HasCallStack
     , mem ~ PMTM.MemoryTrace arch
     )
  => DMS.MacawArchEvalFn sym mem arch
  -> PMTU.UndefinedPtrOps sym
  -> LCS.GlobalVar mem
  -> DMS.GlobalMap sym mem (DMC.ArchAddrWidth arch)
  -> LCSE.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
macawTraceExtensions archEval undefPtrOps memVar globalMap =
  LCSE.ExtensionImpl { LCSE.extensionEval = evalMacawExpr undefPtrOps
                     , LCSE.extensionExec = execMacawStmt archEval undefPtrOps memVar globalMap
                     }
