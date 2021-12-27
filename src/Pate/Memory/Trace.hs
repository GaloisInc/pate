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

import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
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
     )
  => DMS.MacawArchEvalFn sym (PMTM.MemoryTrace arch) arch
  -> PMTU.UndefinedPtrOps sym
  -> LCS.GlobalVar (PMTM.MemoryTrace arch)
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
execMacawStmt (DMSB.MacawArchEvalFn archStmtFn) undefPtrOps memVar stmt crucState =
  case stmt of
    DMS.MacawReadMem _addrWidth memRepr (LCS.regValue -> addr) -> do
      memImpl0 <- getGlobalVar crucState memVar
      let sym = crucState ^. LCSE.stateSymInterface
      (res, memImpl1) <- PMTM.readMemory sym addr memRepr memImpl0
      return (res, setGlobalVar crucState memVar memImpl1)

    DMS.MacawCondReadMem _addrWidth memRepr (LCS.regValue -> cond) (LCS.regValue -> addr) (LCS.regValue -> def) -> do
      memImpl0 <- getGlobalVar crucState memVar
      let sym = crucState ^. LCSE.stateSymInterface
      (res, memImpl1) <- PMTM.readMemoryConditional sym cond addr memRepr def memImpl0
      return (res, setGlobalVar crucState memVar memImpl1)


    DMS.MacawArchStateUpdate {} -> return ((), crucState)
    DMS.MacawInstructionStart {} -> return ((), crucState)
    DMS.MacawLookupFunctionHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["Function calls are not supported in the compositional verification extension"]
    DMS.MacawLookupSyscallHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["System calls are not supported in the compositional verification extension"]

macawTraceExtensions
  :: ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , HasCallStack
     )
  => DMS.MacawArchEvalFn sym (PMTM.MemoryTrace arch) arch
  -> PMTU.UndefinedPtrOps sym
  -> LCS.GlobalVar (PMTM.MemoryTrace arch)
  -> LCSE.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
macawTraceExtensions archEval undefPtrOps memVar =
  LCSE.ExtensionImpl { LCSE.extensionEval = evalMacawExpr undefPtrOps
                     , LCSE.extensionExec = execMacawStmt archEval undefPtrOps memVar
                     }
