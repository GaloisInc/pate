{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
import qualified Data.Parameterized.TraversableFC as FC
import           GHC.Stack ( HasCallStack )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Data.Macaw.Symbolic.MemOps as DMSM
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Pate.Memory.Trace.MemTrace as PMTM
import qualified Pate.Memory.Trace.ValidityPolicy as PMTV
import qualified Pate.Panic as PP

-- | The custom evaluation function for macaw expressions
--
-- We only need to override the pointer to bitvector operation, as we need
-- control over validity side conditions.
evalMacawExpr
  :: forall f sym arch tp p ext rtp blocks r ctx
   . ( LCB.IsSymInterface sym
     )
  => PMTV.ValidityPolicy sym arch
  -> sym
  -> LCS.IntrinsicTypes sym
  -> (Int -> String -> IO ())
  -- ^ Log function for Crucible (unused)
  -> LCSE.CrucibleState p sym ext rtp blocks r ctx
  -> (forall utp . f utp -> IO (LCS.RegValue sym utp))
  -- ^ The function that converts from a macaw expr to a crucible expr
  -> DMS.MacawExprExtension arch f tp
  -> IO (LCS.RegValue sym tp)
evalMacawExpr validityPolicy sym intrinsics logFn crucState f expr = do
  let f' :: forall ytp . f ytp -> IO (LCS.RegValue' sym ytp)
      f' v = LCS.RV <$> f v
  expr' <- FC.traverseFC f' expr
  case expr' of
    DMS.PtrToBits _w _ptr -> PMTV.validateExpression validityPolicy sym expr'
    _ ->
      -- NOTE: We don't use the validated expressions for these default cases
      -- since the types aren't set up properly.  If validation is required for
      -- these, we need to handle them explicitly.
      DMS.evalMacawExprExtension sym intrinsics logFn crucState f expr

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
  -> PMTV.ValidityPolicy sym arch
  -> LCS.GlobalVar mem
  -> DMS.GlobalMap sym mem (DMC.ArchAddrWidth arch)
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
execMacawStmt (DMSB.MacawArchEvalFn archStmtFn) validityPolicy memVar globalMap stmt crucState = do
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

    DMS.PtrMux _w _ _ _ ->
      -- NOTE: There don't need to be any validity checks for pointer muxes
      (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrEq _w _ _ ->
      -- NOTE: There don't need to be any validity checks for pointer equality either
      (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrLeq _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrLt _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrAdd _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrSub _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrAnd _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrXor _w _ _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrTrunc _w _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt
    DMS.PtrUExt _w _ -> (, crucState) <$> PMTV.validateStatement validityPolicy sym stmt

    DMS.MacawArchStmtExtension archStmt -> archStmtFn memVar globalMap archStmt crucState

    DMS.MacawArchStateUpdate {} -> return ((), crucState)
    DMS.MacawInstructionStart {} -> return ((), crucState)

    DMS.MacawFreshSymbolic {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["Fresh values are not supported in the compositional verification extension"]
    DMS.MacawLookupFunctionHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["Function calls are not supported in the compositional verification extension"]
    DMS.MacawLookupSyscallHandle {} ->
      PP.panic PP.MemoryModel "execMacawStmt" ["System calls are not supported in the compositional verification extension"]

-- | A Crucible extension for symbolically executing machine code using the
-- trace-based memory model
--
-- The major configuration option is the 'PMTV.ValidityPolicy', which controls
-- how pointer operations are validated.  We want to experiment with these to
-- maximize efficiency while preserving soundness.
--
-- The intent is that we can use this configurability to run each symbolic
-- execution of a slice twice: once in "optimistic" mode where we generate side
-- conditions to check the validity of all pointer operations and again in
-- "conservative" mode to generate defensive terms that can be compared for
-- equi-undefinedness.  We can then arrange for the outer pate verifier to
-- attempt to prove all of the side conditions.  If it can prove them, it is
-- allowed to use the optimistic memory model.  Otherwise, it has to use the
-- results from the conservative one.
--
-- Ideally we would be able to maintain both the optimistic and conservative
-- interpretations of the memory state in the same memory model, but we can't
-- return two different values from the pointer operation interpreter (e.g.,
-- PtrAdd).
macawTraceExtensions
  :: ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , HasCallStack
     , mem ~ PMTM.MemoryTrace arch
     )
  => DMS.MacawArchEvalFn sym mem arch
  -> PMTV.ValidityPolicy sym arch
  -> LCS.GlobalVar mem
  -> DMS.GlobalMap sym mem (DMC.ArchAddrWidth arch)
  -> LCSE.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
macawTraceExtensions archEval validityPolicy memVar globalMap =
  LCSE.ExtensionImpl { LCSE.extensionEval = evalMacawExpr validityPolicy
                     , LCSE.extensionExec = execMacawStmt archEval validityPolicy memVar globalMap
                     }

{- Note [Optimistic Memory Model Design]

The optimistic memory model will return unadorned terms accompanied by a set of
validity assertions. Those assertions should be maintained in an IORef separate
from the normal assertion stack, as we don't want to check any of the validity
assertions that are generated as a side effect of symbolic execution.  The
allocator for the ValidityPolicy should be in IO and return an additional value:
a newtype wrapper around the IORef.  The interface should expose a function to
consume that value and:

1. Attempt to prove the side conditions
2. Report the failures if there were any

Note that we could also maintain a side mapping (via the Annotation mechanism)
that can flag which values the side conditions are for. It isn't obvious if we
need that.

If there are verification failures, the verifier should re-run the symbolic
execution with the conservative memory model that contains the elaborated terms.
Perhaps that could actually only provide elaborated terms for the terms that
actually failed. Note that it is likely to be the case that relating the values
across the two runs is probably not practical. In the worst case, we can just
use conservative values for all values in the slice. We can use the SMT solver
to attempt to resolve all of the muxes and prove them away.

We then need to duplicate some of the infrastructure (but maybe not all) to
implement a function from symbolic terms to the set of undefined behaviors that
they can exhibit, as those are annotated onto ground values.  It will probably
be a lot easier to use the annotation mechanism for that.

-}
