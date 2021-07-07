{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-- | This module provides the interface to the symbolic execution engine used by the pate verifier
--
-- It performs all of the setup and extraction of results, along with logic for
-- converting superblocks (collections of basic blocks with no calls and no loop
-- backedges) into programs suitable for symbolic execution (i.e., Crucible
-- CFGs).
module Pate.Verification.SymbolicExecution (
  simulate
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import qualified Data.Functor.Compose as DFC
import qualified Data.List as DL
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as Set
import           Data.String ( fromString )
import           GHC.Stack ( HasCallStack )
import qualified System.IO as IO
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4L

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified Pate.Binary as PBi
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Memory.MemTrace as PMT
import           Pate.Monad
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR

-- | Return a Crucible run-time repr for the architecture-specific register file
archStructRepr :: forall sym arch. EquivM sym arch (CC.TypeRepr (MS.ArchRegStruct arch))
archStructRepr = do
  archFs <- archFuns
  return $ CC.StructRepr $ MS.crucArchRegTypes archFs

-- | Classify macaw blocks as terminal or non-terminal
--
-- Note that we consider any error blocks as terminal. We also consider any arch
-- term statement as terminal; those are usually some kind of
-- architecture-specific trap instruction.
isTerminalBlock :: MD.ParsedBlock arch ids -> Bool
isTerminalBlock pb = case MD.pblockTermStmt pb of
  MD.ParsedCall{} -> True
  MD.PLTStub{} -> True
  MD.ParsedJump{} -> False
  MD.ParsedBranch{} -> False
  MD.ParsedLookupTable{} -> False
  MD.ParsedReturn{} -> False
  MD.ParsedArchTermStmt{} -> True -- TODO: think harder about this
  MD.ParsedTranslateError{} -> True
  MD.ClassifyFailure{} -> True

-- | Kill back jumps within the function
--
-- FIXME: This is not very rigorous
backJumps ::
  Set.Set (MM.ArchSegmentOff arch) ->
  MD.ParsedBlock arch ids ->
  [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
backJumps internalAddrs pb =
  [ (MD.pblockAddr pb, tgt)
  | tgt <- case MD.pblockTermStmt pb of
     MD.ParsedJump _ tgt -> [tgt]
     MD.ParsedBranch _ _ tgt tgt' -> [tgt, tgt']
     MD.ParsedLookupTable _jt _ _ tgts -> F.toList tgts
     _ -> []
  , tgt < MD.pblockAddr pb
  , tgt `Set.member` internalAddrs
  ]

-- | Compute the /external/ edges induced by this 'MD.ParsedBlock' in the CFG that includes it
--
-- External edges are those that jump outside of the CFG
externalTransitions
  :: Set.Set (MM.ArchSegmentOff arch)
  -- ^ The set of targets that are known to be internal to the CFG we are constructing
  -> MD.ParsedBlock arch ids
  -> [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
externalTransitions internalAddrs pb =
  [ (MD.pblockAddr pb, tgt)
  | tgt <- case MD.pblockTermStmt pb of
      MD.ParsedCall{} -> []
      MD.PLTStub{} -> []
      MD.ParsedJump _ tgt -> [tgt]
      MD.ParsedBranch _ _ tgt tgt' -> [tgt, tgt']
      MD.ParsedLookupTable _jt _ _ tgts -> F.toList tgts
      MD.ParsedReturn{} -> []
      MD.ParsedArchTermStmt{} -> [] -- TODO: think harder about this
      MD.ParsedTranslateError{} -> []
      MD.ClassifyFailure{} -> []
  , tgt `Set.notMember` internalAddrs
  ]

-- | Construct an initial 'CS.SimContext' for Crucible
--
-- Note that this differs from some other uses of Crucible for machine code in
-- that it uses a custom memory model (see
-- 'Pate.Memory.MemTrace.memTraceIntrinsicTypes'). Additionally, it does not
-- support calls to functions; we only symbolically execute code that is loop-
-- and call- free.
initSimContext ::
  EquivM sym arch (CS.SimContext (MS.MacawSimulatorState sym) sym (MS.MacawExt arch))
initSimContext = withValid $ withSym $ \sym -> do
  exts <- CMR.asks envExtensions
  ha <- CMR.asks (handles . envCtx)
  return $
    CS.initSimContext
    sym
    PMT.memTraceIntrinsicTypes
    ha
    IO.stderr
    (CS.FnBindings CFH.emptyHandleMap)
    exts
    MS.MacawSimulatorState

-- | Convert a macaw register state into a Crucible assignment
regStateToAsn :: forall sym arch.
  HasCallStack =>
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  EquivM sym arch (Ctx.Assignment (CS.RegValue' sym)  (MS.MacawCrucibleRegTypes arch))
regStateToAsn regs = do
  archFs <- archFuns
  let allRegsAsn = MS.crucGenRegAssignment archFs
  return $ MS.macawAssignToCruc (\(PSR.MacawRegEntry _ v) -> CS.RV @sym v) $
    TFC.fmapFC (\r -> regs ^. MM.boundValue r) allRegsAsn

-- | Convert a Crucible register state back into a Macaw register state
structToRegState :: forall sym arch.
  CS.RegEntry sym (MS.ArchRegStruct arch) ->
  EquivM sym arch (MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym))
structToRegState e = do
  archVs <- CMR.asks $ envArchVals
  return $ MM.mkRegState (PSR.macawRegEntry . MS.lookupReg archVs e)

-- | Construct an initial global state for the symbolic execution engine
--
-- Note that this refers to crucible globals (and not global memory).  It
-- populates the set of globals with the variable used for tracing memory
-- operations and the special global that is used to determine how a branch
-- exits (e.g., due to a call or loop backedge).
getGlobals ::
  forall sym arch bin.
  PS.SimInput sym arch bin ->
  EquivM sym arch (CS.SymGlobalState sym)
getGlobals simInput = withValid $ withSym $ \sym -> do
  env <- CMR.ask
  blkend <- liftIO $ MS.initBlockEnd (Proxy @arch) sym
  return $
      CGS.insertGlobal (envMemTraceVar env) (PS.simInMem simInput)
    $ CGS.insertGlobal (envBlockEndVar env) blkend
    $ CGS.emptyGlobals

-- | Extract the final state after symbolic execution
--
-- This includes three things:
--
-- 1. The (symbolic) result value (which is a symbolic register
-- state) produced by the function
--
-- 2. The state of memory, which has both the memory post state and a trace of
-- operations
--
-- 3. The distinguished global that indicates the conditions under which the
-- superblock exits (e.g., via a loop backedge or function call)
--
-- The latter two are stored in Crucible global variables
--
-- This function will throw an exception if either global is missing (which
-- could actually be a panic condition) or if the symbolic execution times out
-- or aborts. Note that there should not be any cases where symbolic execution
-- aborts, as we have no assertions in the binary.
--
-- The return values are:
--
-- 1. The condition under which the result holds (this will often be @True@, but
--    could be constrained if a path leads to e.g., a divide by zero)
-- 2. The final register state resulting from the symbolic execution
-- 3. The final memory state
-- 4. The value indicating how the superblock exited (which can be symbolic)
--
-- TODO: What should happen if the Pred sym in a PartialRes in pres or pres' is
-- false?
getGPValueAndTrace ::
  forall sym arch p ext.
  CS.ExecResult p sym ext (CS.RegEntry sym (MS.ArchRegStruct arch)) ->
  EquivM sym arch
    ( W4.Pred sym
    , MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
    , PMT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    , CS.RegValue sym (MS.MacawBlockEndType arch)
    )
getGPValueAndTrace (CS.FinishedResult _ pres) = withSym $ \sym -> do
  mem <- CMR.asks envMemTraceVar
  eclass <- CMR.asks envBlockEndVar
  asm <- case pres of
    CS.TotalRes _ -> return $ W4.truePred sym
    CS.PartialRes _ p _ _ -> return p

  case pres ^. CS.partialValue of
    CS.GlobalPair val globs
      | Just mt <- CGS.lookupGlobal mem globs
      , Just ec <- CGS.lookupGlobal eclass globs -> withValid $ do
        val' <- structToRegState @sym @arch val
        return $ (asm, val', mt, ec)
    _ -> throwHere PEE.MissingCrucibleGlobals
getGPValueAndTrace (CS.AbortedResult _ ar) = throwHere . PEE.SymbolicExecutionFailed . ppAbortedResult $ ar
getGPValueAndTrace (CS.TimeoutResult _) = throwHere (PEE.SymbolicExecutionFailed "timeout")

-- | Run Crucible on the given CFG with the given initial conditions
evalCFG
  :: CS.SymGlobalState sym
  -- ^ The initial globals to symbolically execute with
  -> CS.RegMap sym tp
  -- ^ The initial register state
  -> CC.CFG (MS.MacawExt arch) blocks tp (MS.ArchRegStruct arch)
  -- ^ The CFG to symbolically execute
  -> EquivM sym arch (CS.ExecResult (MS.MacawSimulatorState sym) sym (MS.MacawExt arch) (CS.RegEntry sym (MS.ArchRegStruct arch)))
evalCFG globals regs cfg = do
  archRepr <- archStructRepr
  initCtx <- initSimContext
  liftIO $ id
    . CS.executeCrucible []
    . CS.InitialState initCtx globals CS.defaultAbortHandler archRepr
    . CS.runOverrideSim archRepr
    $ CS.regValue <$> CS.callCFG cfg regs

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) =
  "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"

-- | Symbolically execute a chunk of code under the preconditions determined by
-- the compositional analysis
simulate ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PS.SimInput sym arch bin ->
  EquivM sym arch (W4.Pred sym, PS.SimOutput sym arch bin)
simulate simInput = withBinary @bin $ do
  -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
  CC.SomeCFG cfg <- do
    CC.Some (DFC.Compose pbs_) <- PD.lookupBlocks (PS.simInBlock simInput)
    -- See Note [Loop Breaking]
    let pb:pbs = DL.sortOn MD.pblockAddr pbs_
        -- Multiple ParsedBlocks may have the same address, so the delete
        -- is really needed.
    let internalAddrs = Set.delete (MD.pblockAddr pb) $ Set.fromList [MD.pblockAddr b | b <- pbs]
    let (terminal_, nonTerminal) = DL.partition isTerminalBlock pbs
    let terminal = [pb | isTerminalBlock pb] ++ terminal_
    let killEdges =
          concatMap (backJumps internalAddrs) (pb : pbs) ++
          concatMap (externalTransitions internalAddrs) (pb:pbs)
    fns <- archFuns
    ha <- CMR.asks (handles . envCtx)
    be <- CMR.asks envBlockEndVar
    liftIO $ MS.mkBlockSliceCFG fns ha (W4L.OtherPos . fromString . show) pb nonTerminal terminal killEdges (Just be)
  let preRegs = PS.simInRegs simInput
  preRegsAsn <- regStateToAsn preRegs
  archRepr <- archStructRepr
  let regs = CS.assignReg archRepr preRegsAsn CS.emptyRegMap
  globals <- getGlobals simInput
  cres <- evalCFG globals regs cfg
  (asm, postRegs, memTrace, exitClass) <- getGPValueAndTrace cres

  return $ (asm, PS.SimOutput (PS.SimState memTrace postRegs) exitClass)

{- Note [Loop Breaking]

There's a slight hack here.

The core problem we're dealing with here is that renovate blocks
can have multiple basic blocks; and almost always do in the
rewritten binary. We want to stitch them together in the right
way, and part of that means deciding whether basic block
terminators are things we should "follow" to their target to
continue symbolically executing or not. Normally any block
terminator that goes to another basic block in the same renovate
block is one we want to keep symbolically executing through.

BUT if there is an actual self-contained loop within a single
renovate block, we want to avoid trying to symbolically execute
that forever, so we'd like to pick some of the edges in the
"block X can jump to block Y" graph that break all the cycles,
and mark all of those as terminal for the purposes of CFG
creation.

Instead of doing a careful analysis of that graph, we adopt the
following heuristic: kill any edges that point to the entry
point of the renovate block, and symbolically execute through
all the others. This catches at the very least any
single-basic-block loops in the original binary and in most
cases even their transformed version in the rewritten binary. If
we ever kill such an edge, we have certainly broken a cycle; but
cycles could appear in other ways that we don't catch.

This heuristic is reflected in the code like this: when deciding
if a jump should be killed, we compare jump targets to a
collection of "internal" addresses, and kill it if the target
isn't in that collection. Then we omit the entry point's address
from that collection, so that jumps to it are considered terminal.

-}
