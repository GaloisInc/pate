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
import qualified Data.List as DL
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.String ( fromString )
import qualified Data.Text as T
import           GHC.Stack ( HasCallStack, callStack )
import qualified System.IO as IO
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4L

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified Pate.Binary as PBi
import qualified Pate.Address as PA
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Memory.MemTrace as PMT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
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

-- | Construct an initial 'CS.SimContext' for Crucible
--
-- Note that this differs from some other uses of Crucible for machine code in
-- that it uses a custom memory model (see
-- 'Pate.Memory.MemTrace.memTraceIntrinsicTypes'). Additionally, it does not
-- support calls to functions; we only symbolically execute code that is loop-
-- and call- free.
initSimContext ::
  EquivM sym arch (CS.SimContext (MS.MacawSimulatorState sym) sym (MS.MacawExt arch))
initSimContext = withValid $ withBackend $ \bak -> do
  exts <- CMR.asks envExtensions
  ha <- CMR.asks (PMC.handles . envCtx)
  return $
    CS.initSimContext
    bak
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
--
-- Returns:
--
-- 1. The assumption required for the symbolic execution to be total
-- 2. The captured post-state
simulate ::
  forall sym arch bin.
  (HasCallStack, PBi.KnownBinary bin) =>
  PS.SimInput sym arch bin ->
  EquivM sym arch (W4.Pred sym, PS.SimOutput sym arch bin)
simulate simInput = withBinary @bin $ do
  CC.SomeCFG cfg <- do
    PMC.ParsedBlocks pbs_ <- PD.lookupBlocks (PS.simInBlock simInput)

    let entryAddr = PB.concreteAddress (PS.simInBlock simInput)

    let (pb,sbi) = computeSliceBodyInfo entryAddr pbs_
    let (terminal, nonTerminal) = DL.partition isTerminalBlock (sbiReachableBlocks sbi)
    let killEdges = sbiBackEdges sbi ++ sbiExitEdges sbi

    emitEvent (PE.ProofTraceEvent callStack entryAddr entryAddr (T.pack ("Discarding edges: " ++ show killEdges)))

    fns <- archFuns
    ha <- CMR.asks (PMC.handles . envCtx)
    be <- CMR.asks envBlockEndVar
    let posFn = W4L.OtherPos . fromString . show
    liftIO $ MS.mkBlockSliceCFG fns ha posFn pb nonTerminal terminal killEdges (Just be)
  let preRegs = PS.simInRegs simInput
  preRegsAsn <- regStateToAsn preRegs
  archRepr <- archStructRepr
  let regs = CS.assignReg archRepr preRegsAsn CS.emptyRegMap
  globals <- getGlobals simInput
  cres <- withSymBackendLock $ evalCFG globals regs cfg
  (asm, postRegs, memTrace, exitClass) <- getGPValueAndTrace cres

  return $ (asm, PS.SimOutput (PS.SimState memTrace postRegs) exitClass)


data SliceBodyInfo arch ids =
  SliceBodyInfo
  { sbiReachableAddrs  :: Set.Set (MM.ArchSegmentOff arch)
  , sbiReachableBlocks :: [ MD.ParsedBlock arch ids ]
  , sbiBackEdges       :: [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
  , sbiExitEdges       :: [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
  }

-- | Perform a depth-first search on the structure of the parsed blocks we have
--   in hand, starting from the given entry address. We want to find all the
--   reachable blocks, identify the back edges in the graph, and identify
--   what edges correspond to jumps outside the collection of blocks we have.
--   Return a @SliceBodyInfo@ capturing this information, and the parsed block
--   corresponding to the entry point.
computeSliceBodyInfo :: forall arch ids.
  PA.ConcreteAddress arch ->
  [ MD.ParsedBlock arch ids ] ->
  ( MD.ParsedBlock arch ids, SliceBodyInfo arch ids)
computeSliceBodyInfo entryAddr blks =
   case Map.lookup entryAddr blkmap of
     Nothing -> error $ unlines ["Could not find entry point in block map:"
                                , show entryAddr
                                , unwords (map (show . PA.segOffToAddr @arch . MD.pblockAddr) blks)
                                ]
     Just eblk -> 
        let sbi = dfs Set.empty eblk (SliceBodyInfo Set.empty [] [] [])
         in (eblk, sbi)

  where
    blkmap = Map.fromList [ (PA.segOffToAddr (MD.pblockAddr blk), blk) | blk <- blks ]

    dfs ancestors pb sbi =
          let addr       = MD.pblockAddr pb
              ancestors' = Set.insert addr ancestors
              ss         = DL.nub (MD.parsedTermSucc (MD.pblockTermStmt pb))
              sbi'       = foldl (visit_edge ancestors' addr) sbi ss
              raddrs     = Set.insert addr (sbiReachableAddrs sbi')
              rblks      = pb : sbiReachableBlocks sbi'
          in sbi'{ sbiReachableAddrs = raddrs, sbiReachableBlocks = rblks }

    visit_edge ancestors from sbi to
        -- back edge case
      | Set.member to ancestors = sbi{ sbiBackEdges = (from,to):sbiBackEdges sbi }

        -- cross/forward edge
      | Set.member to (sbiReachableAddrs sbi) = sbi

        -- tree edge
      | otherwise =
          case Map.lookup (PA.segOffToAddr to) blkmap of
            Nothing -> sbi{ sbiExitEdges = (from,to) : sbiExitEdges sbi }
            Just pb -> dfs ancestors pb sbi

