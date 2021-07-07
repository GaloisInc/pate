{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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

archStructRepr :: forall sym arch. EquivM sym arch (CC.TypeRepr (MS.ArchRegStruct arch))
archStructRepr = do
  archFs <- archFuns
  return $ CC.StructRepr $ MS.crucArchRegTypes archFs


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

-- FIXME: this is hardly rigorous
-- | Kill back jumps within the function
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

externalTransitions ::
  Set.Set (MM.ArchSegmentOff arch) ->
  MD.ParsedBlock arch ids ->
  [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
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

initSimContext ::
  EquivM sym arch (CS.SimContext (MS.MacawSimulatorState sym) sym (MS.MacawExt arch))
initSimContext = withValid $ withSym $ \sym -> do
  exts <- CMR.asks envExtensions
  ha <- CMR.asks $ handles . envCtx
  return $
    CS.initSimContext
    sym
    PMT.memTraceIntrinsicTypes
    ha
    IO.stderr
    (CS.FnBindings CFH.emptyHandleMap)
    exts
    MS.MacawSimulatorState

regStateToAsn :: forall sym arch.
  HasCallStack =>
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  EquivM sym arch (Ctx.Assignment (CS.RegValue' sym)  (MS.MacawCrucibleRegTypes arch))
regStateToAsn regs = do
  archFs <- archFuns
  let allRegsAsn = MS.crucGenRegAssignment archFs
  return $ MS.macawAssignToCruc (\(PSR.MacawRegEntry _ v) -> CS.RV @sym v) $
    TFC.fmapFC (\r -> regs ^. MM.boundValue r) allRegsAsn

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

-- TODO: What should happen if the Pred sym in a PartialRes in pres or pres' is false?
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

evalCFG ::
  CS.SymGlobalState sym ->
  CS.RegMap sym tp ->
  CC.CFG (MS.MacawExt arch) blocks tp (MS.ArchRegStruct arch) ->
  EquivM sym arch (CS.ExecResult (MS.MacawSimulatorState sym) sym (MS.MacawExt arch) (CS.RegEntry sym (MS.ArchRegStruct arch)))
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
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"

structToRegState :: forall sym arch.
  CS.RegEntry sym (MS.ArchRegStruct arch) ->
  EquivM sym arch (MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym))
structToRegState e = do
  archVs <- CMR.asks $ envArchVals
  return $ MM.mkRegState (PSR.macawRegEntry . MS.lookupReg archVs e)

simulate ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PS.SimInput sym arch bin ->
  EquivM sym arch (W4.Pred sym, PS.SimOutput sym arch bin)
simulate simInput = withBinary @bin $ do
  -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
  CC.SomeCFG cfg <- do
    CC.Some (DFC.Compose pbs_) <- PD.lookupBlocks (PS.simInBlock simInput)
    let pb:pbs = DL.sortOn MD.pblockAddr pbs_
        -- There's a slight hack here.
        --
        -- The core problem we're dealing with here is that renovate blocks
        -- can have multiple basic blocks; and almost always do in the
        -- rewritten binary. We want to stitch them together in the right
        -- way, and part of that means deciding whether basic block
        -- terminators are things we should "follow" to their target to
        -- continue symbolically executing or not. Normally any block
        -- terminator that goes to another basic block in the same renovate
        -- block is one we want to keep symbolically executing through.
        --
        -- BUT if there is an actual self-contained loop within a single
        -- renovate block, we want to avoid trying to symbolically execute
        -- that forever, so we'd like to pick some of the edges in the
        -- "block X can jump to block Y" graph that break all the cycles,
        -- and mark all of those as terminal for the purposes of CFG
        -- creation.
        --
        -- Instead of doing a careful analysis of that graph, we adopt the
        -- following heuristic: kill any edges that point to the entry
        -- point of the renovate block, and symbolically execute through
        -- all the others. This catches at the very least any
        -- single-basic-block loops in the original binary and in most
        -- cases even their transformed version in the rewritten binary. If
        -- we ever kill such an edge, we have certainly broken a cycle; but
        -- cycles could appear in other ways that we don't catch.
        --
        -- This heuristic is reflected in the code like this: when deciding
        -- if a jump should be killed, we compare jump targets to a
        -- collection of "internal" addresses, and kill it if the target
        -- isn't in that collection. Then we omit the entry point's address
        -- from that collection, so that jumps to it are considered terminal.

        -- Multiple ParsedBlocks may have the same address, so the delete
        -- is really needed.
        internalAddrs = Set.delete (MD.pblockAddr pb) $ Set.fromList [MD.pblockAddr b | b <- pbs]
        (terminal_, nonTerminal) = DL.partition isTerminalBlock pbs
        terminal = [pb | isTerminalBlock pb] ++ terminal_
        killEdges =
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
