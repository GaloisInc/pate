{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}

module Pate.Verification.PairGraph
  ( Gas(..)
  , initialGas
  , PairGraph
  , AbstractDomain
  , initialDomain
  , initialDomainSpec
  , initializePairGraph
  , chooseWorkItem
  , pairGraphWorklist
  , popWorkItem
  , updateDomain
  , modifyDomain
  , addReturnVector
  , getReturnVectors
  , freshDomain
  , pairGraphComputeVerdict
  , getCurrentDomain
  , considerObservableEvent
  , considerDesyncEvent
  , recordMiscAnalysisError
  , reportAnalysisErrors
  , TotalityCounterexample(..)
  , ObservableCounterexample(..)
  , ppProgramDomains
  , getOrphanedReturns
  , addExtraEdge
  , getExtraEdges
  , addTerminalNode
  , emptyReturnVector
  , getEquivCondition
  , setEquivCondition
  , dropDomain
  , markEdge
  , getSyncPoint
  , asSyncPoint
  , getBackEdgesFrom
  , setSyncPoint
  , getCombinedSyncPoint
  , addToWorkList
  , SyncPoint(..)
  , updateSyncPoint
  , singleNodeRepr
  , queuePendingAction
  , runPendingActions
  , addLazyAction
  , VerifierResult(..)
  ) where

import           Prettyprinter

import           Control.Monad (foldM)
import           Control.Monad.IO.Class

import qualified Data.Foldable as F
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Parameterized.Classes
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word (Word32)
import qualified Lumberjack as LJ

import qualified Data.Parameterized.TraversableF as TF

import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Equivalence as PE
import qualified Pate.Event as Event
import           Pate.Monad
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Verification.Domain as PVD
import qualified Pate.SimState as PS


import           Pate.Verification.PairGraph.Node ( GraphNode(..), NodeEntry, NodeReturn, pattern GraphNodeEntry, pattern GraphNodeReturn, rootEntry, nodeBlocks, rootReturn, nodeFuns, graphNodeBlocks, getDivergePoint )
import           Pate.Verification.StrongestPosts.CounterExample ( TotalityCounterexample(..), ObservableCounterexample(..) )

import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( AbstractDomain, AbstractDomainSpec )
import           Pate.TraceTree
import qualified Pate.Binary as PBi
import Data.Parameterized (Some(..))
import Control.Applicative (Const(..))
import qualified Control.Monad.IO.Unlift as IO

-- | Gas is used to ensure that our fixpoint computation terminates
--   in a reasonable amount of time.  Gas is expended each time
--   we widen an abstract domain along a control flow path
--   from some particular slice.  It is intended to only
--   be used along loops or recursive cycles.  Right now,
--   the amount of gas is set to a fairly small number (5)
--   under the assumption that widening will stabalize
--   either quickly or not at all.
newtype Gas = Gas Word32

-- | Temporary constant value for the gas parameter.
--   Should make this configurable.
initialGas :: Gas
initialGas = Gas 5

-- | The PairGraph is the main datastructure tracking all the
--   information we compute when analysing a program. The analysis we
--   are doing is essentially a (context insensitive) forward dataflow
--   analysis.
--
--   The core assumption we make is that the pair of programs being
--   analysed are nearly the same, and thus have control flow that
--   advances nearly in lockstep. The abstract domains capture
--   information about where the program state differs and we
--   propagate that information forward through the program attempting
--   to compute a fixpoint, which will give us a sound
--   overapproximation of all the differences that may exist between
--   runs of the two programs.
--
--   As we compute the fixpoint we note cases where we discover a
--   location where we cannot keep the control-flow synchronized, or
--   where we discover some observable difference in the program
--   behavior. These "program desyncrhonization" and "observable
--   difference" occurences are ultimately the information we want to
--   deliver to the user.
--
--   We additionally track situations where we cut off the fixpoint
--   computation early as reportable situations that represent
--   limitations of the analysis; such situations represent potential
--   sources of unsoundness that may cause us to miss desyncronization
--   or observable difference events.
data PairGraph sym arch =
  PairGraph
  { -- | The main data structure for the pair graph, which records the current abstract
    --   domain value for each reachable graph node.
    pairGraphDomains :: !(Map (GraphNode arch) (AbstractDomainSpec sym arch))

    -- | This data structure records the amount of remaining "gas" corresponding to each
    --   edge of the program graph. Initially, this map is empty. When we traverse an
    --   edge for the first time, we record it's initial amount of gas, which is later
    --   decremented each time we perform an update along this edge in the future.
    --   We stop propagating updates along this edge when the amount of gas reaches zero.
  , pairGraphGas :: !(Map (GraphNode arch, GraphNode arch) Gas)

    -- | The "worklist" which records the set of nodes that must be revisited.
    --   Whenever we propagate a new abstract domain to a node, that node must
    --   be revisited, and here we record all such nodes that must be examinied.
    --
    --   For now, this is just a set and we examine nodes in whatever order is defined
    --   by their 'Ord' instance. It may make sense at some point to use a more sophisticated
    --   mechanism to determine the order in which to visit nodes.
  , pairGraphWorklist :: !(Set (GraphNode arch))

    -- | The set of blocks where this function may return to. Whenever we see a function
    --   call to the given FunPair, we record the program point pair where the function
    --   returns to here. This is used to tell us where we need to propagate abstract domain
    --   information when visiting a ReturnNode.
  , pairGraphReturnVectors :: !(Map (NodeReturn arch) (Set (NodeEntry arch)))

    -- TODO, I'm not entirely sure I love this idea of tracking error conditions in this
    -- data structure like this.  It works for now, but maybe is worth thinking about some more.
    -- Because of the monotonicity of the system, results can be reported as soon as they are
    -- discovered, so perhaps they should be streamed directly to output somehow.

    -- TODO, maybe this is the right place to include conditional equivalence conditions?

    -- | If we find a counterexample regarding observables in a particular block, record it here.
    --   Later, this can be used to generate reports to the user.  We also avoid checking for
    --   additional counterexamples for the given block if we have already found one.
  , pairGraphObservableReports :: !(Map (NodeEntry arch) (ObservableCounterexample sym (MM.ArchAddrWidth arch)))

    -- | If we find a counterexample to the exit totality check, record it here.  This occurs when
    --   the programs have sufficiently-different control flow that they cannot be synchronized, or
    --   when the analysis encounters some control-flow construct it doesn't know how to handle.
    --   Once we find a desynchronization error for a particular block, we do not look for additional
    --   involving that same block.
  , pairGraphDesyncReports :: !(Map (NodeEntry arch) (TotalityCounterexample (MM.ArchAddrWidth arch)))

    -- | Keep track of the target nodes whenever we run out of gas while trying to reach fixpoint.
    --   This can be used to report to the user instances where the analysis may be incomplete.
  , pairGraphGasExhausted :: !(Set (GraphNode arch))

    -- | Other sorts of analysis errors not captured by the previous categories. These generally
    --   arise from things like incompleteness of the SMT solvers, or other unexpected situations
    --   that may impact the soundness of the analysis.
  , pairGraphMiscAnalysisErrors :: !(Map (GraphNode arch) [PEE.EquivalenceError])

    -- | Extra edges to follow when processing a node. These arise from analysis failures
    --   when we can't determine how a function exits, but still want to continue analyzing
    --   past all of its call sites.
  , pairGraphExtraEdges :: !(Map (NodeEntry arch) (Set (GraphNode arch)))
    -- | Avoid adding extra edges to these nodes, as we expect these functions
    --   may not actually return on any path (i.e. they end in an abort or exit)
  , pairGraphTerminalNodes :: !(Set (NodeReturn arch))
  , pairGraphEquivConditions :: !(Map (GraphNode arch) (PEC.EquivConditionSpec sym arch))
    -- | Any edges that have been followed at any point (which may later become infeasible
    -- due to further analysis)
  , pairGraphEdges :: !(Map (GraphNode arch) (Set (GraphNode arch)))
    -- | Reverse map of the above (from descendants to ancestors)
  , pairGraphBackEdges :: !(Map (GraphNode arch) (Set (GraphNode arch)))
    -- | Mapping from singleton nodes to their "synchronization" point, representing
    --   the case where two independent program analysis steps have occurred and now
    --   their control-flows have re-synchronized
  , pairGraphSyncPoints :: !(Map (GraphNode arch) (SyncPoint arch))
  , pairGraphPendingActs :: PendingActions sym arch
  }

-- Final result of verifier after widening for a particular edge
data VerifierResult sym arch = forall v.
    VerifierResult 
      { resultScope :: PS.SimScope sym arch v 
      , resultBundle :: PS.SimBundle sym arch v
      , resultPredomain :: AbstractDomain sym arch v
      , resultPostdomain :: AbstractDomain sym arch v
      }

data PendingActions sym arch =
  PendingActions (Map (GraphNode arch, GraphNode arch) [(Int, (VerifierResult sym arch -> PairGraph sym arch -> IO (Maybe (PairGraph sym arch))))]) Int

dropActId' ::
  Int ->
  PendingActions sym arch ->
  PendingActions sym arch
dropActId' actId (PendingActions acts nextActId) = PendingActions (fmap (filter (\(actId',_) -> actId /= actId')) acts) nextActId

dropActId ::
  Int ->
  PairGraph sym arch ->
  PairGraph sym arch
dropActId actId pg = pg { pairGraphPendingActs = dropActId' actId (pairGraphPendingActs pg) }

addLazyAction ::
  IsTreeBuilder k e m =>
  IO.MonadUnliftIO m =>
  (GraphNode arch, GraphNode arch) ->
  PairGraph sym arch ->
  String ->
  (forall m'. Monad m' => ((String -> (VerifierResult sym arch -> PairGraph sym arch -> m (PairGraph sym arch)) -> m' ())) -> m' ()) ->
  m (PairGraph sym arch)  
addLazyAction edge pg actNm f = do
  pendingAct <- chooseLazy @"()" actNm (\choice -> f (\nm act -> choice nm () (\(result,pg') -> act result pg')))
  queuePendingAction edge (\result pg' -> pendingAct (result,pg')) pg

queuePendingAction ::
  IO.MonadUnliftIO m =>
  (GraphNode arch, GraphNode arch) ->
  (VerifierResult sym arch -> PairGraph sym arch -> m (Maybe (PairGraph sym arch))) ->
  PairGraph sym arch ->
  m (PairGraph sym arch)
queuePendingAction edge act pg = do
  inIO <- IO.askRunInIO
  let PendingActions actMap nextActId = pairGraphPendingActs pg
  let act' = (nextActId, (\result pg' -> inIO (act result (dropActId nextActId pg'))))
  return $ pg { pairGraphPendingActs = PendingActions (Map.insertWith (++) edge [act'] actMap) (nextActId + 1) }

runPendingActions ::
  forall sym arch m.
  IO.MonadIO m =>
  (GraphNode arch, GraphNode arch) ->
  VerifierResult sym arch ->
  PairGraph sym arch ->
  m (PairGraph sym arch)
runPendingActions edge result pg = do
  let PendingActions actMap _ = pairGraphPendingActs pg
  let actList = fromMaybe [] (Map.lookup edge actMap)
  go (map snd actList) pg
  where 
    go :: [(VerifierResult sym arch -> PairGraph sym arch -> IO (Maybe (PairGraph sym arch)))] -> PairGraph sym arch -> m (PairGraph sym arch)
    go [] pg' = return pg'
    go (act:acts) pg' = (liftIO $ act result pg') >>= \case
      Just pg'' -> go acts pg''
      Nothing -> go acts pg'

data SyncPoint arch =
  SyncPoint { syncNodes :: PPa.PatchPairC (GraphNode arch), syncTerminal :: Maybe Bool }

ppProgramDomains ::
  forall sym arch a.
  ( PA.ValidArch arch
  , W4.IsSymExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  (W4.Pred sym -> Doc a) ->
  PairGraph sym arch ->
  Doc a
ppProgramDomains ppPred gr =
  vcat
  [ vcat [ pretty pPair
         , PS.viewSpecBody adSpec $ \ad -> PAD.ppAbstractDomain ppPred ad
         ]
  | (pPair, adSpec) <- Map.toList (pairGraphDomains gr)
  ]


-- | A totally empty initial pair graph.
emptyPairGraph :: PairGraph sym arch
emptyPairGraph =
  PairGraph
  { pairGraphDomains  = mempty
  , pairGraphGas      = mempty
  , pairGraphWorklist = mempty
  , pairGraphReturnVectors = mempty
  , pairGraphObservableReports = mempty
  , pairGraphDesyncReports = mempty
  , pairGraphGasExhausted = mempty
  , pairGraphMiscAnalysisErrors = mempty
  , pairGraphExtraEdges = mempty
  , pairGraphTerminalNodes = mempty
  , pairGraphEquivConditions = mempty
  , pairGraphEdges = mempty
  , pairGraphBackEdges = mempty
  , pairGraphSyncPoints = mempty
  , pairGraphPendingActs = PendingActions Map.empty 0
  }

-- | Given a pair graph and a function pair, return the set of all
--   the sites we have encountered so far where this function may return to.
getReturnVectors ::
  PairGraph sym arch ->
  NodeReturn arch ->
  Set (NodeEntry arch)
getReturnVectors gr fPair = fromMaybe mempty (Map.lookup fPair (pairGraphReturnVectors gr))

-- | Look up the current abstract domain for the given graph node.
getCurrentDomain ::
  PairGraph sym arch ->
  GraphNode arch ->
  Maybe (AbstractDomainSpec sym arch)
getCurrentDomain pg nd = Map.lookup nd (pairGraphDomains pg)

getEdgesFrom ::
  PairGraph sym arch ->
  GraphNode arch ->
  Set (GraphNode arch)
getEdgesFrom pg nd = case Map.lookup nd (pairGraphEdges pg) of
  Just s -> s
  Nothing -> Set.empty

getBackEdgesFrom ::
  PairGraph sym arch ->
  GraphNode arch ->
  Set (GraphNode arch)
getBackEdgesFrom pg nd = case Map.lookup nd (pairGraphBackEdges pg) of
  Just s -> s
  Nothing -> Set.empty

-- | Delete the abstract domain for the given node, following
--   any reachable edges and discarding those domains as well
--   This is necessary if a domain is "narrowed": i.e. it moves
--   from assuming fewer equalities to assuming more equalities.
--   Marks any ancestors as requiring re-analysis
dropDomain ::
  GraphNode arch -> 
  PairGraph sym arch ->
  PairGraph sym arch 
dropDomain nd pg = case getCurrentDomain pg nd of
  Just{}->
    let
      -- clear this domain and all descendant domains
      pg' = case Set.null (getBackEdgesFrom pg nd) of
        -- don't drop the domain for a toplevel entrypoint, but mark it for
        -- re-analysis
        True -> pg { pairGraphWorklist = Set.insert nd (pairGraphWorklist pg) }
        False -> pg { pairGraphDomains = Map.delete nd (pairGraphDomains pg), pairGraphWorklist = Set.delete nd (pairGraphWorklist pg) }
      pg'' = Set.foldl' (\pg_ nd' -> dropDomain nd' pg_) pg' (getEdgesFrom pg nd)
      -- mark all ancestors as requiring re-processing
    in addAncestors Set.empty pg'' nd
  Nothing -> pg
  where
    addAncestors :: Set (GraphNode arch) -> PairGraph sym arch -> GraphNode arch -> PairGraph sym arch
    addAncestors considered pg_ nd_ = case Set.member nd_ considered of
      True -> pg_
      False -> case addToWorkList nd_ pg_ of
        Just pg' -> pg'
        -- if this node has no defined domain (i.e it was dropped as part of the previous
        -- step) then we consider further ancestors
        Nothing -> Set.foldl' (addAncestors (Set.insert nd_ considered)) pg_ (getBackEdgesFrom pg_ nd_)


getEquivCondition ::
  PairGraph sym arch ->
  GraphNode arch ->
  Maybe (PEC.EquivConditionSpec sym arch)
getEquivCondition pg nd = Map.lookup nd (pairGraphEquivConditions pg)
  
setEquivCondition ::
  GraphNode arch ->
  PEC.EquivConditionSpec sym arch ->
  PairGraph sym arch ->
  PairGraph sym arch
setEquivCondition nd cond pg = pg { pairGraphEquivConditions = Map.insert nd cond (pairGraphEquivConditions pg) }

-- | If an observable counterexample has not already been found
--   for this block pair, run the given action to check if there
--   currently is one.
considerObservableEvent :: Monad m =>
  PairGraph sym arch ->
  NodeEntry arch ->
  (m (Maybe (ObservableCounterexample sym (MM.ArchAddrWidth arch)), PairGraph sym arch)) ->
  m (PairGraph sym arch)
considerObservableEvent gr bPair action =
  case Map.lookup bPair (pairGraphObservableReports gr) of
    -- we have already found observable event differences at this location, so skip the check
    Just _ -> return gr
    Nothing ->
      do (mcex, gr') <- action
         case mcex of
           Nothing  -> return gr'
           Just cex -> return gr'{ pairGraphObservableReports = Map.insert bPair cex (pairGraphObservableReports gr) }

-- | If a program desync has not already be found
--   for this block pair, run the given action to check if there
--   currently is one.
considerDesyncEvent :: Monad m =>
  IsTreeBuilder '(sym, arch) PEE.EquivalenceError m =>
  PA.ValidArch arch =>
  PairGraph sym arch ->
  NodeEntry arch ->
  (m (Maybe (TotalityCounterexample (MM.ArchAddrWidth arch)), PairGraph sym arch)) ->
  m (PairGraph sym arch)
considerDesyncEvent gr bPair action =
  case Map.lookup bPair (pairGraphDesyncReports gr) of
    -- we have already found observable event differences at this location, so skip the check
    Just cex -> do
      withTracing @"totalityce" cex $ 
        emitTraceWarning $ PEE.equivalenceError $ PEE.NonTotalBlockExits (nodeBlocks bPair)
      return gr
    Nothing ->
      do (mcex, gr') <- action
         case mcex of
           Nothing  -> return gr'
           Just cex -> do
             withTracing @"totalityce" cex $ 
               emitTraceWarning $ PEE.equivalenceError $ PEE.NonTotalBlockExits (nodeBlocks bPair)
             return gr'{ pairGraphDesyncReports = Map.insert bPair cex (pairGraphDesyncReports gr) }

-- | Record an error that occured during analysis that doesn't fall into one of the
--   other, more structured, types of errors.
recordMiscAnalysisError ::
  PairGraph sym arch ->
  GraphNode arch ->
  PEE.EquivalenceError ->
  PairGraph sym arch
recordMiscAnalysisError gr nd er =
  let m = Map.alter f nd (pairGraphMiscAnalysisErrors gr)
      f Nothing  = Just [er]
      f (Just s) = Just (er:s)
   in gr{ pairGraphMiscAnalysisErrors = m }


-- | TODO, Right now, this just prints error reports to stdout.
--   We should decide how and to what extent this should connect
--   to the `emitEvent` infrastructure.
reportAnalysisErrors
  :: (PA.ValidArch arch, W4.IsExprBuilder sym, MonadIO m)
  => LJ.LogAction IO (Event.Event arch)
  -> PairGraph sym arch
  -> m ()
reportAnalysisErrors logAction gr =
  do mapM_ reportObservables (Map.toList (pairGraphObservableReports gr))
     mapM_ reportDesync (Map.toList (pairGraphDesyncReports gr))
     mapM_ reportGasExhausted (Set.toList (pairGraphGasExhausted gr))
     mapM_ reportMiscError (Map.toList (pairGraphMiscAnalysisErrors gr))
 where
   reportObservables (pPair, ocex) =
     liftIO $ LJ.writeLog logAction (Event.StrongestPostObservable pPair ocex)

   reportDesync (pPair, tcex) =
     liftIO $ LJ.writeLog logAction (Event.StrongestPostDesync pPair tcex)

   reportGasExhausted pPair =
     liftIO $ LJ.writeLog logAction (Event.GasExhausted pPair)

   reportMiscError (pPair, msgs) =
     liftIO $ F.forM_ msgs $ \msg -> do
       LJ.writeLog logAction (Event.StrongestPostMiscError pPair msg)


initialDomain :: EquivM sym arch (PAD.AbstractDomain sym arch v)
initialDomain = withSym $ \sym -> 
  PAD.AbstractDomain 
  <$> pure (PVD.universalDomain sym)
  <*> (PPa.forBins $ \_ -> return $ PAD.emptyDomainVals)
  <*> (PPa.forBins $ \_ -> PAD.emptyEvents sym)

initialDomainSpec ::
  forall sym arch.
  GraphNode arch ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
initialDomainSpec (GraphNodeEntry blocks) = withTracing @"function_name" "initialDomainSpec" $ 
  withFreshVars blocks $ \_vars -> do
    dom <- initialDomain
    return (mempty, dom)
initialDomainSpec (GraphNodeReturn fPair) = withTracing @"function_name" "initialDomainSpec" $ do
  let blocks = TF.fmapF PB.functionEntryToConcreteBlock fPair
  withFreshVars blocks $ \_vars -> do
    dom <- initialDomain
    return (mempty, dom)

-- | Given a list of top-level function entry points to analyse,
--   initialize a pair graph with default abstract domains for those
--   entry points and add them to the work list.
initializePairGraph :: forall sym arch.
  [PB.FunPair arch] ->
  EquivM sym arch (PairGraph sym arch)
initializePairGraph pPairs = foldM (\x y -> initPair x y) emptyPairGraph pPairs
  where
    initPair :: PairGraph sym arch -> PB.FunPair arch -> EquivM sym arch (PairGraph sym arch)
    initPair gr fnPair =
      do let bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair
         withPair bPair $ do
           -- initial state of the pair graph: choose the universal domain that equates as much as possible
           let node = GraphNode (rootEntry bPair)
           idom <- initialDomainSpec node
           -- when the program is initialized, we assume no memory regions are allocated,
           -- and therefore we pick a concrete initial region that doesn't overlap with
           -- the global or stack regions.
           --
           -- in the event that this node is encountered again (i.e. the analysis entry
           -- point is some intermediate program point), then this value domain will simply
           -- be overridden as a result of widening
           rootDom <- PS.forSpec idom $ \_ idom' -> do
             vals' <- PPa.forBins $ \bin -> do
               vals <- PPa.get bin (PAD.absDomVals idom')
               -- FIXME: compute this from the global and stack regions
               return $ vals { PAD.absMaxRegion = PAD.AbsIntConstant 3 }
             return $ idom' { PAD.absDomVals = vals' }
           let gr1 = freshDomain gr node rootDom
           return $ emptyReturnVector gr1 (rootReturn fnPair)


popWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  GraphNode arch ->
  (PairGraph sym arch, GraphNode arch, AbstractDomainSpec sym arch)
popWorkItem gr nd = case Map.lookup nd (pairGraphDomains gr) of
  Nothing -> panic Verifier "popWorkItem" ["Could not find domain corresponding to block pair", show nd]
  Just d  -> 
    let wl = Set.delete nd (pairGraphWorklist gr)
    in (gr{ pairGraphWorklist = wl }, nd, d)

-- | Given a pair graph, chose the next node in the graph to visit
--   from the work list, updating the necessary bookeeping.  If the
--   work list is empty, return Nothing, indicating that we are done.
chooseWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  Maybe (PairGraph sym arch, GraphNode arch, AbstractDomainSpec sym arch)
chooseWorkItem gr =
  -- choose the smallest pair from the worklist. This is a pretty brain-dead
  -- heuristic.  Perhaps we should do something more clever.
  case Set.minView (pairGraphWorklist gr) of
    Nothing -> Nothing
    Just (nd, wl) -> case Map.lookup nd (pairGraphDomains gr) of
      Nothing -> panic Verifier "chooseWorkItem" ["Could not find domain corresponding to block pair", show nd]
      Just d  -> Just (gr{ pairGraphWorklist = wl }, nd, d)

-- | Update the abstract domain for the target graph node,
--   decreasing the gas parameter as necessary.
--   If we have run out of Gas, return a `Left` value.
--   The domain will be updated, but the graph node will
--   not be added back to the work list.
--   Return a `Right` value if the update succeeded.
updateDomain ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ point pair we are jumping from -} ->
  GraphNode arch {- ^ point pair we are jumping to -} ->
  AbstractDomainSpec sym arch {- ^ new domain value to insert -} ->
  Either (PairGraph sym arch) (PairGraph sym arch)
updateDomain gr pFrom pTo d
  | g > 0 = Right $ markEdge pFrom pTo $ gr
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            , pairGraphGas      = Map.insert (pFrom,pTo) (Gas (g-1)) (pairGraphGas gr)
            , pairGraphWorklist = Set.insert pTo (pairGraphWorklist gr)
            , pairGraphEdges = Map.insertWith Set.union pFrom (Set.singleton pTo) (pairGraphEdges gr)
            , pairGraphBackEdges = Map.insertWith Set.union pTo (Set.singleton pFrom) (pairGraphBackEdges gr)
            }

  | otherwise =
            Left $ markEdge pFrom pTo $ gr
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            }

  where
     -- Lookup the amount of remaining gas.  Initialize to a fresh value
     -- if it is not in the map
      Gas g = fromMaybe initialGas (Map.lookup (pFrom,pTo) (pairGraphGas gr))

modifyDomain ::
  Monad m =>
  GraphNode arch ->
  PairGraph sym arch ->
  (forall scope. PS.SimScope sym arch scope -> AbstractDomain sym arch scope -> m (AbstractDomain sym arch scope, PEC.EquivalenceCondition sym arch scope)) ->
  m (PairGraph sym arch)
modifyDomain nd pg f  = case Map.lookup nd (pairGraphDomains pg) of
  Just domSpec -> do
    (domSpec', eqSpec') <- PS.forSpec2 domSpec f
    return $ (pg { pairGraphDomains = Map.insert nd domSpec' (pairGraphDomains pg), pairGraphEquivConditions = Map.insert nd eqSpec' (pairGraphEquivConditions pg) })
  Nothing -> return pg

emptyReturnVector ::
  PairGraph sym arch ->
  NodeReturn arch ->
  PairGraph sym arch
emptyReturnVector gr ret = gr{ pairGraphReturnVectors = rvs }
  where
    rvs = Map.alter f ret (pairGraphReturnVectors gr)
    f Nothing  = Just (Set.empty)
    f (Just s) = Just s
                 
-- | When we encounter a function call, record where the function
--   returns to so that we can correctly propagate abstract domain
--   information from function returns to their call sites.
addReturnVector ::
  PairGraph sym arch ->
  NodeReturn arch {- ^ The function being called -}  ->
  NodeEntry arch {- ^ The program point where it returns to -} ->
  PairGraph sym arch
addReturnVector gr funPair retPair =
   -- If the domain graph already has a node corresponding to the
   -- return point of the function we are calling, make sure
   -- we explore the return site by adding the function return node
   -- to the work list. This ensures that we explore the code following
   -- the return even if the dataflow doesn't force a reexamination of
   -- the body of the called function.
   case Map.lookup (ReturnNode funPair) (pairGraphDomains gr) of
     -- No node for the return from this function. Either this is the first
     -- time we have found a call to this function, or previous explorations
     -- never have not reached a return. There is nothing we need to do
     -- other than register retPair as a return vector.
     Nothing -> gr{ pairGraphReturnVectors = rvs }

     -- We know there is at least one control-flow path through the function
     -- we are calling that returns. We need to ensure that we propagate
     -- information from the function return to retPair.  The easiest way
     -- to do this is to add the return node corresponding to funPair to
     -- the worklist.
     Just _ ->
       gr{ pairGraphReturnVectors = rvs
         , pairGraphWorklist = wl
         }

  where
    -- Remember that retPair is one of the places that funPair
    -- can return to
    rvs = Map.alter f funPair (pairGraphReturnVectors gr)
    f Nothing  = Just (Set.singleton retPair)
    f (Just s) = Just (Set.insert retPair s)

    wl = Set.insert (ReturnNode funPair) (pairGraphWorklist gr)


getSyncPoint ::
  PairGraph sym arch ->
  PBi.WhichBinaryRepr bin ->
  GraphNode arch ->
  Maybe (GraphNode arch)
getSyncPoint gr bin nd = case Map.lookup nd (pairGraphSyncPoints gr) of
  Just (SyncPoint syncPair _) -> PPa.getC bin syncPair
  Nothing -> Nothing

updateSyncPoint ::
  PairGraph sym arch ->
  GraphNode arch -> 
  (SyncPoint arch -> SyncPoint arch) ->
  PairGraph sym arch
updateSyncPoint pg nd f = case getDivergePoint nd of
  Just divergePoint | Just sync <- asSyncPoint pg nd -> 
    pg { pairGraphSyncPoints = Map.insert divergePoint (f sync) (pairGraphSyncPoints pg)}
  _ -> pg

asSyncPoint ::
  PairGraph sym arch ->
  GraphNode arch ->
  Maybe (SyncPoint arch)
asSyncPoint pg nd = do
  divergeNode <- getDivergePoint nd
  Some bin <- singleNodeRepr nd
  sync@(SyncPoint syncPair _) <- Map.lookup divergeNode (pairGraphSyncPoints pg)
  nd' <- PPa.getC bin syncPair
  case nd == nd' of
    True -> return sync
    False -> Nothing

-- | If both sides of the sync point are defined, returns
--   the merged node for them
getCombinedSyncPoint ::
  PairGraph sym arch ->
  GraphNode arch ->
  Maybe (GraphNode arch, SyncPoint arch)
getCombinedSyncPoint gr ndDiv = do
  sync@(SyncPoint syncPair _) <- Map.lookup ndDiv (pairGraphSyncPoints gr)
  case syncPair of
    PPa.PatchPairSingle{} -> Nothing
    PPa.PatchPairC ndO ndP -> case combineNodes ndO ndP of
      Just mergedNode -> Just (mergedNode, sync)
      Nothing -> panic Verifier "getCombinedSyncPoint" ["Unexpected sync nodes"]

-- | Compute a merged node for two diverging nodes
-- FIXME: do we need to support mismatched node kinds here?
combineNodes :: GraphNode arch -> GraphNode arch -> Maybe (GraphNode arch)
combineNodes node1 node2 = do
  (nodeO, nodeP) <- case PPa.get PBi.OriginalRepr (graphNodeBlocks node1) of
    Just{} -> return (node1, node2)
    Nothing -> return (node2, node1)
  case (nodeO, nodeP) of
    (GraphNode nodeO', GraphNode nodeP') -> do
      blocksO <- PPa.get PBi.OriginalRepr (nodeBlocks nodeO')
      blocksP <- PPa.get PBi.PatchedRepr (nodeBlocks nodeP')
      -- FIXME: retain calling context?
      return $ GraphNode $ rootEntry (PPa.PatchPair blocksO blocksP)
    (ReturnNode nodeO', ReturnNode nodeP') -> do
      fnsO <- PPa.get PBi.OriginalRepr (nodeFuns nodeO')
      fnsP <- PPa.get PBi.PatchedRepr (nodeFuns nodeP')
      -- FIXME: retain calling context?
      return $ ReturnNode $ rootReturn (PPa.PatchPair fnsO fnsP)
    _ -> Nothing

singleNodeRepr :: GraphNode arch -> Maybe (Some (PBi.WhichBinaryRepr))
singleNodeRepr nd = case graphNodeBlocks nd of
  PPa.PatchPairSingle bin _ -> return $ Some bin
  PPa.PatchPair{} -> Nothing

setSyncPoint ::
  PPa.PatchPairM m =>
  PairGraph sym arch ->
  GraphNode arch {- ^ The divergent node -}  ->
  GraphNode arch {- ^ The sync node -} ->
  m (PairGraph sym arch)
setSyncPoint pg ndDiv ndSync = do
  fmap PPa.someC $ PPa.forBinsC $ \bin -> do
    -- check which binary these nodes are for
    _ <- PPa.get bin (graphNodeBlocks ndDiv)
    _ <- PPa.get bin (graphNodeBlocks ndSync)
    let ndSync' = PPa.PatchPairSingle bin (Const ndSync)
    case Map.lookup ndDiv (pairGraphSyncPoints pg) of
      Just (SyncPoint sp b) -> do
        sp' <- PPa.update sp $ \bin' -> PPa.get bin' ndSync'
        return $ pg { pairGraphSyncPoints = Map.insert ndDiv (SyncPoint sp' b) (pairGraphSyncPoints pg) }
      Nothing -> do
        let sp = PPa.mkSingle bin (Const ndSync)
        return $ pg {pairGraphSyncPoints = Map.insert ndDiv (SyncPoint sp Nothing) (pairGraphSyncPoints pg) }

-- | Add a node back to the worklist to be re-analyzed if there is
--   an existing abstract domain for it. Otherwise return Nothing.
addToWorkList ::
  GraphNode arch ->
  PairGraph sym arch ->
  Maybe (PairGraph sym arch)
addToWorkList nd gr = case getCurrentDomain gr nd of
  Just{} -> Just $ gr { pairGraphWorklist = Set.insert nd (pairGraphWorklist gr) }
  Nothing -> Nothing

-- | Add an initial abstract domain value to a graph node, and
--   record it in the worklist to be visited.
freshDomain ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ point pair we are jumping to -} ->
  AbstractDomainSpec sym arch {- ^ new domain value to insert -} ->
  PairGraph sym arch
freshDomain gr pTo d =
  gr{ pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
    , pairGraphWorklist = Set.insert pTo (pairGraphWorklist gr)
    }

markEdge ::
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  PairGraph sym arch
markEdge from to gr =
  gr { pairGraphEdges = Map.insertWith Set.union from (Set.singleton to) (pairGraphEdges gr)
     , pairGraphBackEdges = Map.insertWith Set.union to (Set.singleton from) (pairGraphBackEdges gr)}

addExtraEdge ::
  PairGraph sym arch ->
  NodeEntry arch ->
  GraphNode arch ->
  PairGraph sym arch
addExtraEdge gr from to = markEdge (GraphNode from) to $
  gr { pairGraphExtraEdges = Map.insertWith Set.union from (Set.singleton to) ( pairGraphExtraEdges gr)
     }


getExtraEdges ::
  PairGraph sym arch ->
  NodeEntry arch ->
  Set (GraphNode arch)
getExtraEdges gr e = case Map.lookup e (pairGraphExtraEdges gr) of
  Just es -> es
  Nothing -> Set.empty

-- | Mark a return node for a function as terminal, indicating that it
--   might not have any valid return paths.
--   A non-terminal function with no return paths is considered an analysis error, since
--   we can't continue analyzing past any of its call sites.
addTerminalNode ::
  PairGraph sym arch ->
  NodeReturn arch ->
  PairGraph sym arch
addTerminalNode gr nd = gr { pairGraphTerminalNodes = Set.insert nd (pairGraphTerminalNodes gr) }

-- | Return the set of "orphaned" nodes in the current graph. An orphaned
--   node is a return node for a function where no return path was found
--   (i.e. we have a set of call sites for the function, but no post-equivalence
--   domain). This usually indicates some sort of analysis failure.
--   We exclude any terminal nodes here, since it is expected that a terminal
--   node might not have any return paths.
getOrphanedReturns ::
  PairGraph sym arch ->
  Set (NodeReturn arch)
getOrphanedReturns gr = do
  let rets = (Map.keysSet (pairGraphReturnVectors gr)) Set.\\ (pairGraphTerminalNodes gr)  
  Set.filter (\ret -> not (Map.member (ReturnNode ret) (pairGraphDomains gr))) rets


-- | After computing the dataflow fixpoint, examine the generated
--   error reports to determine an overall verdict for the programs.
pairGraphComputeVerdict ::
  PairGraph sym arch ->
  EquivM sym arch PE.EquivalenceStatus
pairGraphComputeVerdict gr =
  if Map.null (pairGraphObservableReports gr) &&
     Map.null (pairGraphDesyncReports gr) &&
     Set.null (pairGraphGasExhausted gr) then
    return PE.Equivalent
  else
    return PE.Inequivalent
