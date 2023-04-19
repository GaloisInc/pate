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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FunctionalDependencies #-}

module Pate.Verification.PairGraph
  ( Gas(..)
  , initialGas
  , PairGraph
  , maybeUpdate
  , AbstractDomain
  , initialDomain
  , initialDomainSpec
  , initializePairGraph
  , chooseWorkItem
  , hasWorkLeft
  , pairGraphWorklist
  , pairGraphObservableReports
  , popWorkItem
  , updateDomain
  , updateDomain'
  , dropWorkItem
  , addReturnVector
  , getReturnVectors
  , getEdgesFrom
  , freshDomain
  , initDomain
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
  , ConditionKind(..)
  , PropagateKind(..)
  , getCondition
  , getScopedCondition
  , setCondition
  , dropCondition
  , nextPropagate
  , dropDomain
  , dropReturns
  , dropPostDomains
  , markEdge
  , getSyncPoint
  , asSyncPoint
  , getBackEdgesFrom
  , setSyncPoint
  , getCombinedSyncPoint
  , combineNodes
  , NodePriority(..)
  , addToWorkList
  , getQueuedPriority
  , queueAncestors
  , queueNode
  , emptyWorkList
  , SyncPoint(..)
  , updateSyncPoint
  , singleNodeRepr
  , queuePendingAction
  , runPendingActions
  , queuePendingNodes
  --- FIXME: move this
  , TupleF
  , pattern TupleF2
  , pattern TupleF3
  , pattern TupleF4
  --
  , addLazyAction
  , edgeActions
  , nodeActions
  , refineActions
  , queueActions
  , getAllNodes
  , emptyPairGraph
  , DomainRefinementKind(..)
  , DomainRefinement(..)
  , addDomainRefinement
  , getNextDomainRefinement
  , conditionPrefix
  , conditionAction
  , conditionName
  , shouldPropagate
  , maybeUpdate'
  , hasSomeCondition
  , propagateOnce, getPropagationKind, propagateAction) where

import           Prettyprinter

import           Control.Monad (foldM)
import           Control.Monad.IO.Class
import qualified Control.Lens as L
import           Control.Lens ( (&), (.~), (^.), (%~) )
import           Data.Kind (Type)

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
import qualified Data.RevMap as RevMap
import           Data.RevMap (RevMap)

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
import Data.Parameterized (Some(..), Pair (..))
import Control.Applicative (Const(..))
import qualified Control.Monad.IO.Unlift as IO
import Pate.Solver (ValidSym)
import Control.Monad.Reader (local, MonadReader (ask))
import SemMC.Formula.Env (SomeSome(..))
import qualified Pate.Location as PL
import qualified Pate.ExprMappable as PEM

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
    --   This is a mapping from nodes to their queue priority.
  , pairGraphWorklist :: !(RevMap (GraphNode arch) NodePriority)
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
  , pairGraphObservableReports :: !(Map (NodeEntry arch) (ObservableCounterexample sym arch))

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
    -- | These are conditions that are intended to be sufficient to imply
    --   equality (i.e. to yield a stronger equivalence domain than can be proven),
    --   or to imply subsequent conditions on descendant nodes.
  , pairGraphConditions :: !(Map (GraphNode arch, ConditionKind) (PropagateKind, PEC.EquivConditionSpec sym arch))
    -- | Any edges that have been followed at any point (which may later become infeasible
    -- due to further analysis)
  , pairGraphEdges :: !(Map (GraphNode arch) (Set (GraphNode arch)))
    -- | Reverse map of the above (from descendants to ancestors)
  , pairGraphBackEdges :: !(Map (GraphNode arch) (Set (GraphNode arch)))
    -- | Mapping from singleton nodes to their "synchronization" point, representing
    --   the case where two independent program analysis steps have occurred and now
    --   their control-flows have re-synchronized
  , pairGraphSyncPoints :: !(Map (GraphNode arch) (SyncPoint arch))
  , pairGraphPendingActs :: ActionQueue sym arch
  , pairGraphDomainRefinements ::
      !(Map (GraphNode arch) [DomainRefinement sym arch])
  }

data ConditionKind = 
    ConditionAsserted
  | ConditionAssumed
  -- ^ flag is true if this assumption should be propagated to ancestor nodes.
  --   After propagation, this is set to false so that it only propagates once.
  --   See 'nextCondition'
  | ConditionEquiv
  -- ^ a separate category for equivalence conditions, which should be shown
  --   to the user once the analysis is complete
  deriving (Eq,Ord, Enum, Bounded)

data PropagateKind =
    PropagateFull
  | PropagateOnce
  | PropagateNone
  deriving (Eq,Ord, Enum, Bounded)

propagateAction ::
  PropagateKind -> String
propagateAction = \case
  PropagateFull -> "fully"
  PropagateOnce -> "once"
  PropagateNone -> "never"

nextPropagate ::
  PropagateKind -> PropagateKind
nextPropagate = \case
  PropagateFull -> PropagateFull
  PropagateOnce -> PropagateNone
  PropagateNone -> PropagateNone

propagateOnce ::
  PropagateKind -> PropagateKind
propagateOnce = \case
  PropagateFull -> PropagateFull
  PropagateOnce -> PropagateOnce
  PropagateNone -> PropagateOnce


shouldPropagate :: PropagateKind -> Bool
shouldPropagate = \case
  PropagateNone -> False
  _ -> True

conditionPrefix :: ConditionKind -> String
conditionPrefix = \case
  ConditionAsserted{} -> "Asserted"
  ConditionAssumed{} -> "Assumed"
  ConditionEquiv{} -> "Equivalence Condition Assumed"

conditionName :: ConditionKind -> String
conditionName = \case
  ConditionAsserted{} -> "Assertion"
  ConditionAssumed{} -> "Assumption"
  ConditionEquiv{} -> "Equivalence Condition"

conditionAction :: ConditionKind -> String
conditionAction = \case
  ConditionAsserted{} -> "Assert"
  ConditionAssumed{} -> "Assume"
  ConditionEquiv{} -> "Assume (Equivalence Condition)"


data DomainRefinementKind =
    RefineUsingIntraBlockPaths
  | RefineUsingExactEquality



data DomainRefinement sym arch =
    LocationRefinement ConditionKind DomainRefinementKind (PL.SomeLocation sym arch -> Bool)
  | PruneBranch ConditionKind

addDomainRefinement ::
  GraphNode arch ->
  DomainRefinement sym arch ->
  PairGraph sym arch ->
  PairGraph sym arch
addDomainRefinement nd f pg0 = 
  let
    pg1 = pg0 { pairGraphDomainRefinements = Map.insertWith (++) nd [f] (pairGraphDomainRefinements pg0) }
  -- we need to re-process any nodes that have an outgoing edge here, since
  -- those are the domains we need to refine
  in queueAncestors (normalPriority PriorityUserRequest) nd pg1

getNextDomainRefinement ::
  GraphNode arch ->
  PairGraph sym arch ->
  Maybe (DomainRefinement sym arch, PairGraph sym arch)
getNextDomainRefinement nd pg = case Map.lookup nd (pairGraphDomainRefinements pg) of
  Just (refine:rest) -> Just (refine, pg {pairGraphDomainRefinements = Map.insert nd rest (pairGraphDomainRefinements pg)})
  _ -> Nothing

-- FIXME: move this 
data PairF tp1 tp2 k = PairF (tp1 k) (tp2 k)

type family TupleF (t :: l) :: (k -> Type)
type instance TupleF '(a,b) = PairF a b
type instance TupleF '(a,b,c) = PairF a (PairF b c)
type instance TupleF '(a,b,c,d) = PairF a (PairF b (PairF c d))

pattern TupleF2 :: a k -> b k -> TupleF '(a,b) k
pattern TupleF2 a b = PairF a b

pattern TupleF3 :: a k -> b k -> c k -> TupleF '(a,b,c) k
pattern TupleF3 a b c = PairF a (PairF b c)

pattern TupleF4 :: a k -> b k -> c k -> d k -> TupleF '(a,b,c,d) k
pattern TupleF4 a b c d = PairF a (PairF b (PairF c d))

data PendingAction sym arch (f :: PS.VarScope -> Type) = 
  PendingAction { pactIdent :: Int, _pactAction :: LazyIOAction (EquivEnv sym arch, Some f, PairGraph sym arch) (PairGraph sym arch)}

-- TODO: After some refactoring I'm not sure if we actually need edge actions anymore, so this potentially can be simplified
data ActionQueue sym arch =
  ActionQueue 
    { _edgeActions :: Map (GraphNode arch, GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, PS.SimBundle sym arch, AbstractDomain sym arch, AbstractDomain sym arch))]
    , _nodeActions :: Map (GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, PS.SimBundle sym arch, AbstractDomain sym arch))]
    , _refineActions :: Map (GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, AbstractDomain sym arch))]
    , _queueActions :: Map () [PendingAction sym arch (Const ())]
    , _latestPendingId :: Int
    }


data SyncPoint arch =
  SyncPoint { syncNodes :: PPa.PatchPairC (GraphNode arch) }

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
  , pairGraphWorklist = RevMap.empty
  , pairGraphReturnVectors = mempty
  , pairGraphObservableReports = mempty
  , pairGraphDesyncReports = mempty
  , pairGraphGasExhausted = mempty
  , pairGraphMiscAnalysisErrors = mempty
  , pairGraphExtraEdges = mempty
  , pairGraphTerminalNodes = mempty
  , pairGraphConditions = mempty
  , pairGraphEdges = mempty
  , pairGraphBackEdges = mempty
  , pairGraphSyncPoints = mempty
  , pairGraphPendingActs = ActionQueue Map.empty Map.empty Map.empty Map.empty 0
  , pairGraphDomainRefinements = mempty
  }

maybeUpdate ::
  Monad m =>
  a -> 
  m (Maybe a) ->
  m a
maybeUpdate gr f = f >>= \case
  Just gr' -> return gr'
  Nothing -> return gr

maybeUpdate' ::
  Monad m =>
  a -> 
  m (Maybe a) ->
  m (Bool, a)
maybeUpdate' gr f = f >>= \case
  Just gr' -> return (True, gr')
  Nothing -> return (False, gr)

getAllNodes :: PairGraph sym arch -> [GraphNode arch]
getAllNodes pg = Map.keys (pairGraphDomains pg)

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

dropObservableReports ::
  GraphNode arch ->
  PairGraph sym arch ->
  PairGraph sym arch
dropObservableReports (GraphNode ne) pg = pg { pairGraphObservableReports = Map.delete ne (pairGraphObservableReports pg) }
dropObservableReports (ReturnNode{}) pg = pg

dropReturns ::
  NodeReturn arch -> 
  PairGraph sym arch ->
  PairGraph sym arch
dropReturns nr pg = pg { pairGraphReturnVectors = Map.delete nr (pairGraphReturnVectors pg) }

-- | Delete the abstract domain for all outgoing nodes from this node
--   May potentially delete this node if there are back-edges.
dropPostDomains ::
  GraphNode arch ->
  NodePriority ->
  PairGraph sym arch ->
  PairGraph sym arch   
dropPostDomains nd priority pg = dropObservableReports nd $ Set.foldl' (\pg_ nd' -> dropDomain nd' priority pg_) pg (getEdgesFrom pg nd)

dropDomainRefinement ::
  GraphNode arch -> 
  PairGraph sym arch ->
  PairGraph sym arch
dropDomainRefinement nd pg = pg { pairGraphDomainRefinements = Map.delete nd (pairGraphDomainRefinements pg)}

-- | Delete the abstract domain for the given node, following
--   any reachable edges and discarding those domains as well
--   This is necessary if a domain is "narrowed": i.e. it moves
--   from assuming fewer equalities to assuming more equalities.
--   Marks any ancestors as requiring re-analysis
dropDomain ::
  GraphNode arch ->
  NodePriority ->
  PairGraph sym arch ->
  PairGraph sym arch 
dropDomain nd priority pg = case getCurrentDomain pg nd of
  Just{}->
    let
      -- clear this domain and all descendant domains
      pg' = case Set.null (getBackEdgesFrom pg nd) of
        -- don't drop the domain for a toplevel entrypoint, but mark it for
        -- re-analysis
        True -> pg { pairGraphWorklist = RevMap.insertWith (min) nd priority (pairGraphWorklist pg) }
        False -> pg { pairGraphDomains = Map.delete nd (pairGraphDomains pg), 
                      pairGraphWorklist = RevMap.delete nd (pairGraphWorklist pg)
                    }
      pg'' = Set.foldl' (\pg_ nd' -> dropDomain nd' priority pg_) pg' (getEdgesFrom pg nd)
      pg3 = dropObservableReports nd pg''
      -- mark all ancestors as requiring re-processing
    in queueNode priority nd pg3
  Nothing -> pg

{-
queueEntryPoints :: NodePriority -> PairGraph sym arch -> PairGraph sym arch
queueEntryPoints priority pg = 
  where
    go nd = case Set.minView (Map.keysSet (pairGraphDomains pg)) of
  
  Just (nd,_) -> 
-}


queueAncestors :: NodePriority -> GraphNode arch -> PairGraph sym arch -> PairGraph sym arch
queueAncestors priority nd pg = 
  snd $ Set.foldr (queueNode' priority) (Set.singleton nd, pg) (getBackEdgesFrom pg nd)

queueNode :: NodePriority -> GraphNode arch -> PairGraph sym arch -> PairGraph sym arch
queueNode priority nd__ pg__ = snd $ queueNode' priority nd__ (Set.empty, pg__)

-- | Adds a node to the work list. If it doesn't have a domain, queue its ancestors.
--   Takes a set of nodes that have already been considerd, and returns all considered nodes
queueNode' :: NodePriority -> GraphNode arch -> (Set (GraphNode arch), PairGraph sym arch) -> (Set (GraphNode arch), PairGraph sym arch)
queueNode' priority nd_ (considered, pg_) = case Set.member nd_ considered of
  True -> (considered, pg_)
  False -> case addToWorkList nd_ priority pg_ of
    Just pg' -> (Set.insert nd_ considered, pg')
    -- if this node has no defined domain (i.e it was dropped as part of the previous
    -- step) then we consider further ancestors
    Nothing -> Set.foldr' (queueNode' priority) (Set.insert nd_ considered, pg_) (getBackEdgesFrom pg_ nd_)

getCondition ::
  PairGraph sym arch ->
  GraphNode arch ->
  ConditionKind ->
  Maybe (PEC.EquivConditionSpec sym arch)
getCondition pg nd condK = fmap snd $ Map.lookup (nd, condK) (pairGraphConditions pg)

getPropagationKind ::
  PairGraph sym arch ->
  GraphNode arch ->
  ConditionKind ->
  PropagateKind
getPropagationKind _ _ ConditionAsserted = PropagateFull
getPropagationKind pg nd condK = 
  fromMaybe PropagateNone $ fmap fst $ Map.lookup (nd, condK) (pairGraphConditions pg)

hasSomeCondition :: PairGraph sym arch -> GraphNode arch -> Bool
hasSomeCondition pg nd = any (\condK -> isJust $ getCondition pg nd condK) [minBound..maxBound]

getScopedCondition ::
  PS.SimScope sym arch v ->
  PairGraph sym arch ->
  GraphNode arch ->
  ConditionKind ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
getScopedCondition scope pg nd condK = withSym $ \sym -> case getCondition pg nd condK of
  Just condSpec -> do
    (_, eqCond) <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) condSpec
    return eqCond
  Nothing -> return $ PEC.universal sym

setCondition :: 
  GraphNode arch ->
  ConditionKind ->
  PropagateKind ->
  PEC.EquivConditionSpec sym arch ->
  PairGraph sym arch ->
  PairGraph sym arch
setCondition nd condK propK cond pg = pg { pairGraphConditions = Map.insert (nd,condK) (propK, cond) (pairGraphConditions pg) }

dropCondition ::
  GraphNode arch ->
  ConditionKind ->
  PairGraph sym arch ->
  PairGraph sym arch
dropCondition nd condK pg = pg { pairGraphConditions = Map.delete (nd,condK) (pairGraphConditions pg) }

-- | If an observable counterexample has not already been found
--   for this block pair, run the given action to check if there
--   currently is one.
considerObservableEvent :: Monad m =>
  PairGraph sym arch ->
  NodeEntry arch ->
  (m (Maybe (ObservableCounterexample sym arch), PairGraph sym arch)) ->
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
           let gr1 = freshDomain gr node (normalPriority PriorityUserRequest) rootDom
           return $ emptyReturnVector gr1 (rootReturn fnPair) 


popWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  GraphNode arch ->
  (PairGraph sym arch, GraphNode arch, AbstractDomainSpec sym arch)
popWorkItem gr nd = case Map.lookup nd (pairGraphDomains gr) of
  Nothing -> panic Verifier "popWorkItem" ["Could not find domain corresponding to block pair", show nd]
  Just d  -> 
    let wl = RevMap.delete nd (pairGraphWorklist gr)
    in (gr{ pairGraphWorklist = wl }, nd, d)

-- | Drop the given node from the work queue if it is queued.
--   Otherwise do nothing.
dropWorkItem ::
  PA.ValidArch arch =>
  GraphNode arch ->
  PairGraph sym arch ->
  PairGraph sym arch
dropWorkItem nd gr = gr { pairGraphWorklist = RevMap.delete nd (pairGraphWorklist gr) }

hasWorkLeft ::
  PairGraph sym arch -> Bool
hasWorkLeft pg = case RevMap.minView_value (pairGraphWorklist pg) of
  Nothing -> False
  Just{} -> True

-- | Given a pair graph, chose the next node in the graph to visit
--   from the work list, updating the necessary bookeeping.  If the
--   work list is empty, return Nothing, indicating that we are done.
chooseWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  Maybe (NodePriority, PairGraph sym arch, GraphNode arch, AbstractDomainSpec sym arch)
chooseWorkItem gr =
  -- choose the smallest pair from the worklist. This is a pretty brain-dead
  -- heuristic.  Perhaps we should do something more clever.
  case RevMap.minView_value (pairGraphWorklist gr) of
    Nothing -> Nothing
    Just (nd, p, wl) -> case Map.lookup nd (pairGraphDomains gr) of
      Nothing -> panic Verifier "chooseWorkItem" ["Could not find domain corresponding to block pair", show nd]
      Just d  -> Just (p, gr{ pairGraphWorklist = wl }, nd, d)

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
  NodePriority {- ^ priority to add 'to' to the worklist -} ->
  Either (PairGraph sym arch) (PairGraph sym arch)
updateDomain gr pFrom pTo d priority
  | g > 0 = Right $ 
     (updateDomain' gr pFrom pTo d priority)
       { pairGraphGas = Map.insert (pFrom,pTo) (Gas (g-1)) (pairGraphGas gr)}

  | otherwise =
            Left $ markEdge pFrom pTo $ gr
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            }

  where
     -- Lookup the amount of remaining gas.  Initialize to a fresh value
     -- if it is not in the map
      Gas g = fromMaybe initialGas (Map.lookup (pFrom,pTo) (pairGraphGas gr))

-- | Update the abstract domain for the target graph node,
--   ignoring the gas parameter.
updateDomain' ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ point pair we are jumping from -} ->
  GraphNode arch {- ^ point pair we are jumping to -} ->
  AbstractDomainSpec sym arch {- ^ new domain value to insert -} ->
  NodePriority {- ^ priority to add 'to' to the worklist -} ->
  PairGraph sym arch
updateDomain' gr pFrom pTo d priority = markEdge pFrom pTo $ gr
  { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
  , pairGraphWorklist = RevMap.insertWith (min) pTo priority (pairGraphWorklist gr)
  , pairGraphEdges = Map.insertWith Set.union pFrom (Set.singleton pTo) (pairGraphEdges gr)
  , pairGraphBackEdges = Map.insertWith Set.union pTo (Set.singleton pFrom) (pairGraphBackEdges gr)
  }


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
  NodePriority {- ^ priority to queue the caller node -} -> 
  PairGraph sym arch
addReturnVector gr funPair retPair priority =
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

    wl = RevMap.insertWith (min) (ReturnNode funPair) priority (pairGraphWorklist gr)


getSyncPoint ::
  PairGraph sym arch ->
  PBi.WhichBinaryRepr bin ->
  GraphNode arch ->
  Maybe (GraphNode arch)
getSyncPoint gr bin nd = case Map.lookup nd (pairGraphSyncPoints gr) of
  Just (SyncPoint syncPair) -> PPa.getC bin syncPair
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
  sync@(SyncPoint syncPair) <- Map.lookup divergeNode (pairGraphSyncPoints pg)
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
  sync@(SyncPoint syncPair) <- Map.lookup ndDiv (pairGraphSyncPoints gr)
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
      Just (SyncPoint sp) -> do
        sp' <- PPa.update sp $ \bin' -> PPa.get bin' ndSync'
        return $ pg { pairGraphSyncPoints = Map.insert ndDiv (SyncPoint sp') (pairGraphSyncPoints pg) }
      Nothing -> do
        let sp = PPa.mkSingle bin (Const ndSync)
        return $ pg {pairGraphSyncPoints = Map.insert ndDiv (SyncPoint sp) (pairGraphSyncPoints pg) }

-- | Add a node back to the worklist to be re-analyzed if there is
--   an existing abstract domain for it. Otherwise return Nothing.
addToWorkList ::
  GraphNode arch ->
  NodePriority ->
  PairGraph sym arch ->
  Maybe (PairGraph sym arch)  
addToWorkList nd priority gr = case getCurrentDomain gr nd of
  Just{} -> Just $ gr { pairGraphWorklist = RevMap.insertWith (min) nd priority (pairGraphWorklist gr) }
  Nothing -> Nothing

getQueuedPriority ::
  GraphNode arch -> PairGraph sym arch -> Maybe NodePriority
getQueuedPriority nd pg = RevMap.lookup nd (pairGraphWorklist pg)

emptyWorkList :: PairGraph sym arch -> PairGraph sym arch
emptyWorkList pg = pg { pairGraphWorklist = RevMap.empty }

-- | Add an initial abstract domain value to a graph node, and
--   record it in the worklist to be visited.
freshDomain ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ point pair we are jumping to -} ->
  NodePriority {- ^ priority to queue the new node at -}  -> 
  AbstractDomainSpec sym arch {- ^ new domain value to insert -} ->
  PairGraph sym arch
freshDomain gr pTo priority d =
  gr{ pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
    , pairGraphWorklist = RevMap.insertWith (min) pTo priority (pairGraphWorklist gr)
    }

initDomain ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ point pair we are jumping from -} ->
  GraphNode arch {- ^ point pair we are jumping to -} ->
  NodePriority {- ^ priority to queue the new node at -}  -> 
  AbstractDomainSpec sym arch {- ^ new domain value to insert -} ->
  PairGraph sym arch  
initDomain gr pFrom pTo priority d = markEdge pFrom pTo (freshDomain gr pTo priority d)

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
    case filter (\(_,condK) -> case condK of {ConditionEquiv{} -> True; _ -> False}) (Map.keys (pairGraphConditions gr)) of
      [] -> return PE.Equivalent
      _ -> return PE.ConditionallyEquivalent
  else
    return PE.Inequivalent

$(L.makeLenses ''ActionQueue)

dropActId' ::
  Int ->
  ActionQueue sym arch ->
  ActionQueue sym arch
dropActId' actId (ActionQueue edgeActs nodeActs refineActs queueActs nextActId) = 
   ActionQueue 
    (fmap (filter (\pact -> actId /= (pactIdent pact))) edgeActs) 
    (fmap (filter (\pact -> actId /= (pactIdent pact))) nodeActs) 
    (fmap (filter (\pact -> actId /= (pactIdent pact))) refineActs)
    (fmap (filter (\pact -> actId /= (pactIdent pact))) queueActs) 
    nextActId

dropActId ::
  Int ->
  PairGraph sym arch ->
  PairGraph sym arch
dropActId actId pg = pg { pairGraphPendingActs = dropActId' actId (pairGraphPendingActs pg) }

addLazyAction ::
  Ord k =>
  L.Lens' (ActionQueue sym arch) (Map k [PendingAction sym arch f]) ->
  k ->
  PairGraph sym arch ->
  String ->
  (forall m'. Monad m' => ((String -> (forall v. (f v -> PairGraph sym arch -> EquivM_ sym arch (PairGraph sym arch))) -> m' ())) -> m' ()) ->
  EquivM sym arch (PairGraph sym arch)  
addLazyAction lens edge pg actNm f = do
  inIO <- IO.askRunInIO
  pendingAct <-
    chooseLazy @"()"  actNm $ \choice -> f (\nm act -> choice nm () (\(env, Some result, pg') -> inIO $ local (\_ -> env) $ act result pg'))
  liftIO $ queuePendingAction lens edge pendingAct pg

queuePendingAction ::
  Ord k =>
  L.Lens' (ActionQueue sym arch) (Map k [PendingAction sym arch f]) ->
  k ->
  (LazyIOAction (EquivEnv sym arch, Some f, PairGraph sym arch) (PairGraph sym arch)) ->
  PairGraph sym arch ->
  IO (PairGraph sym arch)
queuePendingAction lens edge (LazyIOAction actReady fn) pg = do
  let 
    actMap = (pairGraphPendingActs pg) ^. lens
    nextActId = (pairGraphPendingActs pg) ^. latestPendingId
    act' = PendingAction nextActId (LazyIOAction actReady (\(env, result, pg') -> fn (env, result, dropActId nextActId pg')))
    actMap' = Map.insertWith (++) edge [act'] actMap
    pendingActs = (pairGraphPendingActs pg) & lens .~ actMap'

  return $ pg { pairGraphPendingActs = (pendingActs & latestPendingId %~ (+ 1)) }


-- | For any edges with pending actions, we need to ensure that the 'from' node is
--   queued so that the action is processed.
queuePendingNodes ::
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
queuePendingNodes pg0 = do
  priority <- currentPriority
  let 
    edgeActs = (pairGraphPendingActs pg0) ^. edgeActions
    nodeActs = (pairGraphPendingActs pg0) ^. nodeActions
    refineActs = (pairGraphPendingActs pg0) ^. refineActions
    nodeActs' = 
      (map (\((from,_),acts) -> (from, map asSomeAct acts)) (Map.toList edgeActs))
      ++ (map (\(from,acts) -> (from, map asSomeAct acts)) (Map.toList nodeActs))
      ++ (map (\(from,acts) -> (from, map asSomeAct acts)) (Map.toList refineActs))
    queueActs = concat $ Map.elems $ (pairGraphPendingActs pg0) ^. queueActions
  
  env <- ask
  liftIO $ do
    pg1 <- foldM (\pg_ (PendingAction _ act) -> 
      maybeUpdate pg_ (runLazyAction act (env, Some (Const ()), pg_))) pg0 queueActs

    foldM (\pg_ (from,acts) -> someActionReady acts >>= \case
      True | Just pg__ <- addToWorkList from (mkPriority PriorityHandleActions priority) pg_ -> return pg__
      _ -> return pg_) pg1 nodeActs'
  where
    asSomeAct :: PendingAction sym arch f -> SomeSome LazyIOAction
    asSomeAct (PendingAction _ act) = SomeSome act

    someActionReady :: [SomeSome LazyIOAction] -> IO Bool
    someActionReady [] = return False
    someActionReady (SomeSome act:acts) = lazyActionReady act >>= \case
      True -> return True
      False-> someActionReady acts

-- | Run any pending actions for the given node or edge. Returns 'Nothing' if
--   no actions were run.
runPendingActions ::
  forall sym arch k f v.
  Ord k =>
  L.Lens' (ActionQueue sym arch) (Map k [PendingAction sym arch f]) ->
  k ->
  f v ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
runPendingActions lens edge result pg = do
  let actMap = (pairGraphPendingActs pg) ^. lens
  let actList = fromMaybe [] (Map.lookup edge actMap)
  env <- ask
  let go :: [PendingAction sym arch f] -> PairGraph sym arch -> IO (PairGraph sym arch,Bool)
      go [] _pg' = return (_pg', False)
      go (PendingAction _ act:acts) pg' = runLazyAction act (env, Some result, pg') >>= \case
        Just pg'' -> (go acts pg'' >>= \(pg''',_) -> return (pg''',True))
        Nothing -> go acts pg'
  (pg', didchange) <- liftIO $ go actList pg
  case didchange of
    True -> return $ Just pg'
    False -> return Nothing







