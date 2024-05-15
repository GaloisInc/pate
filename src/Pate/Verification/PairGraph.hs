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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Pate.Verification.PairGraph
  ( Gas(..)
  , initialGas
  , PairGraph
  , PairGraphM
  , runPairGraphM
  , execPairGraphM
  , evalPairGraphM
  , maybeUpdate
  , AbstractDomain
  , chooseWorkItem
  , hasWorkLeft
  , pairGraphWorklist
  , pairGraphObservableReports
  , updateDomain
  , updateDomain'
  , addReturnVector
  , getReturnVectors
  , getEdgesFrom
  , freshDomain
  , initDomain
  , getCurrentDomain
  , getCurrentDomainM
  , considerObservableEvent
  , addDesyncReport
  , getDesyncReport
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
  , setCondition
  , dropCondition
  , nextPropagate
  , dropDomain
  , dropReturns
  , dropPostDomains
  , markEdge
  , getBackEdgesFrom
  , getCombinedSyncPoints
  , combineNodes
  , NodePriority(..)
  , addToWorkList
  , WorkItem(ProcessNode)
  , pattern ProcessMerge
  , workItemNode
  , getQueuedPriority
  , queueAncestors
  , queueNode
  , emptyWorkList
  , SyncPoint
  , getSyncPoint
  , modifySyncPoint
  , syncMergeExitNodes
  , syncCutAddresses
  , syncExceptions
  , singleNodeRepr
  , edgeActions
  , nodeActions
  , refineActions
  , queueActions
  , ActionQueueLens
  , queuePendingAction
  , getPendingActions
  , PendingAction
  , pactAction
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
  , shouldAddPathCond
  , maybeUpdate'
  , hasSomeCondition
  , propagateOnce
  , getPropagationKind
  , propagateAction
  , addSyncAddress
  -- , filterSyncExits
  , pairGraphComputeVerdict
  -- FIXME: remove this and have modules import this directly
  , module Data.Parameterized.PairF
  , handleSingleSidedReturnTo
  , filterSyncExits
  , isDivergeNode
  , mkProcessMerge
  , dropWorkItem
  ) where

import           Prettyprinter

import           Control.Monad (guard, forM, forM_, filterM, unless)
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict (MonadState (..), modify, State, gets)
import           Control.Monad.Except (ExceptT, MonadError (..))
import           Control.Monad.Trans.Except (runExceptT)
import           Control.Monad.Trans.State.Strict (runState)

import qualified Control.Lens as L
import           Control.Lens ( (&), (.~), (^.), (%~) )
import           Data.Kind (Type)

import qualified Data.Foldable as F
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, catMaybes)
import           Data.Parameterized.Classes
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word (Word32)
import qualified Lumberjack as LJ

import           Data.Parameterized (Some(..), Pair (..))
import qualified Data.RevMap as RevMap
import           Data.RevMap (RevMap)

import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Equivalence as PE
import qualified Pate.Event as Event
import           Pate.Monad.Environment
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.SimState as PS


import           Pate.Verification.PairGraph.Node
import           Pate.Verification.StrongestPosts.CounterExample ( TotalityCounterexample(..), ObservableCounterexample(..) )

import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( AbstractDomain, AbstractDomainSpec )
import           Pate.TraceTree
import qualified Pate.Binary as PBi

import           Control.Applicative (Const(..), Alternative(..)) 

import qualified Pate.Location as PL
import qualified Pate.Address as PAd
import Data.Foldable (find)
import           Data.Parameterized.PairF
import           Data.Parameterized.SetF (SetF)
import qualified Data.Parameterized.SetF as SetF
import GHC.Stack (HasCallStack)

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
  , pairGraphWorklist :: !(WorkList arch)
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

type WorkList arch = RevMap (WorkItem arch) NodePriority

-- | Operations that can be a scheduled and handled
--   at the top-level.
data WorkItem arch = 
  -- | Handle all normal node processing logic
    ProcessNode (GraphNode arch)
  -- | Handle merging two single-sided analyses (both nodes must share a diverge point)
  | ProcessMergeCtor
      (SingleNodeEntry arch PBi.Original) 
      (SingleNodeEntry arch PBi.Patched)
  deriving (Eq, Ord)

-- Use mkProcessMerge as a partial smart constructor, but
-- export this pattern so we can match on it
pattern ProcessMerge :: SingleNodeEntry arch PBi.Original -> SingleNodeEntry arch PBi.Patched -> WorkItem arch
pattern ProcessMerge sneO sneP <- ProcessMergeCtor sneO sneP

{-# COMPLETE ProcessNode, ProcessMerge #-}

-- TODO: After some refactoring I'm not sure if we actually need edge actions anymore, so this potentially can be simplified
data ActionQueue sym arch =
  ActionQueue 
    { _edgeActions :: Map (GraphNode arch, GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, PS.SimBundle sym arch, AbstractDomain sym arch, AbstractDomain sym arch))]
    , _nodeActions :: Map (GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, PS.SimBundle sym arch, AbstractDomain sym arch))]
    , _refineActions :: Map (GraphNode arch) [PendingAction sym arch (TupleF '(PS.SimScope sym arch, AbstractDomain sym arch))]
    , _queueActions :: Map () [PendingAction sym arch (Const ())]
    , _latestPendingId :: Int
    }

data PendingAction sym arch (f :: PS.VarScope -> Type) = 
  PendingAction { pactIdent :: Int, pactAction :: LazyIOAction (EquivEnv sym arch, Some f, PairGraph sym arch) (PairGraph sym arch)}

data DomainRefinementKind =
    RefineUsingIntraBlockPaths
  | RefineUsingExactEquality

data DomainRefinement sym arch =
    LocationRefinement ConditionKind DomainRefinementKind (PL.SomeLocation sym arch -> Bool)
  | PruneBranch ConditionKind
  | AlignControlFlowRefinment ConditionKind

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
  | PropagateFullNoPaths
  | PropagateOnce
  | PropagateNone
  deriving (Eq,Ord, Enum, Bounded)

-- | Defines the data structure for tracking how to re-synchronize
--   control flow for a given diverge point.
--   Each diverge node yields two single-sided analyses, which
--   terminate (i.e. sync back with the normal two-sided analysis)
--   when they reach a defined sync point. A sync point is defined
--   as a single-sided GraphNode, paired with a "cut" address
--   indicating a particular exit from that node.
--   Cut addresses are provided at the start of the split analysis,
--   and the merge nodes are discovered during the single-sided analysis
--   when a node is determined to be able to exit to a cut point.
-- Note that, for a given divergence, we need to take the product
-- of Original sync point vs. every Patched sync point
-- In practice this is still reasonably small, since there are usually
-- only 2-3 cut addresses on each side (i.e. 4-9 merge cases to consider)
data SyncPoint arch =
  SyncPoint
    { 
      -- | During single-sided analysis, if we encounter an edge
      -- that ends in a cut point, we
      -- mark it here as a node that needs to be considered for merging
      _syncMergeExitNodes :: PPa.PatchPair (SetF (SingleNodeEntry arch))
      -- | Instruction addresses that, if reached during single-sided
      --   analysis (from the corresponding diverge point), 
      --   should trigger a merge back into a two-sided analysis
    , _syncCutAddresses :: PPa.PatchPair (SetF (PPa.WithBin (PAd.ConcreteAddress arch)))
      -- | Defines exceptions for exits that would otherwise be considered sync points.
      --   In these cases, the single-sided analysis continues instead, with the intention
      --   that another sync point is encountered after additional instructions are executed
    , _syncExceptions :: PPa.PatchPair (SetF (TupleF '(SingleNodeEntry arch, PB.BlockTarget arch)))
    }



instance Semigroup (SyncPoint arch) where
  (SyncPoint a1 b1 c1) <> (SyncPoint a2 b2 c2) = (SyncPoint (a1 <> a2) (b1 <> b2) (c1 <> c2))


instance Monoid (SyncPoint arch) where
  mempty = SyncPoint 
    (PPa.mkPair PBi.OriginalRepr SetF.empty SetF.empty) 
    (PPa.mkPair PBi.OriginalRepr SetF.empty SetF.empty) 
    (PPa.mkPair PBi.OriginalRepr SetF.empty SetF.empty) 

$(L.makeLenses ''SyncPoint)
$(L.makeLenses ''ActionQueue)

type ActionQueueLens sym arch k v = L.Lens' (ActionQueue sym arch) (Map k [PendingAction sym arch v])

getSyncPoint ::
  forall sym arch x bin.
  HasCallStack =>
  (OrdF x, Ord (x bin)) =>
  L.Lens' (SyncPoint arch) (PPa.PatchPair (SetF x)) ->
  PBi.WhichBinaryRepr bin ->
  GraphNode arch {- ^ The divergent node -}  ->
  PairGraphM sym arch (Set (x bin))
getSyncPoint lens bin nd = do
  sp <- lookupPairGraph @sym pairGraphSyncPoints nd
  let x = sp ^. lens
  -- should be redundant, but no harm in checking
  case PPa.get bin x of
    Just x' -> return $ SetF.toSet x'
    Nothing -> return Set.empty

modifySyncPoint ::
  forall sym arch x bin.
  HasCallStack =>
  (OrdF x, Ord (x bin)) =>
  L.Lens' (SyncPoint arch) (PPa.PatchPair (SetF x)) ->
  PBi.WhichBinaryRepr bin ->
  GraphNode arch -> 
  (Set (x bin) -> Set (x bin)) ->
  PairGraphM sym arch ()
modifySyncPoint lens bin dp f = do
  msp <- tryPG $ lookupPairGraph pairGraphSyncPoints dp
  let f' = \x -> SetF.fromSet (f (SetF.toSet x))
  let sp' = case msp of
        Nothing -> mempty & lens .~ (PPa.mkSingle bin (f' SetF.empty))
        Just sp -> sp & lens %~ 
          (\x -> PPa.set bin (f' $ fromMaybe SetF.empty (PPa.get bin x)) x)
  modify $ \pg -> 
    pg { pairGraphSyncPoints = Map.insert dp sp' (pairGraphSyncPoints pg)}

addToSyncPoint ::
  forall sym arch x bin.
  (OrdF x, Ord (x bin)) =>
  HasCallStack =>
  L.Lens' (SyncPoint arch) (PPa.PatchPair (SetF x)) ->
  PBi.WhichBinaryRepr bin ->
  GraphNode arch {- ^ The divergent node -}  ->
  x bin ->
  PairGraphM sym arch ()
addToSyncPoint lens bin nd x = modifySyncPoint lens bin nd (Set.insert x)

addSyncAddress ::
  forall sym arch bin.
  GraphNode arch {- ^ The divergent node -}  ->
  PBi.WhichBinaryRepr bin ->
  PAd.ConcreteAddress arch ->
  PairGraphM sym arch ()
addSyncAddress nd bin syncAddr = addToSyncPoint syncCutAddresses bin nd (PPa.WithBin bin syncAddr)

-- | Combine two single-sided nodes into a 'WorkItem' to process their
--   merge. Returns 'Nothing' if the two single-sided nodes have different
--   divergence points.
mkProcessMerge :: 
  SingleNodeEntry arch bin -> 
  SingleNodeEntry arch (PBi.OtherBinary bin) ->
  Maybe (WorkItem arch)
mkProcessMerge sne1 sne2 
  | dp1 <- singleNodeDivergePoint sne1
  , dp2 <- singleNodeDivergePoint sne2
  , dp1 == dp2 = case singleEntryBin sne1 of
    PBi.OriginalRepr -> Just $ ProcessMergeCtor sne1 sne2
    PBi.PatchedRepr -> Just $ ProcessMergeCtor sne2 sne1
mkProcessMerge _ _ = Nothing

workItemNode :: WorkItem arch -> GraphNode arch
workItemNode = \case
  ProcessNode nd -> nd
  ProcessMerge sneO sneP -> case combineSingleEntries sneO sneP of
    Just merged -> GraphNode merged
    Nothing -> panic Verifier "workItemNode" ["Unexpected mismatched single-sided nodes"]

newtype PairGraphM sym arch a = PairGraphT { unpgT :: ExceptT PEE.PairGraphErr (State (PairGraph sym arch)) a }
  deriving (Functor
           , Applicative
           , Monad
           , MonadState (PairGraph sym arch)
           , MonadError PEE.PairGraphErr
           )

instance PPa.PatchPairM (PairGraphM sym arch) where
  throwPairErr = throwError $ PEE.PairGraphErr "PatchPair"
  catchPairErr f hdl = catchError f $ \case
    PEE.PairGraphErr "PatchPair" -> hdl
    e -> throwError e

instance Alternative (PairGraphM sym arch) where
  a <|> b = catchError a $ \_ -> b
  empty = throwError $ PEE.PairGraphErr "No more alternatives"

instance MonadFail (PairGraphM sym arch) where
  fail msg = throwError $ PEE.PairGraphErr ("fail: " ++ msg)

runPairGraphM :: PairGraph sym arch -> PairGraphM sym arch a -> Either PEE.PairGraphErr (a, PairGraph sym arch)
runPairGraphM pg f = case runState (runExceptT (unpgT f)) pg of
  (Left err, _) -> Left err
  (Right a, pg') -> Right (a, pg')

execPairGraphM :: PairGraph sym arch -> PairGraphM sym arch a -> Either PEE.PairGraphErr (PairGraph sym arch)
execPairGraphM pg f  = case runPairGraphM pg f of
  Left err -> Left err
  Right (_,pg') -> Right pg'

evalPairGraphM :: PairGraph sym arch -> PairGraphM sym arch a -> Either PEE.PairGraphErr a
evalPairGraphM pg f  = case runPairGraphM pg f of
  Left err -> Left err
  Right (a,_) -> Right a

lookupPairGraph ::
  forall sym arch b.
  HasCallStack =>
  (PairGraph sym arch -> Map (GraphNode arch) b) -> 
  GraphNode arch ->
  PairGraphM sym arch b
lookupPairGraph f node = do
  m <- gets f
  pgMaybe "missing node entry" $ Map.lookup node m

propagateAction ::
  PropagateKind -> String
propagateAction = \case
  PropagateFull -> "fully"
  PropagateFullNoPaths -> "fully (no path conditions)"
  PropagateOnce -> "once"
  PropagateNone -> "never"

nextPropagate ::
  PropagateKind -> PropagateKind
nextPropagate = \case
  PropagateFull -> PropagateFull
  PropagateFullNoPaths -> PropagateFullNoPaths
  PropagateOnce -> PropagateNone
  PropagateNone -> PropagateNone

propagateOnce ::
  PropagateKind -> PropagateKind
propagateOnce = \case
  PropagateFull -> PropagateFull
  PropagateFullNoPaths -> PropagateFullNoPaths
  PropagateOnce -> PropagateOnce
  PropagateNone -> PropagateOnce


shouldAddPathCond :: PropagateKind -> Bool
shouldAddPathCond = \case
  PropagateFullNoPaths -> False
  _ -> True

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
  ConditionEquiv{} -> "Assume as equivalence condition"

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

getCurrentDomainM ::
  GraphNode arch ->
  PairGraphM sym arch (AbstractDomainSpec sym arch)
getCurrentDomainM nd = do
  pg <- get
  Just spec <- return $ getCurrentDomain pg nd
  return spec

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
        True -> pg { pairGraphWorklist = RevMap.insertWith (min) (ProcessNode nd) priority (pairGraphWorklist pg) }
        False -> pg { pairGraphDomains = Map.delete nd (pairGraphDomains pg), 
                      pairGraphWorklist = dropNodeFromWorkList nd (pairGraphWorklist pg)
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

-- | Calls 'queueNode' for 'ProcessNode' work items.
--   For 'ProcessMerge' work items, queues up the merge if
--   there exist domains for both single-sided nodes.
--   Otherwise, queues up the single-sided nodes with missing domains.
queueWorkItem :: NodePriority -> WorkItem arch -> PairGraph sym arch -> PairGraph sym arch
queueWorkItem priority wi pg = case wi of
  ProcessNode nd -> queueNode priority nd pg
  ProcessMerge sneO sneP -> 
    let 
      neO = GraphNode (singleToNodeEntry sneO)
      neP = GraphNode (singleToNodeEntry sneP)
    in case (getCurrentDomain pg neO, getCurrentDomain pg neP) of
      (Just{},Just{}) -> addItemToWorkList wi priority pg
      (Just{}, Nothing) -> queueNode priority neP pg
      (Nothing, Just{}) -> queueNode priority neO pg
      (Nothing, Nothing) -> 
        queueNode priority neP (queueNode priority neO pg)


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

addDesyncReport :: 
  NodeEntry arch -> 
  TotalityCounterexample (MM.ArchAddrWidth arch) ->
  PairGraphM sym arch ()
addDesyncReport bPair cex = 
  modify $ \pg -> pg{ pairGraphDesyncReports = Map.insert bPair cex (pairGraphDesyncReports pg) }

getDesyncReport ::
  NodeEntry arch -> 
  PairGraphM sym arch (Maybe (TotalityCounterexample (MM.ArchAddrWidth arch)))
getDesyncReport ne = do
  pg <- get
  return $ Map.lookup ne (pairGraphDesyncReports pg) 

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

-- | After computing the dataflow fixpoint, examine the generated
--   error reports to determine an overall verdict for the programs.
pairGraphComputeVerdict ::
  PairGraph sym arch ->
  PE.EquivalenceStatus
pairGraphComputeVerdict gr =
  if Map.null (pairGraphObservableReports gr) &&
     Map.null (pairGraphDesyncReports gr) &&
     Set.null (pairGraphGasExhausted gr) then
    case filter (\(_,condK) -> case condK of {ConditionEquiv{} -> True; _ -> False}) (Map.keys (pairGraphConditions gr)) of
      [] -> PE.Equivalent
      _ -> PE.ConditionallyEquivalent
  else
    PE.Inequivalent

-- | Drop the given node from the work queue if it is queued.
--   Otherwise do nothing.
dropNodeFromWorkList ::
  GraphNode arch ->
  WorkList arch ->
  WorkList arch
dropNodeFromWorkList nd wl = RevMap.filter (\wi _ -> workItemNode wi == nd) wl

hasWorkLeft ::
  PairGraph sym arch -> Bool
hasWorkLeft pg = case RevMap.minView_value (pairGraphWorklist pg) of
  Nothing -> False
  Just{} -> True

isDivergeNode ::
  GraphNode arch -> PairGraph sym arch -> Bool
isDivergeNode nd pg = Map.member nd (pairGraphSyncPoints pg)

-- | Given a pair graph, chose the next node in the graph to visit
--   from the work list, updating the necessary bookeeping.  If the
--   work list is empty, return Nothing, indicating that we are done.
chooseWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  Maybe (NodePriority, PairGraph sym arch, WorkItem arch)
chooseWorkItem gr = case runPairGraphM gr chooseWorkItem' of
  Left err -> panic Verifier "chooseWorkItem" ["Unexpected PairGraphM error", show err]
  Right (Just (np,wi),gr1) -> Just (np,gr1,wi)
  Right (Nothing, _) -> Nothing

chooseWorkItem' ::
  PA.ValidArch arch =>
  PairGraphM sym arch (Maybe (NodePriority, WorkItem arch))
chooseWorkItem' = do
  gr <- get
  case RevMap.minView_value (pairGraphWorklist gr) of
    Nothing -> return Nothing
    Just (wi, p, wl) -> do
      modify $ \gr_ -> gr_ { pairGraphWorklist = wl }
      case wi of
        ProcessNode (GraphNode ne) | Just (Some sne) <- asSingleNodeEntry ne -> do
          let bin = singleEntryBin sne
          let sne_addr = PB.concreteAddress $ singleNodeBlock sne
          (exceptEdges, _) <- getSingleNodeSync syncExceptions sne
          (cutAddrs, _) <- getSingleNodeSync syncCutAddresses sne
          let isCutAddr = SetF.member (PPa.WithBin bin sne_addr) cutAddrs
          let excepts = SetF.map (\(TupleF2 sne_ _) -> sne_) exceptEdges
          let isExcepted =  SetF.member sne excepts
          case (isCutAddr, isExcepted) of
            -- special case where we ignore single-sided nodes
            -- that are exactly at the cut point, since this should
            -- be handled as part of merging any nodes that reach this
            (True, False) -> chooseWorkItem'
            _ -> return $ Just (p,wi)
        -- FIXME: handle diverge node?
          
        _ -> return $ Just (p,wi)

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
  , pairGraphWorklist = RevMap.insertWith (min) (ProcessNode pTo) priority (pairGraphWorklist gr)
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

    wl = RevMap.insertWith (min) (ProcessNode (ReturnNode funPair)) priority (pairGraphWorklist gr)

pgMaybe :: String -> Maybe a -> PairGraphM sym arch a
pgMaybe _ (Just a) = return a
pgMaybe msg Nothing = throwError $ PEE.PairGraphErr msg

-- | Returns all discovered merge points from the given diverge point
getCombinedSyncPoints ::
  forall sym arch.
  HasCallStack =>
  GraphNode arch ->
  PairGraphM sym arch ([((SingleNodeEntry arch PBi.Original, SingleNodeEntry arch PBi.Patched), GraphNode arch)], SyncPoint arch)
getCombinedSyncPoints ndDiv = do
  sync@(SyncPoint syncSet _ _) <- lookupPairGraph @sym pairGraphSyncPoints ndDiv
  case syncSet of
    PPa.PatchPair ndsO ndsP -> do
      all_pairs <- forM (Set.toList $ Set.cartesianProduct (SetF.toSet ndsO) (SetF.toSet ndsP)) $ \(ndO, ndP) -> do
        combined <- pgMaybe "failed to combine nodes" $ combineNodes ndO ndP
        return $ ((ndO, ndP), combined)
      return (all_pairs, sync)
    _ -> return ([], sync)

-- | Compute a merged node for two diverging nodes
-- FIXME: do we need to support mismatched node kinds here?
combineNodes :: SingleNodeEntry arch bin -> SingleNodeEntry arch (PBi.OtherBinary bin) -> Maybe (GraphNode arch)
combineNodes node1 node2 = do
  let ndPair = PPa.mkPair (singleEntryBin node1) node1 node2
  nodeO <- PPa.get PBi.OriginalRepr ndPair
  nodeP <- PPa.get PBi.PatchedRepr ndPair
  -- it only makes sense to combine nodes that share a divergence point,
  -- where that divergence point will be used as the calling context for the
  -- merged point
  let divergeO = singleNodeDivergence nodeO
  let divergeP = singleNodeDivergence nodeP
  guard $ divergeO == divergeP
  return $ GraphNode $ mkMergedNodeEntry divergeO (singleNodeBlock nodeO) (singleNodeBlock nodeP)

singleNodeRepr :: GraphNode arch -> Maybe (Some (PBi.WhichBinaryRepr))
singleNodeRepr nd = case graphNodeBlocks nd of
  PPa.PatchPairSingle bin _ -> return $ Some bin
  PPa.PatchPair{} -> Nothing


tryPG :: PairGraphM sym arch a -> PairGraphM sym arch (Maybe a)
tryPG f = catchError (Just <$> f) (\_ -> return Nothing)


-- | Retrive the 'SyncPoint' fields corresponding to
--   the divergence point of the given single-sided node
getSingleNodeSync ::
  forall sym arch x bin.
  HasCallStack =>
  L.Lens' (SyncPoint arch) (PPa.PatchPair x) ->
  SingleNodeEntry arch bin ->
  PairGraphM sym arch (x bin, x (PBi.OtherBinary bin))
getSingleNodeSync lens sne = do
  let bin = singleEntryBin sne
  let nd = singleNodeDivergePoint sne 
  sp <- lookupPairGraph @sym pairGraphSyncPoints nd
  let x = sp ^. lens
  v1 <- PPa.get bin x
  v2 <- PPa.get (PBi.flipRepr bin) x
  return (v1, v2)



-- | Add a node back to the worklist to be re-analyzed if there is
--   an existing abstract domain for it. Otherwise return Nothing.
addToWorkList ::
  GraphNode arch ->
  NodePriority ->
  PairGraph sym arch ->
  Maybe (PairGraph sym arch)  
addToWorkList nd priority gr = case getCurrentDomain gr nd of
  Just{} -> Just $ addItemToWorkList (ProcessNode nd) priority gr
  Nothing -> Nothing

-- | Add a work item to the worklist to be processed
addItemToWorkList ::
  WorkItem arch ->
  NodePriority ->
  PairGraph sym arch ->
  PairGraph sym arch
addItemToWorkList wi priority gr = gr { pairGraphWorklist = RevMap.insertWith (min) wi priority (pairGraphWorklist gr) }

-- | Drop a work item. Should only be used in cases where we are certain
--   the work item is going to be handled after it is dropped.
dropWorkItem ::
  WorkItem arch ->
  PairGraph sym arch ->
  PairGraph sym arch
dropWorkItem wi gr = gr { pairGraphWorklist = RevMap.delete wi (pairGraphWorklist gr) }

-- | Return the priority of the given 'GraphNode' if it is queued for
--   normal processing
getQueuedPriority ::
  GraphNode arch -> PairGraph sym arch -> Maybe NodePriority
getQueuedPriority nd pg = RevMap.lookup (ProcessNode nd) (pairGraphWorklist pg)

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
    , pairGraphWorklist = RevMap.insertWith (min) (ProcessNode pTo) priority (pairGraphWorklist gr)
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

queuePendingAction ::
  Ord k =>
  ActionQueueLens sym arch k f ->
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

getPendingActions ::
  ActionQueueLens sym arch k f ->
  PairGraphM sym arch (Map k [PendingAction sym arch f])
getPendingActions lens = do
  pg <- get
  return $ (pairGraphPendingActs pg) ^. lens


isSyncExit :: 
  SingleNodeEntry arch bin ->
  PB.BlockTarget arch bin ->
  PairGraphM sym arch (Maybe (PB.ConcreteBlock arch bin))
isSyncExit sne blkt@(PB.BlockTarget{}) = do
  let dp = singleNodeDivergePoint sne 
  let bin = singleEntryBin sne
  cuts <- getSyncPoint syncCutAddresses bin dp
  excepts <- getSyncPoint syncExceptions bin dp
  let isExcept = Set.member (TupleF2 sne blkt) excepts
  case (not isExcept) &&
    Set.member (PPa.WithBin bin (PB.targetRawPC blkt)) cuts of
      True -> return $ Just (PB.targetCall blkt)
      False -> return Nothing
isSyncExit _ _ = return Nothing


-- | Filter a list of reachable block exits to
--   only those that should be handled for the given 'WorkItem'
--   For a 'ProcessNode' item, this is all exits for a 
--   two-sided node and all non-merge exits for a single-sided node.
--   For a single-sided node, any merge exits are paired with all 
--   possible merge nodes from the other side of the analysis and
--   queued as a 'ProcessMerge' work item.
filterSyncExits ::
  (NodePriorityK -> NodePriority) -> 
  WorkItem arch ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  PairGraphM sym arch [PPa.PatchPair (PB.BlockTarget arch)]
filterSyncExits _ (ProcessNode (ReturnNode{})) _ = fail "Unexpected ReturnNode work item"
filterSyncExits _ (ProcessMerge sneO sneP) blktPairs = do
  let isSyncExitPair blktPair = do
        blktO <- PPa.get PBi.OriginalRepr blktPair
        blktP <- PPa.get PBi.PatchedRepr blktPair
        x <- isSyncExit sneO blktO
        y <- isSyncExit sneP blktP
        return $ isJust x && isJust y  
  filterM isSyncExitPair blktPairs
filterSyncExits priority (ProcessNode (GraphNode ne)) blktPairs = case asSingleNodeEntry ne of
  Nothing -> return blktPairs
  Just (Some sne) -> do
    let dp = singleNodeDivergePoint sne
    let bin = singleEntryBin sne
    blkts <- mapM (PPa.get bin) blktPairs
    exitBlks <- catMaybes <$> mapM (isSyncExit sne) blkts
    unless (null exitBlks) $ do
      -- if any of the exits from this node are sync exits,
      -- then we need to queue up processing this node as
      -- a merge against all known merge points
      addToSyncPoint syncMergeExitNodes bin dp sne
      queueMerges priority sne
    return blktPairs

queueMerges ::
  (NodePriorityK -> NodePriority) -> 
  SingleNodeEntry arch bin -> 
  PairGraphM sym arch ()
queueMerges priority sne = do
  let dp = singleNodeDivergePoint sne
  otherExits <- getSyncPoint syncMergeExitNodes (PBi.flipRepr (singleEntryBin sne)) dp
  forM_ otherExits $ \otherExit -> do
    wi <- pgMaybe "unexpected node merge failure" $ mkProcessMerge sne otherExit
    modify $ queueWorkItem (priority PriorityHandleMerge) wi

-- | This handles the special case where the sync point
--   is the return site for a function.
--   This will be handled specially
handleSingleSidedReturnTo ::
  (NodePriorityK -> NodePriority) -> 
  NodeEntry arch ->
  PairGraphM sym arch ()
handleSingleSidedReturnTo priority ne = case asSingleNodeEntry ne of
  Just (Some sne) -> do
    let bin = singleEntryBin sne
    let dp = singleNodeDivergePoint sne
    syncAddrs <- getSyncPoint syncCutAddresses bin dp
    let blk = singleNodeBlock sne
    case Set.member (PPa.WithBin bin (PB.concreteAddress blk)) syncAddrs of
      True -> do
        addToSyncPoint syncMergeExitNodes bin dp sne
        queueMerges priority sne
      False -> return ()
  Nothing -> return ()