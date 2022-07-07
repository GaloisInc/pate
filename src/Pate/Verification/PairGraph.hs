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

module Pate.Verification.PairGraph
  ( Gas(..)
  , initialGas
  , PairGraph
  , AbstractDomain
  , initialDomain
  , initialDomainSpec
  , initializePairGraph
  , chooseWorkItem
  , updateDomain
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
import           Data.Text (Text)
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
import qualified Pate.SimState as PS

import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.Validity as PVV

import           Pate.Verification.PairGraph.Node ( GraphNode(..) )
import           Pate.Verification.StrongestPosts.CounterExample ( TotalityCounterexample(..), ObservableCounterexample(..) )

import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( AbstractDomain, AbstractDomainSpec )

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
  , pairGraphReturnVectors :: !(Map (PPa.FunPair arch) (Set (PPa.BlockPair arch)))

    -- TODO, I'm not entirely sure I love this idea of tracking error conditions in this
    -- data structure like this.  It works for now, but maybe is worth thinking about some more.
    -- Because of the monotonicity of the system, results can be reported as soon as they are
    -- discovered, so perhaps they should be streamed directly to output somehow.

    -- TODO, maybe this is the right place to include conditional equivalence conditions?

    -- | If we find a counterexample regarding observables in a particular block, record it here.
    --   Later, this can be used to generate reports to the user.  We also avoid checking for
    --   additional counterexamples for the given block if we have already found one.
  , pairGraphObservableReports :: !(Map (PPa.BlockPair arch) (ObservableCounterexample sym (MM.ArchAddrWidth arch)))

    -- | If we find a counterexample to the exit totality check, record it here.  This occurs when
    --   the programs have sufficiently-different control flow that they cannot be synchronized, or
    --   when the analysis encounters some control-flow construct it doesn't know how to handle.
    --   Once we find a desynchronization error for a particular block, we do not look for additional
    --   involving that same block.
  , pairGraphDesyncReports :: !(Map (PPa.BlockPair arch) (TotalityCounterexample (MM.ArchAddrWidth arch)))

    -- | Keep track of the target nodes whenever we run out of gas while trying to reach fixpoint.
    --   This can be used to report to the user instances where the analysis may be incomplete.
  , pairGraphGasExhausted :: !(Set (GraphNode arch))

    -- | Other sorts of analysis errors not captured by the previous categories. These generally
    --   arise from things like incompleteness of the SMT solvers, or other unexpected situations
    --   that may impact the soundness of the analysis.
  , pairGraphMiscAnalysisErrors :: !(Map (GraphNode arch) (Set Text))
  }

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
         , PS.viewSpecBody ad $ \ad' -> indent 4 (PAD.ppAbstractDomain ppPred ad')
         ]
  | (pPair, ad) <- Map.toList (pairGraphDomains gr)
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
  }

-- | Given a pair graph and a function pair, return the set of all
--   the sites we have encountered so far where this function may return to.
getReturnVectors ::
  PairGraph sym arch ->
  PPa.FunPair arch ->
  Set (PPa.BlockPair arch)
getReturnVectors gr fPair =
  fromMaybe mempty (Map.lookup fPair (pairGraphReturnVectors gr))

-- | Look up the current abstract domain for the given graph node.
getCurrentDomain ::
  PairGraph sym arch ->
  GraphNode arch ->
  Maybe (AbstractDomainSpec sym arch)
getCurrentDomain pg nd = Map.lookup nd (pairGraphDomains pg)

-- | If an observable counterexample has not already been found
--   for this block pair, run the given action to check if there
--   currently is one.
considerObservableEvent :: Monad m =>
  PairGraph sym arch ->
  PPa.BlockPair arch ->
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
  PairGraph sym arch ->
  PPa.BlockPair arch ->
  (m (Maybe (TotalityCounterexample (MM.ArchAddrWidth arch)), PairGraph sym arch)) ->
  m (PairGraph sym arch)
considerDesyncEvent gr bPair action =
  case Map.lookup bPair (pairGraphDesyncReports gr) of
    -- we have already found observable event differences at this location, so skip the check
    Just _ -> return gr
    Nothing ->
      do (mcex, gr') <- action
         case mcex of
           Nothing  -> return gr'
           Just cex -> return gr'{ pairGraphDesyncReports = Map.insert bPair cex (pairGraphDesyncReports gr) }

-- | Record an error that occured during analysis that doesn't fall into one of the
--   other, more structured, types of errors.
recordMiscAnalysisError ::
  PairGraph sym arch ->
  GraphNode arch ->
  Text ->
  PairGraph sym arch
recordMiscAnalysisError gr nd msg =
  let m = Map.alter f nd (pairGraphMiscAnalysisErrors gr)
      f Nothing  = Just (Set.singleton msg)
      f (Just s) = Just (Set.insert msg s)
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
initialDomain = withSym $ \sym -> return $ PAD.AbstractDomain (PVD.universalDomain sym) (PPa.PatchPair PAD.emptyDomainVals PAD.emptyDomainVals)

initialDomainSpec ::
  forall sym arch.
  GraphNode arch ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
initialDomainSpec node = withFreshVars blocks $ \vars ->
    withAssumptionFrame (PVV.validInitState mBlocks (PS.simVarState $ PPa.pOriginal vars) (PS.simVarState $ PPa.pPatched vars)) $ initialDomain
  where
    -- We don't want to pass a 'PPa.BlockPair' to 'PVV.validInitState' for a return edge,
    -- as this creates unwanted assertions about the final value of the instruction pointer.
    mBlocks :: Maybe (PPa.BlockPair arch)
    mBlocks = case node of
      GraphNode b -> Just b
      ReturnNode{} -> Nothing

    blocks :: PPa.BlockPair arch
    blocks = case node of
      GraphNode b -> b
      ReturnNode fPair -> TF.fmapF PB.functionEntryToConcreteBlock fPair

-- | Given a list of top-level function entry points to analyse,
--   initialize a pair graph with default abstract domains for those
--   entry points and add them to the work list.
initializePairGraph :: forall sym arch.
  [PPa.FunPair arch] ->
  EquivM sym arch (PairGraph sym arch)
initializePairGraph pPairs = foldM (\x y -> initPair x y) emptyPairGraph pPairs
  where
    initPair :: PairGraph sym arch -> PPa.FunPair arch -> EquivM sym arch (PairGraph sym arch)
    initPair gr fnPair =
      do let bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair
         withPair bPair $ do
           -- initial state of the pair graph: choose the universal domain that equates as much as possible
           idom <- initialDomainSpec (GraphNode bPair)
           return (freshDomain gr (GraphNode bPair) idom)

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
    Just (nd, wl) ->
      case Map.lookup nd (pairGraphDomains gr) of
        Nothing -> panic Verifier "choseWorkItem" ["Could not find domain corresponding to block pair", show nd]
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
  | g > 0 = Right gr
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            , pairGraphGas      = Map.insert (pFrom,pTo) (Gas (g-1)) (pairGraphGas gr)
            , pairGraphWorklist = Set.insert pTo (pairGraphWorklist gr)
            }

  | otherwise =
            Left gr
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            }

  where
     -- Lookup the amount of remaining gas.  Initialize to a fresh value
     -- if it is not in the map
      Gas g = fromMaybe initialGas (Map.lookup (pFrom,pTo) (pairGraphGas gr))


-- | When we encounter a function call, record where the function
--   returns to so that we can correctly propagate abstract domain
--   information from function returns to their call sites.
addReturnVector ::
  PairGraph sym arch ->
  PPa.FunPair arch {- ^ The function being called -}  ->
  PPa.BlockPair arch {- ^ The program point where it returns to -} ->
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
