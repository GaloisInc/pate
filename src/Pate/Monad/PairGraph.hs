{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- EquivM operations on a PairGraph
module Pate.Monad.PairGraph 
  ( withPG
  , withPG_
  , liftPG
  , evalPG
  , runPG
  , catchPG
  , liftEqM
  , liftEqM_
  , initializePairGraph
  , initialDomain
  , initialDomainSpec
  , getScopedCondition
  , runPendingActions
  , considerDesyncEvent
  , addLazyAction
  , queuePendingNodes
  ) where

import           Control.Monad.State.Strict
import           Control.Monad.Reader
-- needed for GHC 9.6
import           Control.Monad (foldM, forM_)
import qualified Control.Monad.IO.Unlift as IO
import           Data.Functor.Const
import           Data.Maybe (fromMaybe)

import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.Some

import           SemMC.Formula.Env (SomeSome(..))

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import           Pate.Monad
import           Pate.Verification.PairGraph
import qualified Pate.SimState as PS
import qualified Pate.PatchPair as PPa
import           Pate.TraceTree
import qualified Pate.Verification.AbstractDomain as PAD
import qualified Pate.Verification.Domain as PVD
import           Pate.Verification.PairGraph.Node
import qualified Pate.Equivalence.Condition as PEC
import qualified Data.Macaw.CFG as MM
import qualified Data.Map as Map
import qualified Pate.Equivalence.Error as PEE
import GHC.Stack (HasCallStack)


withPG :: 
  HasCallStack =>
  PairGraph sym arch -> 
  StateT (PairGraph sym arch) (EquivM_ sym arch) a ->
  EquivM sym arch (a, PairGraph sym arch)
withPG pg f = runStateT f pg 

withPG_ :: 
  HasCallStack =>
  PairGraph sym arch -> 
  StateT (PairGraph sym arch) (EquivM_ sym arch) a ->
  EquivM sym arch (PairGraph sym arch)
withPG_ pg f = execStateT f pg

liftPG :: HasCallStack => PairGraphM sym arch a -> StateT (PairGraph sym arch) (EquivM_ sym arch) a
liftPG f = do
  pg <- get
  case runPairGraphM pg f of
    Left err -> lift $ throwHere $ PEE.PairGraphError err
    Right (a,pg') -> do
      put pg'
      return a

evalPG :: HasCallStack => PairGraph sym arch -> PairGraphM sym arch a -> EquivM_ sym arch a
evalPG pg f = fst <$> runPG pg f

runPG :: HasCallStack => PairGraph sym arch -> PairGraphM sym arch a -> EquivM_ sym arch (a, PairGraph sym arch)
runPG pg f = case runPairGraphM pg f of
  Left err -> throwHere $ PEE.PairGraphError err
  Right a -> return a

catchPG :: HasCallStack => PairGraphM sym arch a -> StateT (PairGraph sym arch) (EquivM_ sym arch) (Maybe a)
catchPG f = do
  pg <- get
  case runPairGraphM pg f of
    Left{} -> return Nothing
    Right (a,pg') -> do
      put pg'
      return $ Just a

liftEqM_ :: 
  HasCallStack =>
  (PairGraph sym arch -> EquivM_ sym arch (PairGraph sym arch)) -> 
  StateT (PairGraph sym arch) (EquivM_ sym arch) ()
liftEqM_ f = liftEqM $ \pg -> ((),) <$> (f pg)

liftEqM :: 
  HasCallStack =>
  (PairGraph sym arch -> EquivM_ sym arch (a, PairGraph sym arch)) -> 
  StateT (PairGraph sym arch) (EquivM_ sym arch) a
liftEqM f = do
  s <- get
  (a, s') <- lift $ f s
  put s'
  return a

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

-- | If a program desync has not already be found
--   for this block pair, run the given action to check if there
--   currently is one.
considerDesyncEvent ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  NodeEntry arch ->
  (EquivM_ sym arch (Maybe (TotalityCounterexample (MM.ArchAddrWidth arch)), PairGraph sym arch)) ->
  EquivM sym arch (PairGraph sym arch)
considerDesyncEvent gr0 bPair action =
  (withPG gr0 $ liftPG $ getDesyncReport bPair) >>= \case
    -- we have already found observable event differences at this location, so skip the check
    (Just cex,gr) -> do
      withTracing @"totalityce" cex $ 
        emitWarning $ PEE.NonTotalBlockExits (nodeBlocks bPair)
      return gr
    (Nothing, gr) ->
      do (mcex, gr') <- action
         case mcex of
           Nothing  -> return gr'
           Just cex -> do
             withTracing @"totalityce" cex $ 
               emitWarning $ PEE.NonTotalBlockExits (nodeBlocks bPair)
             withPG_ gr $ liftPG $ addDesyncReport bPair cex


addLazyAction ::
  Ord k =>
  ActionQueueLens sym arch k f ->
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



-- | For any edges with pending actions, we need to ensure that the 'from' node is
--   queued so that the action is processed.
queuePendingNodes ::
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
queuePendingNodes pg0 = do
  priority <- currentPriority
  env <- ask
  withPG_ pg0 $ do
    edgeActs <- liftPG $ getPendingActions edgeActions
    nodeActs <- liftPG $ getPendingActions nodeActions
    refineActs <- liftPG $ getPendingActions refineActions
    let nodeActs' = 
          (map (\((from,_),acts) -> (from, map asSomeAct acts)) (Map.toList edgeActs))
          ++ (map (\(from,acts) -> (from, map asSomeAct acts)) (Map.toList nodeActs))
          ++ (map (\(from,acts) -> (from, map asSomeAct acts)) (Map.toList refineActs))
    queueActs <- liftPG $ getPendingActions queueActions
  
    forM_ (concat $ Map.elems queueActs) $ \(pactAction -> act) -> do
      liftEqM_ $ \pg -> maybeUpdate pg $ liftIO $ runLazyAction act (env, Some (Const ()), pg)
    
    forM_ nodeActs' $ \(from,acts) ->
      (liftIO $ someActionReady acts) >>= \case
        True -> liftPG $ modify $ queueNode (mkPriority PriorityHandleActions priority) from
        _ -> return ()
  where
    asSomeAct :: PendingAction sym arch f -> SomeSome LazyIOAction
    asSomeAct (pactAction -> act) = SomeSome act

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
  ActionQueueLens sym arch k f ->
  k ->
  f v ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
runPendingActions lens edge result pg0 = do
  env <- ask
  (didchange, pg1) <- withPG pg0 $ do
    actMap <- liftPG $ getPendingActions lens
    let actList = fromMaybe [] (Map.lookup edge actMap)
  
    let go :: [PendingAction sym arch f] -> PairGraph sym arch -> IO (Bool, PairGraph sym arch)
        go [] _pg' = return (False, _pg')
        go ((pactAction -> act):acts) pg' = runLazyAction act (env, Some result, pg') >>= \case
            Just pg'' -> (go acts pg'' >>= \(_,pg''') -> return (True, pg'''))
            Nothing -> go acts pg'
    liftEqM $ \pg -> liftIO $ go actList pg
  case didchange of
    True -> return $ Just pg1
    False -> return Nothing
