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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

module Pate.Verification.Widening
  ( widenAlongEdge
  , WidenLocs(..)
  , getObservableEvents
  -- TODO move these?
  , refineEquivalenceDomain
  , updateEquivCondition
  , pruneCurrentBranch
  , addRefinementChoice
  , traceEqCond
  , InteractiveBundle(..)
  , getSomeGroundTrace
  , getTraceFromModel
  , addToEquivCondition
  , strengthenPredicate
  , getTraceFootprint
  , propagateCondition
  , propagateOne
  , getEquivPostCondition
  , PropagateCase(..)
  ) where

import           GHC.Stack
import           Control.Lens ( (.~), (&), (^.), (%~) )
import           Control.Monad (when, forM_, unless, filterM, foldM, void, forM)
import           Control.Monad.IO.Class
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Writer (tell, execWriterT)
import qualified Control.Monad.Reader as CMR
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Class ( lift )

import           Prettyprinter

import qualified Data.BitVector.Sized as BVS
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.List (foldl', (\\), nub)
import           Data.Maybe (mapMaybe, catMaybes)
import           Data.Parameterized.Classes()
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import qualified Data.Text.Lazy.Encoding as Text
import qualified Data.Text.Encoding.Error as Text

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import           What4.SatResult (SatResult(..))
import qualified What4.Concrete as W4C

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MT

import           Pate.Panic
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Location as PL
import qualified Pate.MemCell as PMc
import           Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Equivalence.EquivalenceDomain as PEE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemoryDomain as PEMd
import qualified Pate.ExprMappable as PEM
import qualified Pate.Solver as PSo
import qualified Pate.Verification.Simplify as PSi
import qualified Pate.TraceConstraint as PTC

import           Pate.Monad
import           Pate.Monad.PairGraph
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.EventTrace as ET

import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Config as PC
import qualified Pate.TraceCollection as PTc

import           Pate.Verification.PairGraph
import qualified Pate.Verification.ConditionalEquiv as PVC
import qualified Pate.Verification.Validity as PVV
import           Pate.Verification.PairGraph.Node ( GraphNode, GraphNode'(..), pattern GraphNodeEntry, pattern GraphNodeReturn, nodeFuns, graphNodeBlocks, asSingleNode, singleNodeDivergence, singleNodeDivergePoint, singleNodeRepr, isSingleNode )
import qualified Pate.Verification.StrongestPosts.CounterExample as CE

import qualified Pate.AssumptionSet as PAs
import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( WidenLocs(..) )
import           Pate.TraceTree
import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S

import Lang.Crucible.Simulator.SymSequence
import qualified Pate.Monad.Context as PMC
import Data.Functor.Const (Const(..))
import Pate.Verification.Concretize (symbolicFromConcrete)
import qualified Pate.Arch as PA
import Data.Parameterized (Pair(..))
import Data.Kind (Type)
import qualified Data.Aeson as JSON
import qualified Prettyprinter as PP
import qualified What4.Expr.GroundEval as W4
import qualified Lang.Crucible.Utils.MuxTree as MT
import Pate.Verification.Domain (universalDomain)
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.IORef as IO
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Quant as Qu
import qualified Pate.Verification.FnBindings as PFn
import Control.Monad.State (modify)

-- | Generate a fresh abstract domain value for the given graph node.
--   This should represent the most information we can ever possibly
--   have (i.e., all values are equal) as it will only ever be
--   weakend via widening.
makeFreshAbstractDomain ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  GraphNode arch {- ^ source node -} ->
  GraphNode arch {- ^ target graph node -} ->
  EquivM sym arch (PAD.AbstractDomain sym arch v)
makeFreshAbstractDomain scope bundle preDom from to = withTracing @"debug" "makeFreshAbstractDomain" $ do
  case from of
    -- graph node
    GraphNodeEntry{} -> startTimer $ do
      initDom <- initialDomain
      vals <- getInitalAbsDomainVals to bundle preDom
      evSeq <- getEventSequence to scope bundle preDom
      return $ initDom { PAD.absDomVals = vals, PAD.absDomEvents = evSeq }
    -- return node
    GraphNodeReturn{} -> do
      initDom <- initialDomain
      -- as a small optimization, we know that the return nodes leave the values
      -- unmodified, and therefore any previously-established value constraints
      -- will still hold
      evSeq <- getEventSequence to scope bundle preDom
      return $ initDom { PAD.absDomVals = PAD.absDomVals preDom
                       , PAD.absDomEvents = evSeq
                       }


getEquivPostCondition ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  GraphNode arch {- ^ target -} ->
  ConditionKind ->
  PairGraph sym arch ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
getEquivPostCondition scope bundle to condK gr = withSym $ \sym -> do
  -- this is the equivalence condition that this outgoing node is going to assume
  -- on its pre-state, so we can assume it for our post-state
  -- FIXME: as part of the propagation strategy we need to make sure that
  -- this condition is *implied* by the 'from' equivalence condition and equivalence domain
  let outVars = PS.bundleOutVars scope bundle
  case getCondition gr to condK of
    Just condSpec -> liftIO $ PS.bindSpec sym outVars condSpec
    Nothing -> return $ PEC.universal sym

extractPtrs ::
  PSo.ValidSym sym =>
  CLM.LLVMPtr sym w1 ->
  CLM.LLVMPtr sym w2 ->
  [Some (W4.SymExpr sym)]
extractPtrs (CLM.LLVMPointer region1 off1) (CLM.LLVMPointer region2 off2) =
  [Some (W4.natToIntegerPure region1), Some off1, Some (W4.natToIntegerPure region2), Some off2]

-- Compute a stronger condition that implies the current one using
-- intra-expression analysis
strengthenCondition ::
  forall sym arch v.
  PEC.EquivalenceCondition sym arch v ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
strengthenCondition cond = withSym $ \sym -> do
  PL.traverseLocation @sym @arch sym cond $ \loc p -> do
    p' <- strengthenPredicate [Some p] p
    return $ (PL.getLoc loc, p')

strengthenPredicate ::
  forall sym arch.
  [Some (W4.SymExpr sym)] ->
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
strengthenPredicate values_ eqPred = withSym $ \sym -> do
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  emitTraceLabel @"expr" "input" (Some eqPred)
  isPredTrue' goalTimeout eqPred >>= \case
    True -> return $ W4.truePred sym
    False -> do
      values <- Set.fromList <$> mapM (\(Some e) -> Some <$> ((liftIO (WEH.stripAnnotations sym e)) >>= (\x -> applyCurrentAsmsExpr x))) values_
      (eqPred', ptrAsms) <- PVV.collectPointerAssertions eqPred
      --let values = Set.singleton (Some eqPred')
      withAssumptionSet ptrAsms $ do
        cond1 <- PVC.computeEqCondition eqPred' values
        emitTraceLabel @"expr" "computeEqCondition" (Some cond1)
        cond2 <- PVC.weakenEqCondition cond1 eqPred' values
        emitTraceLabel @"expr" "weakenEqCondition" (Some cond2)
        cond3 <- PVC.checkAndMinimizeEqCondition cond2 eqPred
        emitTraceLabel @"expr" "checkAndMinimizeEqCondition" (Some cond3)
        goalSat "computeEquivCondition" cond3 $ \case
          Sat{} -> return cond3
          _ -> do
            emitWarning $ PEE.UnsatisfiableEquivalenceCondition (PEE.SomeExpr @_ @sym cond3)
            return $ W4.truePred sym

-- | TODO: formally this should actually be a predicate, but we'll stick with
--   structural equivalence for now
isRefinedLoc :: RefineLocations sym arch v -> PL.Location sym arch nm k -> Bool
isRefinedLoc (RefineLocations locs) l = Set.member (PL.SomeLocation l) locs

computeEquivCondition ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ incoming predomain -} ->
  AbstractDomain sym arch v {- ^ resulting target postdomain -} ->
  RefineLocations sym arch v {- ^ filter for locations to force equal -} ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
computeEquivCondition scope bundle preD postD refine = withTracing @"debug" "computeEquivCondition" $ withSym $ \sym -> do
  eqCtx <- equivalenceContext
  emitTraceLabel @"domain" PAD.Postdomain (Some postD)
  let 
    (stO, stP) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState
    regsO = PS.simRegs stO
    regsP = PS.simRegs stP
    memO = PS.simMem stO
    memP = PS.simMem stP
  postD_eq' <- PL.traverseLocation @sym @arch sym (PAD.absDomEq postD) $ \loc p -> case isRefinedLoc refine loc of
    False -> return (PL.getLoc loc, p)
    -- modify postdomain to unconditionally include target locations
    True -> case loc of
      PL.Cell{} -> return $ (PL.getLoc loc, W4.falsePred sym)
      _ -> return $ (PL.getLoc loc, W4.truePred sym)
  
  eqCond <- liftIO $ PEq.getPostdomain sym scope bundle eqCtx (PAD.absDomEq preD) postD_eq'
  eqCond' <- applyCurrentAsms eqCond
  
  subTree @"loc" "Locations" $
    PEC.fromLocationTraversable @sym @arch sym eqCond' $ \loc eqPred -> case isRefinedLoc refine loc of
    -- irrelevant location
    False -> return $ W4.truePred sym
    True -> subTrace (PL.SomeLocation loc) $ do
      -- eqPred is the predicate asserting equality
      -- on this location, which already includes accesses to
      -- the relevant state elements. We only have to inspect this
      -- predicate in order to compute a sufficient predicate that
      -- implies it
      values_ <- case loc of
        PL.Register r -> do
          valO <- return $ PSR.macawRegValue (regsO ^. (MM.boundValue r))
          valP <- return $ PSR.macawRegValue (regsP ^. (MM.boundValue r))
          case PSR.macawRegRepr (regsO ^. (MM.boundValue r)) of
            CLM.LLVMPointerRepr{} -> return $ extractPtrs valO valP
            CT.BoolRepr -> return $ [Some valO, Some valP]
            _ -> return $ [Some eqPred]
        PL.Cell c -> do
          valO <- liftIO $ PMc.readMemCell sym memO c
          valP <- liftIO $ PMc.readMemCell sym memP c
          return $ extractPtrs valO valP
        PL.Unit -> return $ [Some eqPred]
        _ -> throwHere $ PEE.UnsupportedLocation 

      values <- mapM (\(Some e) -> Some <$> ((liftIO (WEH.stripAnnotations sym e)) >>= (\x -> applyCurrentAsmsExpr x))) values_

      strengthenPredicate values eqPred


-- | Updates the equivalence condition for the given node with the
--   given condition, assuming the current path condition
updateEquivCondition ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  ConditionKind ->
  Maybe PropagateKind ->
  PEC.EquivalenceCondition sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)  
updateEquivCondition scope nd condK mpropK cond gr = withSym $ \sym -> do
  let propK = case mpropK of
        Just _propK -> _propK
        Nothing -> getPropagationKind gr nd condK
  cond' <- case shouldAddPathCond propK of
    True -> do
      pathCond <- CMR.asks envPathCondition >>= PAs.toPred sym
      PEC.weaken sym pathCond cond
    False -> return cond
  eqCond <- getScopedCondition scope gr nd condK
  eqCond' <- PEC.merge sym cond' eqCond
  return $ setCondition nd condK propK (PS.mkSimSpec scope eqCond') gr

-- | Adds the given predicate to the equivalence condition for the given node
addToEquivCondition ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  ConditionKind ->
  W4.Pred sym {- predicate must adhere to the 'v' scope -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)    
addToEquivCondition scope nd condK condPred gr = withSym $ \sym -> do
  let eqCond = (PEC.universal sym) { PEC.eqCondExtraCond = PAs.NamedAsms $ PAs.fromPred condPred}
  eqCond' <- getScopedCondition scope gr nd condK 
  eqCond'' <- PEC.merge sym eqCond eqCond'
  let propK = getPropagationKind gr nd condK
  return $ setCondition nd condK propK (PS.mkSimSpec scope eqCond'') gr

pruneCurrentBranch ::
  PS.SimScope sym arch v ->
  (GraphNode arch,GraphNode arch) ->
  ConditionKind ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)     
pruneCurrentBranch scope (from,to) condK gr0 = withSym $ \sym -> do
  priority <- thisPriority
  let gr1 = gr0
  pathCond <- CMR.asks envPathCondition >>= PAs.toPred sym
  notPath <- liftIO $ W4.notPred sym pathCond
  gr2 <- addToEquivCondition scope from condK notPath gr1
  let propK = getPropagationKind gr1 from condK
  case shouldPropagate propK of
    True -> do
      return $ queueAncestors (priority PriorityPropagation) from $ 
        dropPostDomains from (priority PriorityDomainRefresh) (markEdge from to gr2)
    False -> return $ queueNode (priority PriorityNodeRecheck) from $
      dropPostDomains from (priority PriorityDomainRefresh) (markEdge from to gr2)

traceEqCond ::
  ConditionKind -> 
  PEC.EquivalenceCondition sym arch v ->
  EquivM sym arch ()
traceEqCond condK eqCond = withSym $ \sym -> do
  eqCond_pred <- PEC.toPred sym eqCond
  case W4.asConstantPred eqCond_pred of
    Just True -> return ()
    _ -> do
      let msg = conditionPrefix condK
      withTracing @"message" msg $ do
        emitTraceLabel @"eqcond" (PEE.someExpr sym eqCond_pred) (Some eqCond)

addEqDomRefinementChoice ::
  ConditionKind ->
  GraphNode arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
addEqDomRefinementChoice condK nd gr0 = do
  addLazyAction refineActions nd gr0 ("Add " ++ conditionName condK) $ \choice -> do
    let msg = conditionAction condK
    choice (msg ++ " condition") $ \(TupleF2 scope preD) gr1 -> do
      locFilter <- refineEquivalenceDomain preD
      return $ addDomainRefinement nd (LocationRefinement condK RefineUsingExactEquality (PS.mkSimSpec scope locFilter)) gr1
    choice (msg ++ " condition (using intra-block path conditions)") $ \(TupleF2 scope preD) gr1 -> do
      locFilter <- refineEquivalenceDomain preD
      return $ addDomainRefinement nd (LocationRefinement condK RefineUsingIntraBlockPaths (PS.mkSimSpec scope locFilter)) gr1
    choice (msg ++ " that branch is infeasible") $ \_ gr1 ->
      return $ addDomainRefinement nd (PruneBranch condK) gr1



addPropagationChoice ::
  ConditionKind ->
  GraphNode arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
addPropagationChoice condK nd gr0 = do
  addLazyAction queueActions () gr0 ("Propagate " ++ (conditionName condK) ++ "s") $ \choice -> do
    let go propK = do
          choice ("Propagate " ++ (propagateAction propK)) $ \_ gr3 -> withSym $ \sym -> do
            priority <- thisPriority
            case getCondition gr3 nd condK of
              Just eqCondSpec -> PS.viewSpec eqCondSpec $ \scope eqCond -> do
                eqCond_propagate <- getScopedCondition scope gr3 nd condK
                eqCond' <- PEC.merge sym eqCond eqCond_propagate
                gr4 <- return $ setCondition nd condK propK (PS.mkSimSpec scope eqCond') gr3
                return $ queueAncestors (priority PriorityUserRequest) nd gr4
              Nothing -> do
                emitTrace @"message" ("No " ++  conditionName condK ++ " found")
                return gr3
    mapM_ go [PropagateOnce,PropagateFull,PropagateFullNoPaths]

data InteractiveBundle sym arch =
  forall v. InteractiveBundle 
    { iScope :: PS.SimScope sym arch v
    , iBundle :: PS.SimBundle sym arch v
    , iNode :: GraphNode arch
    , iPairGraph :: PairGraph sym arch
    , iDom :: PAD.AbstractDomain sym arch v
    , iCond :: Map.Map ConditionKind (PEC.EquivalenceCondition sym arch v)
    , iEnv :: EquivEnv sym arch
    }

instance PA.ValidArch arch => IsTraceNode '(sym :: Type,arch :: Type) "interactiveBundle" where
  type TraceNodeType '(sym,arch) "interactiveBundle" = InteractiveBundle sym arch
  prettyNode () b = "Interactive Bundle For: " <> pretty (iNode b)
  nodeTags = mkTags @'(sym,arch) @"interactiveBundle" [Summary, Simplified]

-- | Deferred decision about whether or not the domain for this node should be refined
addRefinementChoice ::
  GraphNode arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
addRefinementChoice nd gr0 = withTracing @"message" ("Modify Proof Node: " ++ show nd) $ do
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- only assertions are propagated by default
  gr1 <- foldM (\gr_ condK -> addEqDomRefinementChoice condK nd gr_) gr0 
    [minBound..maxBound]
  gr2 <- addLazyAction nodeActions nd gr1 "Post-process conditions?" $ \choice -> do
    choice "Interactive" $ \(TupleF3 scope bundle d) gr2 -> withSym $ \sym -> do
      env <- CMR.ask
      let conds = Map.fromList $ mapMaybe (\condK -> case getCondition gr2 nd condK of {Just eqSpec -> Just (condK, eqSpec); Nothing -> Nothing}) [minBound..maxBound]

      conds' <- mapM (\spec -> (liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) spec)) conds
      let b = InteractiveBundle scope bundle nd gr2 d conds' env
      -- TODO: allow updates here
      emitTrace @"interactiveBundle" b
      return gr2
    choice "Strengthen conditions" $ \(TupleF3 scope bundle d) gr2 -> withSym $ \sym -> do
      let go condK gr0_ = case getCondition gr0_ nd condK of
            Just eqCondSpec -> withTracing @"message" (conditionName condK) $ withSym $ \sym -> do
              eqCond <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) eqCondSpec
              eqCond' <- strengthenCondition eqCond
              priority <- thisPriority
              let propK = getPropagationKind gr0_ nd condK
              return $ queueAncestors (priority PriorityPropagation) nd $ setCondition nd condK propK (PS.mkSimSpec scope eqCond') gr0_
            Nothing -> return gr0_
      foldM (\gr_ condK -> go condK gr_) gr2 [minBound..maxBound]

    choice "Simplify conditions" $ \(TupleF3 scope _bundle _) gr2 -> do
      let go condK gr0_ = case getCondition gr0_ nd condK of
            Just eqCondSpec -> withTracing @"message" (conditionName condK) $ withSym $ \sym -> do
              eqCond <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) eqCondSpec
              eqCond_pred <- PEC.toPred sym eqCond
              emitTraceLabel @"eqcond" (PEE.someExpr sym eqCond_pred) (Some eqCond)
              meqCond_pred' <- isPredTrue' goalTimeout eqCond_pred >>= \case
                True -> do
                  emitTrace @"message" (conditionName condK ++ " Discharged")
                  return Nothing
                False -> do
                  curAsm <- currentAsm
                  emitTrace @"assumption" curAsm
                  eqCond_pred_simp <- PSi.applySimpStrategy PSi.deepPredicateSimplifier eqCond_pred
                  emitTraceLabel @"expr" (ExprLabel $ "Simplified " ++ conditionName condK) (Some eqCond_pred_simp)
                  return $ Just eqCond_pred_simp
              case meqCond_pred' of
                Nothing -> return $ dropCondition nd condK gr0_
                Just eqCond_pred' -> do
                  let eqCond' = (PEC.universal sym) { PEC.eqCondExtraCond = PAs.NamedAsms $ PAs.fromPred eqCond_pred'}
                  priority <- thisPriority
                  let propK = getPropagationKind gr0_ nd condK
                  return $ queueAncestors (priority PriorityPropagation) nd $ setCondition nd condK propK (PS.mkSimSpec scope eqCond') gr0_
            Nothing -> do
              emitTrace @"message" ("No " ++  conditionName condK ++ " found")
              return gr0_
      foldM (\gr_ condK -> go condK gr_) gr2 [minBound..maxBound]

  gr3 <- foldM (\gr_ condK -> addPropagationChoice condK nd gr_) gr2
    [ConditionAssumed,ConditionEquiv]

  addLazyAction queueActions () gr3 "Re-process proof node?" $ \choice -> do
      choice "Re-check node" $ \_ gr4 -> do
        priority <- thisPriority
        return $ queueNode (priority PriorityUserRequest) nd gr4
      choice "Drop and re-compute equivalence domain" $ \_ gr4 -> do
        priority <- thisPriority
        return $ queueAncestors (priority PriorityUserRequest) nd $ dropDomain nd (priority PriorityDomainRefresh) gr4
      choice "Clear work list (unsafe!)" $ \_ gr4 ->
        return $ emptyWorkList gr4

-- | Predicates which we attempt to assume when generating a model, but raise
--   the corresponding warning when this is not possible.
type WeakAssumptions sym arch = [(W4.Pred sym, Maybe (PEE.InnerEquivalenceError arch))]

-- | Given a predicate 'p', call the given continuation 'f'
--   with a model where a maximal subset of the given 'WeakAssumptions' are also
--   satisfied.
--   If 'p' is not satisfiable (or inconclusive) on its own then the given assumptions are ignored,
--   and 'f' is called with the result of checking just 'p' (either 'Unsat' or 'Unknown').
tryWithAsms ::
  forall sym arch a.
  WeakAssumptions sym arch ->
  W4.Pred sym ->
  (SatResult (SymGroundEvalFn sym) () -> EquivM_ sym arch a) ->
  EquivM sym arch a
tryWithAsms asms_ p f = do
  -- NOTE: we avoid 'withSatAssumption' here since that's somewhat more
  -- expensive than just 'goalSat', and we'd prefer to fail quickly
  mresult <- goalSat "check" p $ \case
    Unsat () -> Just <$> f (Unsat ())
    Unknown -> Just <$> f Unknown
    -- ideally we could just call 'go asms_' from here directly,
    -- but nested solver calls seem to break What4, so there's a
    -- bit of redundancy here
    Sat{} -> return Nothing
  case mresult of
    Just a -> return a
    Nothing -> withAssumption p $ go asms_
  where
    maybeEmit :: Maybe (PEE.InnerEquivalenceError arch) -> EquivM_ sym arch ()
    maybeEmit Nothing = return ()
    maybeEmit (Just err) = emitWarning err

    go ::
      [(W4.Pred sym, Maybe (PEE.InnerEquivalenceError arch))] ->
      EquivM_ sym arch a
    go [] = withSym $ \sym -> goalSat "go" (W4.truePred sym) f
    go [(asm, err)] = do
      mresult <- goalSat "go" asm $ \case
        Sat evalFn -> Just <$> f (Sat evalFn)
        Unsat () -> return Nothing
        Unknown -> return Nothing
      case mresult of
        Nothing -> maybeEmit err >> go []
        Just a -> return a
    go ((asm, err):asms) = do
      mresult <- withSatAssumption (PAs.fromPred asm) $ go asms
      case mresult of
        Nothing -> maybeEmit err >> go asms
        Just a -> return a

mkTraceAssumptions :: SimBundle sym arch v -> EquivM sym arch (WeakAssumptions sym arch)
mkTraceAssumptions bundle = withSym $ \sym -> do
  (_, ptrAsserts) <- PVV.collectPointerAssertions bundle
  stacks_zero <- PPa.catBins $ \bin -> do
    in_ <- PPa.get bin (PS.simIn bundle)
    let stackbase = PS.unSE $ PS.simStackBase (PS.simInState in_) 
    zero <- liftIO $ W4.bvLit sym CT.knownRepr (BVS.mkBV CT.knownRepr 0)
    PAs.fromPred <$> (liftIO $ W4.isEq sym zero stackbase)

  stacks_zero_pred <- PAs.toPred sym stacks_zero
  ptrAsserts_pred <- PAs.toPred sym ptrAsserts
  return $
    [ (stacks_zero_pred, Nothing )
    , (ptrAsserts_pred, Just PEE.RequiresInvalidPointerOps)
    ]

getSomeGroundTrace ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  Maybe (StatePostCondition sym arch v) ->
  EquivM sym arch (CE.TraceEvents sym arch)
getSomeGroundTrace scope bundle preD postCond = withSym $ \sym -> do
  trace_asms <- mkTraceAssumptions bundle
  tryWithAsms trace_asms (W4.truePred sym) $ \case
    Unsat{} -> throwHere PEE.InvalidSMTModel
    Unknown -> throwHere PEE.InconclusiveSAT
    Sat evalFn -> getTraceFromModel scope evalFn bundle preD postCond

getTraceFootprint ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  EquivM sym arch (PPa.PatchPairC (CE.TraceFootprint sym arch))
getTraceFootprint _scope bundle = withSym $ \sym -> PPa.forBinsC $ \bin -> do
    out <- PPa.get bin (PS.simOut bundle)
    in_ <- PPa.get bin (PS.simIn bundle)
    let in_regs = PS.simInRegs in_
    let rop = MT.RegOp (MM.regStateMap in_regs)
    let mem = PS.simOutMem out
    let s = (MT.memFullSeq @_ @arch mem)
    s' <- PEM.mapExpr sym concretizeWithSolver s
    liftIO $ CE.mkFootprint sym rop s'

-- | Compute a counter-example for a given predicate
getTraceFromModel ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  Maybe (StatePostCondition sym arch v) ->
  EquivM sym arch (CE.TraceEvents sym arch)
getTraceFromModel scope evalFn' bundle preD postCond = withSym $ \sym -> do
  ground_postCond <- PEM.mapExpr sym (concretizeWithModel evalFn') postCond
  let (pre_stO, pre_stP) = PS.asStatePair scope (simIn bundle) PS.simInState
  eqCtx <- equivalenceContext
  -- NB: we use eqDomPost here because we want a StatePostCondition, since
  -- that will include individual assertions on each location
  preCond <- liftIO $ eqDomPost sym pre_stO pre_stP eqCtx (PAD.absDomEq preD) (universalDomain sym)
  ground_preCond <- PEM.mapExpr sym (concretizeWithModel evalFn') preCond

  trace_pair <- PPa.forBins $ \bin -> do
    out <- PPa.get bin (PS.simOut bundle)
    in_ <- PPa.get bin (PS.simIn bundle)
    let mem = PS.simOutMem out
    withGroundEvalFn evalFn' $ \evalFn -> do
      evs <- CE.groundTraceEventSequence sym evalFn (MT.memFullSeq @_ @arch mem)
      let in_regs = PS.simInRegs in_
      ground_rop <- CE.groundRegOp sym evalFn (MT.RegOp (MM.regStateMap in_regs))
      -- create a dummy initial register op representing the initial values
      return $ CE.TraceEventsOne ground_rop evs
  return $ CE.TraceEvents trace_pair (Some ground_preCond) (fmap Some ground_postCond)

-- | Apply all existing domain refinements to the 'to' node by adding assertions/assumptions to
--   the 'from' node that are sufficient to imply the desired post-domain.
--   
--   NB: Previously this would remove the refinements afterwards, with the intention that the
--   added assertion was now sufficient to imply the desired domain. This is not the case
--   when there are multiple ancestors to 'to', as each ancestor will require its own assertion.
--   We can safely re-apply the refinements each time 'to' is reached, as this will be
--   effectively a no-op if a sufficient condition has already been added to 'from'.
applyDomainRefinements ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  (GraphNode arch,GraphNode arch) ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ pre-domain -} ->
  AbstractDomain sym arch v {- ^ post-domain -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)   
applyDomainRefinements scope (from,to) bundle preD postD gr0_ = fnTrace "applyDomainRefinements" $ go (getDomainRefinements to gr0_) gr0_
  where
    go :: 
      [DomainRefinement sym arch] -> 
      PairGraph sym arch -> 
      EquivM sym arch (PairGraph sym arch)
    go [] gr0 = do
      emitTrace @"debug" ("No refinements found for: " ++ show to)
      return gr0
    go (x:xs) gr1 = withSym $ \sym -> do
      let next = go xs
      case x of
        -- FIXME: unclear if this is reachable
        AlignControlFlowRefinment{} -> fail "applyDomainRefinements: NOT IMPLEMENTED AlignControlFlowRefinment"
        PruneBranch condK -> withTracing @"debug" ("Applying PruneBranch to " ++ show to) $ do
          gr2 <- pruneCurrentBranch scope (from,to) condK gr1
          next gr2

        LocationRefinement condK refineK refineSpec ->  withTracing @"debug" ("Applying LocationRefinement to " ++ show to) $ do
          -- refine the domain of the predecessor node and drop this domain
          refine <- IO.liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) refineSpec
          eqCond <- case refineK of
            RefineUsingIntraBlockPaths -> computeEquivCondition scope bundle preD postD refine
            RefineUsingExactEquality -> domainToEquivCondition scope bundle preD postD refine
          eqCond_pred <- PEC.toPred sym eqCond
          goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
          emitTraceLabel @"expr" "Generated Condition" (Some eqCond_pred)          
          isPredTrue' goalTimeout eqCond_pred >>= \case
            True -> do
              emitTrace @"debug" "Equivalence condition holds, no propagation needed"
              return gr1
            False -> do
              gr2 <- updateEquivCondition scope from condK Nothing eqCond gr1
              -- since its equivalence condition has been modified, we need to re-examine
              -- all outgoing edges from the predecessor node
              priority <- thisPriority
              gr3 <- return $ queueAncestors (priority PriorityPropagation) from $ 
                dropPostDomains from (priority PriorityDomainRefresh) (markEdge from to gr2)
              next gr3


-- | Unlike 'computeEquivCondition', this simply generates a trivial equivalence condition
--   that asserts the exact target equivalence domain refinement
domainToEquivCondition ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ pre-domain -} ->
  AbstractDomain sym arch v {- ^ post-domain -} ->
  RefineLocations sym arch v ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
domainToEquivCondition scope bundle preD postD refine = withSym $ \sym -> do
  postD_eq' <- PL.traverseLocation @sym @arch sym (PAD.absDomEq postD) $ \loc p -> case isRefinedLoc refine loc of
    False -> return (PL.getLoc loc, p)
    -- modify postdomain to unconditionally include target locations
    True -> case loc of
      PL.Cell{} -> return $ (PL.getLoc loc, W4.falsePred sym)
      _ -> return $ (PL.getLoc loc, W4.truePred sym)

  eqCtx <- equivalenceContext
  eqCond <- liftIO $ PEq.getPostdomain sym scope bundle eqCtx (PAD.absDomEq preD) postD_eq'
  
  PEC.fromLocationTraversable @sym @arch sym eqCond $ \loc eqPred -> case isRefinedLoc refine loc of
    False -> return $ W4.truePred sym
    True -> return eqPred

data PickManyChoice sym arch =
    forall tp. PickRegister (MM.ArchReg arch tp)
  | forall w. PickStack (PMc.MemCell sym arch w)
  | forall w. PickGlobal (PMc.MemCell sym arch w)
  | PickIncludeAllRegisters
  | PickIncludeAll
  | PickFinish

instance forall sym arch. (PSo.ValidSym sym, PA.ValidArch arch) => JSON.ToJSON (PickManyChoice sym arch) where
  -- FIXME: Needs more structure
  toJSON = \case
    PickRegister r -> JSON.object 
      [ "register" JSON..= case PA.fromRegisterDisplay (PA.displayRegister r) of
        Just s -> s
        Nothing -> MapF.showF r]
    PickStack s -> JSON.object [ "stack_cell" JSON..= show (pretty s)]
    PickGlobal s -> JSON.object [ "mem_cell" JSON..= show (pretty s)]
    PickIncludeAllRegisters -> JSON.String "all_registers"
    PickIncludeAll -> JSON.String "all"
    PickFinish -> JSON.String "finish"

data PickChoices sym arch = PickChoices
  { pickRegs :: [Some (MM.ArchReg arch)] 
  , pickStack :: [Some (PMc.MemCell sym arch)]
  , pickGlobal :: [Some (PMc.MemCell sym arch)]
  }

instance Semigroup (PickChoices sym arch) where
  (PickChoices a b c) <> (PickChoices a' b' c') = PickChoices (a <> a') (b <> b') (c <> c')

instance Monoid (PickChoices sym arch) where
  mempty = PickChoices [] [] []

instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "pickManyChoice" where
  type TraceNodeType '(sym,arch) "pickManyChoice" = PickManyChoice sym arch
  prettyNode () = \case
    PickRegister r -> case fmap pretty (PA.fromRegisterDisplay (PA.displayRegister r)) of
      Just s -> s
      Nothing -> pretty $ MapF.showF r
    PickStack c -> pretty c
    PickGlobal c -> pretty c
    PickIncludeAllRegisters -> "Include All Registers"
    PickIncludeAll -> "Include All Locations"
    PickFinish -> "Finish"
  nodeTags = mkTags @'(sym,arch) @"pickManyChoice" [Summary, Simplified]
  jsonNode _ = nodeToJSON @'(sym,arch) @"pickManyChoice"

pickMany ::
  PickChoices sym arch ->
  EquivM sym arch (PickChoices sym arch)
pickMany pickIn = go mempty pickIn
  where

    go :: 
      PickChoices sym arch ->
      PickChoices sym arch ->
      EquivM sym arch (PickChoices sym arch)
    go acc (PickChoices [] [] []) = return acc
    go acc remaining = do
      (acc', remaining') <- choose @"pickManyChoice" "Include Location:" $ \choice -> do
        choice "" PickIncludeAllRegisters $ return $ (acc <> (remaining { pickStack = [], pickGlobal = []}), mempty)
        choice "" PickIncludeAll $ return $ (acc <> remaining, mempty)
        choice "" PickFinish $ return $ (acc, mempty)

        forM_ (zip [0..] (pickRegs remaining)) $ \(idx, Some r) ->
          case PA.displayRegister r of
            PA.Normal{} -> choice "" (PickRegister r) $ do
              let (hd_,(_:tl_)) = splitAt idx (pickRegs remaining)
              return $ (mempty { pickRegs = [Some r] } <> acc, remaining { pickRegs = hd_++tl_ })
            -- in general we can include any register, but it likely
            -- makes sense to only consider registers that we have
            -- defined a pretty display for
            _ -> return ()
        forM_ (zip [0..] (pickStack remaining)) $ \(idx, Some c) -> do
          choice "" (PickStack c) $ do
            let (hd_,(_:tl_)) = splitAt idx (pickStack remaining)
            return $ (mempty { pickStack = [Some c] } <> acc, remaining { pickStack = hd_++tl_ })
        forM_ (zip [0..] (pickGlobal remaining)) $ \(idx, Some c) -> do
          choice "" (PickGlobal c) $ do
            let (hd_,(_:tl_)) = splitAt idx (pickGlobal remaining)
            return $ (mempty { pickGlobal = [Some c] } <> acc, remaining { pickGlobal = hd_++tl_ })

      go acc' remaining'

-- | Interactive refinement of an equivalence domain
--   (i.e. manually specifying locations as equal)
refineEquivalenceDomain ::
  forall sym arch v.
  AbstractDomain sym arch v ->
  EquivM sym arch (RefineLocations sym arch v)
refineEquivalenceDomain dom = withSym $ \sym -> do
  let regDom = PEE.eqDomainRegisters (PAD.absDomEq dom)
  let allRegs = map fst $ PER.toList (PER.universal sym)
  let abnormal = filter (\(Some r) -> case PA.displayRegister r of PA.Normal{} -> False; _ -> True) allRegs
  let excluded = filter (\(Some r) -> not (W4.asConstantPred (PER.registerInDomain sym r regDom) == Just True)) allRegs

  let excludedStack = map fst $ PEMd.toList $ PEE.eqDomainStackMemory (PAD.absDomEq dom)
  let excludedGlobal = map fst $ PEMd.toList $ PEE.eqDomainGlobalMemory (PAD.absDomEq dom)
  let pickIn = PickChoices
        { pickRegs = excluded \\ (abnormal ++ [(Some (MM.ip_reg @(MM.ArchReg arch)))])
        , pickStack = excludedStack
        , pickGlobal = excludedGlobal
        }

  picked <- pickMany pickIn

  let 
    regLocs = map (\(Some r) -> PL.SomeLocation (PL.Register r)) (pickRegs picked)
    stackLocs = map (\(Some c) -> PL.SomeLocation (PL.Cell c)) (pickStack picked)
    memLocs = map (\(Some c) -> PL.SomeLocation (PL.Cell c)) (pickGlobal picked)
  
  return $ RefineLocations (Set.fromList $ regLocs ++ stackLocs ++ memLocs)


-- | True if the satisfiability of the predicate only depends on
--   variables from the given binary
isEqCondSingleSided ::
  forall sym arch bin v.
  PS.SimScope sym arch v ->
  PB.BlockPair arch ->
  PBi.WhichBinaryRepr bin ->
  PEC.EquivalenceCondition sym arch v ->
  EquivM sym arch Bool
isEqCondSingleSided scope blks bin eqCond = withSym $ \sym -> do
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- rewrite the free variables for the other binary into arbitrary (free) terms and
  -- determine if the resulting predicate is equal to the original
  withFreshScope blks $ \(scope2 :: PS.SimScope sym arch v2) -> do
    (this_vars :: PS.SimVars sym arch v2 bin) <- PPa.get bin (PS.scopeVars (PS.unsafeCoerceScope scope))
    (vars2 :: PS.SimVars sym arch v2 (PBi.OtherBinary bin)) <- PPa.get (PBi.flipRepr bin) (PS.scopeVars scope2)

    PPa.PatchPair vars2O vars2P <- return $ PPa.mkPair bin this_vars vars2
    outer_to_inner <- liftIO $ PS.getScopeCoercion sym scope (vars2O,vars2P)
    eqCond2 <- liftIO $ PS.scopedExprMap sym eqCond (PS.applyScopeCoercion sym outer_to_inner)
    eqCond_pred <- PEC.toPred sym eqCond
    eqCond2_pred <- PEC.toPred sym eqCond2
    conds_eq <- liftIO $ W4.isEq sym eqCond_pred eqCond2_pred
    isPredTrue' goalTimeout conds_eq

-- FIXME: the scope of the path condition isn't explicitly
-- maintained, so we assume it here.
-- We could check if the predicate is well-scoped
scopedPathCondition ::
  PS.SimScope sym arch v ->
  EquivM sym arch (PS.ScopedExpr sym W4.BaseBoolType v)
scopedPathCondition _scope = withSym $ \sym -> do
  pathCond <- CMR.asks envPathCondition >>= PAs.toPred sym
  Some scopedPathCond <- return $ PS.mkScopedExpr pathCond
  return $ PS.unsafeCoerceScope scopedPathCond

propagateBindings ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
propagateBindings scope bundle from to gr0 = withSym $ \sym -> case (asSingleNode from,asSingleNode to) of
  (Just (Some (Qu.AsSingle fromS)), Just (Some (Qu.AsSingle toS))) ->
    case testEquality (singleNodeRepr fromS) (singleNodeRepr toS) of
      Nothing -> do
        fail $ "Unexpected mismatched single-sided nodes" ++ show from ++ " vs. " ++ show to
      Just Refl -> do
        let dp = singleNodeDivergePoint fromS
        unless (dp == singleNodeDivergePoint toS) $
          fail $ "Unexpected mismatched divergence points" ++ show from ++ "vs. " ++ show to
        case MapF.lookup (Qu.AsSingle toS) (gr0 ^. (syncData dp . syncBindings)) of
          -- no bindings to propagate, nothing to do
          Nothing -> do
            emitTrace @"debug" "No bindings to propagate"
            return Nothing
          -- 'to' node has defined bindings that need to be propagated
          Just (PS.AbsT toBindsSpec) -> do
            let outVars = PS.bundleOutVars scope bundle
            toBinds <- liftIO $ PS.bindSpec sym outVars toBindsSpec
            lookupFnBindings scope fromS gr0 >>= \case
              -- 'from' has existing binds so we check if we actually need to propagate
              -- FIXME: can we check this without the solver? do we need to check it?
              Just fromBinds -> do
                emitTrace @"debug" "Propagating and merging with existing bindings"
                fromBindsPred <- IO.liftIO $ PFn.toPred sym fromBinds
                withAssumption fromBindsPred $ do
                  toBindsPred <- IO.liftIO $ PFn.toPred sym toBinds
                  not_toBindsPred <- liftIO $ W4.notPred sym toBindsPred
                  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
                  isPredSat' goalTimeout not_toBindsPred >>= \case
                    Just False -> do
                      emitTraceLabel @"expr" (ExprLabel $ "Proved bindings") (Some toBindsPred)
                      return Nothing
                    _ -> withTracing @"message" "Fail to prove bindings" $ do
                      emitTraceLabel @"expr" (ExprLabel $ "To Bindings") (Some toBindsPred)
                      emitTraceLabel @"expr" (ExprLabel $ "From Bindings") (Some fromBindsPred)
                      -- FIXME: use 'addFnBindings' instead? needs to take a mux condition
                      pathCond <- scopedPathCondition scope
                      emitTraceLabel @"expr" (ExprLabel $ "Path Condition") (Some (PS.unSE pathCond))
                      bindsCombined <- IO.liftIO $ PFn.mux sym pathCond toBinds fromBinds
                      return $ Just $ gr0 & (syncData dp . syncBindings) %~ MapF.insert (Qu.AsSingle fromS) (PS.AbsT $ PS.mkSimSpec scope bindsCombined)
              -- 'from' has no binds so we propagate unconditionally
              Nothing -> do
                -- FIXME: do we care about the path condition here?
                emitTrace @"debug" "Propagating bindings"
                return $ Just $ gr0 & (syncData dp . syncBindings) %~ MapF.insert (Qu.AsSingle fromS) (PS.AbsT $ PS.mkSimSpec scope toBinds)
  _ -> do
    emitTrace @"debug" "Not a pair of single-sided nodes"
    return Nothing

data PropagateCase = 
    ConditionInfeasible -- ^ condition cannot be satisfied
  | ConditionNotPropagated
  | ConditionPropagated [ConditionKind] -- ^ condition was propagated, along with preconditions
  deriving (Eq, Ord, Show)

-- | True if the given 'PropagateCase' indicates that the 'PairGraph' was left unmodified.
propagateCaseNoop :: PropagateCase -> Bool
propagateCaseNoop = \case
  ConditionInfeasible -> False
  ConditionNotPropagated -> True
  ConditionPropagated{} -> False


-- | Propagate the given condition kind backwards (from 'to' node to 'from' node).
--   Does not do any other graph maintenance (i.e. dropping stale domains or re-queuing nodes).
--   Returns the resulting (possibly unmodified) PairGraph, with a 'PropagateCase' indicating
--   which case occured.
propagateOne ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  [ConditionKind] -> {- ^ weaken the propagated condition with assumptions -}
  AbstractDomain sym arch v -> {- ^ predomain -}
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  ConditionKind ->
  PairGraph sym arch ->
  EquivM sym arch (PropagateCase, PairGraph sym arch)
propagateOne scope bundle preconds preD from to condK gr0 = withSym $ \sym -> case getCondition gr0 to condK of
  Nothing -> do
    emitTrace @"debug" "No condition to propagate"
    return (ConditionNotPropagated, gr0)
  Just{} -> do
    -- take the condition of the target edge and bind it to
    -- the output state of the bundle
    -- weaken the result with any given preconditions
    cond_ <- getEquivPostCondition scope bundle to condK gr0


    simplifier <- PSi.mkSimplifier PSi.deepPredicateSimplifier
    cond <- PSi.applySimplifier simplifier cond_
        -- check if the "to" condition is already satisifed, otherwise
        -- we need to update our own condition
    cond_pred <- PEC.toPred sym cond

    goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
    mcond_res <- isPredSat' goalTimeout cond_pred
    mcheck_propagate <- case mcond_res of
      Just False -> do
        emitTrace @"message" "Condition is infeasible, dropping branch."
        gr1 <- pruneCurrentBranch scope (from,to) condK gr0
        return $ Just (ConditionInfeasible, gr1)
      _ -> case shouldPropagate (getPropagationKind gr0 to condK) of
        True -> return Nothing
        False -> do
          eqCtx <- equivalenceContext
          (postAsm_1:postAsms_rest) <- mapM (\condK_ -> getEquivPostCondition scope bundle to condK_ gr0) [minBound..maxBound]
          postAsm <- PEC.toPred sym =<< foldM (PEC.merge sym) postAsm_1 postAsms_rest

          eqPost_eq <- liftIO $ PEq.getPostdomain sym scope bundle eqCtx (PAD.absDomEq preD) (universalDomain sym)
          eqPost_pred <- IO.liftIO $ postCondPredicate sym eqPost_eq
          not_eqPost <- liftIO $ W4.notPred sym eqPost_pred
          (withSatAssumption (PAs.fromPred postAsm) $ isPredSat' goalTimeout not_eqPost) >>= \case
            Just (Just False) -> do
              -- post-domain assumes exact equality, so we stop propagating assumed conditions
              emitTrace @"debug" "Condition not propagated"
              return $ Just (ConditionNotPropagated, gr0)
            _ -> do
              withTracing @"debug" "Non-trivial equivalence post-domain:" $ 
                emitTrace @"expr" (Some eqPost_pred) 
              -- domain is non-trivial, so we propagate the assumption backwards since
              -- it may strengthen the condition
              return Nothing
    case mcheck_propagate of
      Just res -> return res
      Nothing -> do
        not_cond <- liftIO $ W4.notPred sym cond_pred
        isPredSat' goalTimeout not_cond >>= \case
          -- equivalence condition for this path holds, we 
          -- don't need any changes
          Just False -> do
            emitTraceLabel @"expr" (ExprLabel $ "Proven " ++ conditionName condK) (Some cond_pred) 
            return (ConditionNotPropagated, gr0)
          -- we need more assumptions for this condition to hold
          Just True -> do
            let go precondK = do
                  precond_ <- getEquivPostCondition scope bundle to precondK gr0
                  precond <- PSi.applySimplifier simplifier precond_
                  precondPred <- PEC.toPred sym precond
                  return (precondK, precond, precondPred)
            res <- mapM go preconds
            asms <- IO.liftIO $ foldM (\p (_,_,precondPred) -> W4.andPred sym p precondPred) (W4.truePred sym) res
            -- if we have any preconditions, check if this is provable with them, and
            -- propagate those conditions as well
            (used_preconds, gr1) <- case W4.asConstantPred asms of
              Just True -> return (Just [], gr0)
              _ -> (withAssumption asms $ isPredSat' goalTimeout not_cond) >>= \case
                Just False -> do
                  emitTraceLabel @"expr" (ExprLabel $ "Proven (with assumptions) " ++ conditionName condK) (Some cond_pred) 
                  return (Nothing, gr0)
                Just True -> do
                  withTracing @"message" "Propagating Assumptions" $ do
                    (used_preconds',gr1) <- withPG gr0 $ forM res $ \(precondK, precond, precondPred) -> do
                      case W4.asConstantPred precondPred of
                        Just True -> return Nothing
                        _ -> do
                          let propK = getPropagationKind gr0 to precondK
                          liftEqM_ $ updateEquivCondition scope from precondK (Just (nextPropagate propK)) precond
                          return $ Just precondK
                    return (Just (catMaybes used_preconds'), gr1)
                Nothing -> throwHere $ PEE.InconclusiveSAT
            case used_preconds of
              Nothing -> return (ConditionNotPropagated, gr1)
              Just used_preconds' -> do
                emitTraceLabel @"expr" (ExprLabel $ "Propagated  " ++ conditionName condK) (Some cond_pred)
                let propK = getPropagationKind gr1 to condK
                gr2 <- updateEquivCondition scope from condK (Just (nextPropagate propK)) cond gr1
                return $ (ConditionPropagated used_preconds', markEdge from to gr2)
          Nothing -> throwHere $ PEE.InconclusiveSAT



-- | Push an assertion back up the graph.
--   Returns 'Nothing' if there is nothing to do (i.e. no assertion or
--   existing assertion is already implied)
propagateCondition ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v -> {- ^ predomain -}
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  EquivM sym arch (PropagateCase, PairGraph sym arch)
propagateCondition scope bundle preD from to gr0 = fnTrace "propagateCondition" $ do
  priority <- thisPriority
  (pcases, gr1) <- go [] [ConditionAssumed, ConditionEquiv, ConditionAsserted] gr0
  let used = nub $ foldr (\pc used_ -> case pc of ConditionPropagated used' -> used_ ++ used'; _ -> used) [] pcases
  (pcase, gr2) <- withPG gr1 $ do
    let anyInfeasible = any ((==) ConditionInfeasible) pcases
    case anyInfeasible of
      True -> return ConditionInfeasible
      False -> liftPartEqM_ (propagateBindings scope bundle from to) >>= \case
        True -> do
          liftPG $ modify $ \gr_ -> 
            queueAncestors (priority PriorityPropagation) from (markEdge from to gr_)
          return $ ConditionPropagated used
        False -> case all propagateCaseNoop pcases of
          True -> return ConditionNotPropagated
          False -> do
            liftPG $ modify $ \gr_ -> 
              queueAncestors (priority PriorityPropagation) from $ 
              queueNode (priority PriorityNodeRecheck) from $ 
              dropPostDomains from (priority PriorityDomainRefresh) (markEdge from to gr_)
            
            return $ ConditionPropagated used

  -- When transitioning between single and two-sided analyses, we
  -- want to avoid propagating conditions implicitly during widening.
  -- Instead this happens explicitly during ProcessMerge or ProcessSplit, which
  -- manages all of the needed bookkeeping surrounding matching up variables
  -- from both sides of the analysis.
  case (isSingleNode from, isSingleNode to) of
        (Just{}, Just{}) -> return $ (pcase, gr2)
        (Nothing, Nothing) -> return $ (pcase, gr2)
        -- special case, where we want to retain the fact that one of the
        -- conditions is infeasible but we don't want to do any graph maintenance
        _ | pcase == ConditionInfeasible -> return $ (ConditionInfeasible, gr0)
        _ -> return (ConditionNotPropagated, gr0)

  where
    go _ [] gr = return ([],gr)
    go preconds (condK:conds) gr =  do
      (pcase, gr') <- propagateOne scope bundle preconds preD from to condK gr
      case pcase of
        -- we need to collect any non-propagated conditions so that
        -- propagated conditions are weakened with them
        -- i.e. we need to retain the fact that asserted conditions need
        -- only be provable under the assumed conditions
        ConditionNotPropagated -> do
          (pcases, gr'') <- go (condK:preconds) conds gr'
          return (pcase:pcases, gr'')
        -- give up early if any conditions are infeasible, since 
        -- we'll necessarily be assuming/asserting that this branch is
        -- unreachable
        ConditionInfeasible -> return ([pcase], gr')
        -- for propagated conditions we don't need any weakening
        ConditionPropagated{} -> do
          (pcases, gr'') <- go preconds conds gr'
          return (ConditionPropagated [condK]:pcases, gr'')

-- | Given the results of symbolic execution, and an edge in the pair graph
--   to consider, compute an updated abstract domain for the target node,
--   and update the pair graph, if necessary.
--
--   This is done by looking up the abstract domain for the target node
--   and proving that the poststate of symbolic execution satisfies
--   the abstract domain of the target node, assuming the abstract domain of
--   the source node.  If this is not the case, we use the resulting counterexample
--   to determine what additional locations need to be added to the target
--   abstract domain. We perform these widening steps in a loop until
--   the process converges or we run out of gas.
--
--   When widening, we first consider register values to widen, then we look at
--   stack, and finally global memory for locations. When widening memory, we
--   consider first locations that differ in the prestate, then locations that
--   were written during the execution of the block.  In theory, this should be
--   enough to account for all the sources of differences we have to consider.
--   Probably, the order in which we consider these effects doesn't matter much,
--   except perhaps if the widening process is aborted early (we run out of gas).
--
--   If, for some reason, we cannot find appropraite locations to widen, we
--   widen as much as we can, and report an error.
widenAlongEdge ::
  forall sym arch v.
  HasCallStack =>
  PS.SimScope sym arch v ->
  SimBundle sym arch v {- ^ results of symbolic execution for this block -} ->
  GraphNode arch {- ^ source node -} ->
  AbstractDomain sym arch v {- ^ source abstract domain -} ->
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ target graph node -} ->
  EquivM sym arch (PairGraph sym arch)
widenAlongEdge scope bundle from d gr0 to = withSym $ \sym -> do
  gr1 <- addRefinementChoice to gr0
  priority <- thisPriority
  propagateCondition scope bundle d from to gr1 >>= \case
    (ConditionPropagated{}, gr2) -> do
      -- since this 'to' edge has propagated backwards
      -- an equivalence condition, we need to restart the analysis
      -- for 'from'
      -- 'dropDomain' clears domains for all nodes following 'from' (including 'to')
      -- and re-adds ancestors of 'from' to be considered for analysis
      emitTrace @"message" "Analysis Skipped - Condition Propagation"
      
      return $ gr2
    (ConditionInfeasible, gr2) -> do
      emitTrace @"message" "Analysis Skipped - Target branch has condition that is infeasible"
      return $ gr2

      -- if no postcondition propagation is needed, we continue under
      -- the strengthened assumption that the equivalence postcondition
      -- is satisfied (potentially allowing for a stronger equivalence
      -- domain to be established)
    (ConditionNotPropagated, gr) -> do
      postCond_assume1 <- getEquivPostCondition scope bundle to ConditionAssumed gr
      postCond_assume2 <- getEquivPostCondition scope bundle to ConditionEquiv gr
      postCond_assume <- liftIO $ PEC.merge sym postCond_assume1 postCond_assume2 >>= PEC.toPred sym
      withTracing @"debug" "Assumed Postcondition" $ emitTrace @"expr" (Some postCond_assume)
      
      withAssumption postCond_assume $ do  
        case getCurrentDomain gr to of
          -- This is the first time we have discovered this location
          Nothing ->
           do traceBundle bundle ("First jump to " ++ show to)
              -- initial state of the pair graph: choose the universal domain that equates as much as possible
              d' <- makeFreshAbstractDomain scope bundle d from to
              postSpec <- initialDomainSpec to
              md <- widenPostcondition scope bundle d d'
              case md of
                NoWideningRequired -> do
                  emitTrace @"debug" "NoWideningRequired"
                  emitTraceLabel @"domain" PAD.Postdomain (Some d')
                  postSpec' <- abstractOverVars scope bundle from to postSpec d'
                  let gr1 = initDomain gr from to (priority PriorityWidening) postSpec'
                  finalizeGraphEdge scope bundle d d' from to gr1
                WideningError msg _ d'' ->
                  do let msg' = ("Error during widening: " ++ msg)
                     err <- emitError' (PEE.WideningError msg')
                     postSpec' <- abstractOverVars scope bundle from to postSpec d''
                     return $ recordMiscAnalysisError (initDomain gr from to (priority PriorityWidening) postSpec') to err
                Widen wk _ d'' -> do
                  emitTrace @"debug" (show wk)
                  emitTraceLabel @"domain" PAD.Postdomain (Some d'')
                  postSpec' <- abstractOverVars scope bundle from to postSpec d''
                  let gr1 = initDomain gr from to (priority PriorityWidening) postSpec'
                  finalizeGraphEdge scope bundle d d'' from to gr1

          -- have visited this location at least once before
          Just postSpec -> do
            -- The variables in 'postSpec' represent the final values in the
            -- post-state of the slice (which have been abstracted out by 'abstractOverVars').
            -- To put everything in the same scope, we need to bind these variables to
            -- the post-state expressions that we have currently as the result of symbolic
            -- execution (i.e. the resulting state in 'SimOutput').
            --
            -- The result is a post-domain describing the proof target (i.e. d'), that
            -- has been brought into the current scope 'v' (as the bound variables in the output
            -- expressions are still in this scope).
            --
            -- After widening, this needs to be re-phrased with respect to the final
            -- values of the slice again. This is accomplised by 'abstractOverVars', which
            -- produces the final 'AbstractDomainSpec' that has been fully abstracted away
            -- from the current scope and can be stored as the updated domain in the 'PairGraph'
            d' <- liftIO $ PS.bindSpec sym (PS.bundleOutVars scope bundle) postSpec
            md <- widenPostcondition scope bundle d d'
            case md of
              NoWideningRequired -> do
                emitTrace @"debug" "NoWideningRequired"
                traceBundle bundle "Did not need to widen"
                emitTraceLabel @"domain" PAD.Postdomain (Some d')
                finalizeGraphEdge scope bundle d d' from to gr

              WideningError msg _ d'' -> do
                let msg' = ("Error during widening: " ++ msg)
                err <- emitError' (PEE.WideningError msg')
                postSpec' <- abstractOverVars scope bundle from to postSpec d''
                case updateDomain gr from to postSpec' (priority PriorityWidening) of
                  Left gr' -> do
                    traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                    return $ recordMiscAnalysisError gr' to err
                  Right gr' -> return $ recordMiscAnalysisError gr' to err

              Widen wk _ d'' -> do
                emitTrace @"debug" (show wk)
                emitTraceLabel @"domain" PAD.Postdomain (Some d'')
                postSpec' <- abstractOverVars scope bundle from to postSpec d''
                case updateDomain gr from to postSpec' (priority PriorityWidening) of
                  Left gr' -> do
                    traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                    finalizeGraphEdge scope bundle d d'' from to gr'
                  Right gr' -> finalizeGraphEdge scope bundle d d'' from to gr'


finalizeGraphEdge ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ incoming source predomain -} ->
  AbstractDomain sym arch v {- ^ resulting target postdomain -} ->
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
finalizeGraphEdge scope bundle preD postD from to gr0 = do
  let gr1 = markEdge from to gr0
  runPendingActions edgeActions (from,to) (TupleF4 scope bundle preD postD) gr1 >>= \case
    Just gr2 -> do
      priority <- thisPriority
      return $ queueAncestors (priority PriorityHandleActions) to gr2
    Nothing -> 
      -- if the computed domain doesn't agree with any requested domain refinements,
      -- we need to propagate this backwards by dropping the entry for 'to',
      -- augmenting the equivalence condition for 'from' and re-processing it
      applyDomainRefinements scope (from,to) bundle preD postD gr1

data MaybeCF f c tp where
  JustF :: f tp c -> MaybeCF f c tp
  NothingF :: MaybeCF f c tp

runMaybeTF :: Monad m => MaybeT m (a tp c) -> m (MaybeCF a c tp)
runMaybeTF m = runMaybeT m >>= \case
  Just a -> return $ JustF a
  Nothing -> return $ NothingF

toMaybe :: MaybeCF a c tp -> Maybe (a tp c)
toMaybe (JustF a) = Just a
toMaybe NothingF = Nothing

memVars ::
  PS.SimVars sym arch v bin -> EquivM sym arch (Set.Set (Some (W4.BoundVar sym)))
memVars vars = do
  let
    mem = MT.memState $ PS.simMem $ PS.simVarState vars
    binds = MT.mkMemoryBinding mem mem
  withValid $
    (Set.unions <$> mapM (\(Some e) -> IO.liftIO $ WEH.boundVars e) (MapF.keys binds))

-- | Compute an'PAD.AbstractDomainSpec' from the input 'PAD.AbstractDomain' that is
-- parameterized over the *output* state of the given 'SimBundle'.
-- Until now, the widening process has used the same scope for the pre-domain and
-- post-domain (i.e. both contain free variables corresponding to the initial values
-- before symbolic execution).
-- To abstract the computed post-domain from its calling context, we need to rephrase
-- any symbolic terms it contains so that they only refer to the output state.
-- Specifically, given a post-domain @dom[pre]@ phrased over the pre-state variables, and
-- a function @f(pre)@ representing the result of symbolic execution, we want to compute
-- @dom'[post]@ such that @dom'[post/f(pre)] == dom[pre]@.
--
-- For any given sub-expression in the domain there are multiple possible strategies that
-- can be applied to perform this re-scoping. Here we have a (neccessarily incomplete) list of
-- strategies that are attempted, but in general they may all fail.
-- See: 'PS.StackBase' for a discussion on how this is used to re-scope stack relative
-- accesses
abstractOverVars ::
  forall sym arch pre.
  HasCallStack =>
  PS.SimScope sym arch pre  ->
  SimBundle sym arch pre ->
  GraphNode arch {- ^ source node -} ->
  GraphNode arch {- ^ target graph node -} ->
  PAD.AbstractDomainSpec sym arch {- ^ previous post-domain -} ->
  PAD.AbstractDomain sym arch pre {- ^ computed post-domain (with variables from the initial 'pre' scope) -} ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
abstractOverVars scope_pre bundle _from _to postSpec postResult = do
  result <- withTracing @"debug" "abstractOverVars" $ go
  PS.viewSpec result $ \_ d -> do
    emitTraceLabel @"domain" PAD.ExternalPostDomain (Some d)
  return result
  where
    go :: EquivM sym arch (PAD.AbstractDomainSpec sym arch)
    go = withSym $ \sym -> do
      emitTraceLabel @"domain" PAD.Postdomain (Some postResult)
      -- the post-state of the slice phrased over 'pre'
      let outVars = PS.bundleOutVars scope_pre bundle

      curAsm <- currentAsm
      emitTrace @"assumption" curAsm

      --traceBundle bundle $ "AbstractOverVars:  curAsm\n" ++ (show (pretty curAsm))

      withSimSpec (PS.simPair bundle) postSpec $ \(scope_post :: PS.SimScope sym arch post) _body -> do
        -- the variables representing the post-state (i.e. the target scope)
        let postVars = PS.scopeVarsPair scope_post

        -- rewrite post-scoped terms into pre-scoped terms that represent
        -- the result of symbolic execution (i.e. formally stating that
        -- the initial bound variables of post are equal to the results
        -- of symbolic execution)
        -- e[post] --> e[post/f(pre)]
        -- e.g.
        -- f := sp++;
        -- sp1 + 2 --> (sp0 + 1) + 2
        post_to_pre <- liftIO $ PS.getScopeCoercion sym scope_post outVars

        -- Rewrite a pre-scoped term to a post-scoped term by simply swapping
        -- out the bound variables
        -- e[pre] --> e[pre/post]
        pre_to_post <- liftIO $ PS.getScopeCoercion sym scope_pre postVars

        cache <- W4B.newIdxCache
        -- Strategies for re-scoping expressions
        let
          asConcrete :: forall v1 v2 tp. PS.ScopedExpr sym tp v1 -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp v2)
          asConcrete se = do
            Just c <- return $ (W4.asConcrete (PS.unSE se))
            liftIO $ PS.concreteScope @v2 sym c

          asScopedConst :: forall v1 v2 tp. HasCallStack => W4.Pred sym -> PS.ScopedExpr sym tp v1 -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp v2)
          asScopedConst asm se = do
            emitTrace @"assumption" (PAs.fromPred asm)
            Just c <- lift $ withAssumption asm $ do
              e' <- concretizeWithSolver (PS.unSE se)
              emitTraceLabel @"expr" "output" (Some e')
              return $ W4.asConcrete e'
            off' <- liftIO $ PS.concreteScope @v2 sym c
            emitTraceLabel @"expr" "final output" (Some (PS.unSE off'))
            return off'

          -- static version of 'asStackOffset' (no solver)
          simpleStackOffset :: forall bin tp. HasCallStack => PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym tp pre -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp post)
          simpleStackOffset bin se = do
            W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
            Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))
            pre_vars <- PPa.get bin (PS.scopeVars scope_pre)
            post_vars <- PPa.get bin (PPa.fromTuple postVars)
            let preFrame = PS.simStackBase $ PS.simVarState pre_vars
            let postFrame = PS.simStackBase $ PS.simVarState post_vars

            -- se = preFrame + off1
            Just (se_base, W4C.ConcreteBV _ se_off) <- return $ WEH.asConstantOffset sym (PS.unSE se)
            -- postFrame = preFrame + off2
            Just (postFrame_base, W4C.ConcreteBV _ postFrame_off) <- return $ WEH.asConstantOffset sym (PS.unSE postFrame)
            p1 <- liftIO $ W4.isEq sym se_base (PS.unSE preFrame)
            Just True <- return $ W4.asConstantPred p1
            p2 <- liftIO $ W4.isEq sym postFrame_base (PS.unSE preFrame)
            Just True <- return $ W4.asConstantPred p2
            -- preFrame = postFrame - off2
            -- se = (postFrame - off2) + off1
            -- se = postFrame + (off1 - off2)
            off' <- liftIO $ PS.concreteScope @post sym (W4C.ConcreteBV w (BVS.sub w se_off postFrame_off))
            liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off'


          asStackOffset :: forall bin tp. HasCallStack => PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym tp pre -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp post)
          asStackOffset bin se = do
            W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
            Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))
            -- se[v]
            post_vars <- PPa.get bin (PPa.fromTuple postVars)
            let postFrame = PS.simStackBase $ PS.simVarState post_vars

            off <- liftIO $ PS.liftScope0 @post sym (\sym' -> W4.freshConstant sym' (W4.safeSymbol "frame_offset") (W4.BaseBVRepr w))
            -- asFrameOffset := frame[post] + off
            asFrameOffset <- liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off
            -- asFrameOffset' := frame[post/f(v)] + off
            asFrameOffset' <- liftIO $ PS.applyScopeCoercion sym post_to_pre asFrameOffset
            -- asm := se == frame[post/f(pre)] + off
            asm <- liftIO $ PS.liftScope2 sym W4.isEq se asFrameOffset'
            -- assuming 'asm', is 'off' constant?        
            off' <- asScopedConst (PS.unSE asm) off        
            -- lift $ traceBundle bundle (show $ W4.printSymExpr (PS.unSE off'))
            -- return frame[post] + off
            liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off'

          asSimpleAssign :: forall tp. HasCallStack => PS.ScopedExpr sym tp pre -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp post)
          asSimpleAssign se = do
            -- se[pre]
            -- se' := se[pre/post]
            se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
            -- e'' := se[post/f(pre)]
            e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
            -- se is the original value, and e'' is the value rewritten
            -- to be phrased over the post-state
            heuristicTimeout <- lift $ CMR.asks (PC.cfgHeuristicTimeout . envConfig)
            asm <- liftIO $ PS.liftScope2 sym W4.isEq se e''
            True <- lift $ isPredTrue' heuristicTimeout (PS.unSE asm)
            return se'

          doRescope :: forall tp nm k. PL.Location sym arch nm k -> PS.ScopedExpr sym tp pre -> EquivM_ sym arch (MaybeCF (PS.ScopedExpr sym) post tp)
          doRescope _loc se = W4B.idxCacheEval cache (PS.unSE se) $ runMaybeTF $ do
              -- The decision of ordering here is only for efficiency: we expect only
              -- one strategy to succeed.
              -- NOTE: Although it is possible for multiple strategies to be applicable,
              -- they (should) all return semantically equivalent terms
              -- TODO: We could do better by picking the strategy based on the term shape,
              -- but it's not strictly necessary.

            asStackOffsetStrats <- PPa.catBins $ \bin -> do
              scope_vars_pre <- PPa.get bin (PS.scopeVars scope_pre)
              let stackbase = PS.unSE $ PS.simStackBase $ PS.simVarState scope_vars_pre
              sbVars <- IO.liftIO $ WEH.boundVars stackbase
              seVars <- IO.liftIO $ WEH.boundVars (PS.unSE se)

              -- as an optimization, we omit this test for
              -- terms which contain memory accesses (i.e. depend on
              -- the memory variable somehow), since we don't have any support for
              -- indirect reads
              mvars <- lift $ memVars scope_vars_pre
              let noMem = Set.null (Set.intersection seVars mvars)

              case Set.isSubsetOf sbVars seVars && noMem of
                True -> return $ [("asStackOffset (" ++ show bin ++ ")", asStackOffset bin se)]
                False -> return $ []



            se' <- traceAlternatives $
              -- first try strategies that don't use the solver
              [ ("asConcrete", asConcrete se)
              , ("simpleStackOffsetO", simpleStackOffset PBi.OriginalRepr se)
              , ("simpleStackOffsetP", simpleStackOffset PBi.PatchedRepr se)
              -- solver-based strategies now
              , ("asSimpleAssign", asSimpleAssign se)
              ] ++ asStackOffsetStrats
              ++ [ ("asScopedConst", asScopedConst (W4.truePred sym) se) ] 

            lift $ emitEvent (PE.ScopeAbstractionResult (PS.simPair bundle) se se')
            return se'
        -- First traverse the equivalence domain and rescope its entries
        -- In this case, failing to rescope is a (recoverable) error, as it results
        -- in a loss of soundness; dropping an entry means that the resulting domain
        -- is effectively now assuming equality on that entry.

        let domEq = PAD.absDomEq postResult
        eq_post <- subTree "equivalence" $ fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre domEq) $ \loc (se :: PS.ScopedExpr sym tp pre) ->
           subTrace @"loc" (PL.SomeLocation loc) $ do
            emitTraceLabel @"expr" "input" (Some (PS.unSE se))
            doRescope loc se >>= \case
              JustF se' -> do
                emitTraceLabel @"expr" "output" (Some (PS.unSE se'))
                return $ Just se'
              NothingF -> CMR.asks (PC.cfgRescopingFailureMode . envConfig) >>= \case
                PC.AllowEqRescopeFailure -> return Nothing
                x -> do
                  -- failed to rescope, emit a recoverable error and drop this entry
                  se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
                  e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
                  curAsms <- currentAsm

                  case x of
                    PC.ThrowOnEqRescopeFailure -> do
                      void $ emitError $ PEE.InnerSymEquivalenceError $ PEE.RescopingFailure curAsms se e''
                    PC.WarnOnEqRescopeFailure -> do
                      void $ emitWarning $ PEE.InnerSymEquivalenceError $ PEE.RescopingFailure curAsms se e''
                  return Nothing

        let evSeq = PAD.absDomEvents postResult 
        evSeq_post <- subTree "events" $ fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre evSeq) $ \loc se ->
          subTrace @"loc" (PL.SomeLocation loc) $ do
            emitTraceLabel @"expr" "input" (Some (PS.unSE se))
            doRescope loc se >>= \case
              JustF se' -> return $ Just se'
              NothingF -> CMR.asks (PC.cfgRescopingFailureMode . envConfig) >>= \case
                PC.AllowEqRescopeFailure -> return Nothing
                x -> do
                  se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
                  e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
                  curAsms <- currentAsm
                  let err = PEE.InnerSymEquivalenceError $ PEE.RescopingFailure curAsms se e''
                  case x of
                    PC.ThrowOnEqRescopeFailure -> void $ emitError err
                    PC.WarnOnEqRescopeFailure -> void $ emitWarning err
                  return Nothing
        -- Now traverse the value domain and rescope its entries. In this case
        -- failing to rescope is not an error, as it is simply weakening the resulting
        -- domain by not asserting any value constraints on that entry.
        --domVals_simplified <- PSi.applySimplifier simplifier (PAD.absDomVals postResult)
        let domVals = PAD.absDomVals postResult
        val_post <- subTree "value" $ fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre domVals) $ \loc se ->
          subTrace @"loc" (PL.SomeLocation loc) $ do
            emitTraceLabel @"expr" "input" (Some (PS.unSE se))
            doRescope loc se >>= \case
              JustF se' -> do
                emitTraceLabel @"expr" "output" (Some (PS.unSE se'))
                return $ Just se'
              NothingF -> return Nothing

        let dom = PAD.AbstractDomain eq_post val_post evSeq_post
        emitTraceLabel @"domain" PAD.ExternalPostDomain (Some dom)
        return dom

-- | Accumulate any observable events during single-sided analysis.
--   Returns empty sequences for two-sided analysis, since those are checked
--   for equality at each verification step.
getEventSequence ::
  GraphNode arch ->
  PS.SimScope sym arch v  ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v ->
  EquivM sym arch (PPa.PatchPair (PAD.EventSequence sym arch))
getEventSequence to _scope bundle preDom = withTracing @"function_name" "getEventSequence" $ withSym $ \sym -> do
  evs <- case PS.simOut bundle of
    PPa.PatchPair{} -> PPa.PatchPair <$> PAD.emptyEvents sym <*> PAD.emptyEvents sym
    PPa.PatchPairSingle bin out -> do
      PAD.EventSequence prev_seq <- PPa.get bin (PAD.absDomEvents preDom)
      next_seq <- getObservableEvents out
      -- observable events produced by this step
      is_nil <- liftIO $ isNilSymSequence sym next_seq
      case W4.asConstantPred is_nil of
        -- no new events, just return the previous event sequence
        Just True -> return $ PPa.PatchPairSingle bin (PAD.EventSequence prev_seq)
        _ -> do
          -- otherwise, append new events onto the previous ones
          fin_seq <- liftIO $ appendSymSequence sym next_seq prev_seq
          return $ PPa.PatchPairSingle bin (PAD.EventSequence fin_seq)
  PPa.matchShape (graphNodeBlocks to) evs $ \_ -> PAD.emptyEvents sym

-- | Extract the sequence of observable events for the given 
--   symbolic execution step
getObservableEvents ::
  PS.SimOutput sym arch bin v ->
  EquivM sym arch (SymSequence sym (MT.MemEvent sym (MM.ArchAddrWidth arch)))
getObservableEvents out = withSym $ \sym -> do
  let mem = PS.simMem (PS.simOutState out)
  stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
  obsMem <- CMR.asks (PMC.observableMemory . envCtx)

  let filterObservableMemOps op@(MT.MemOp (CLM.LLVMPointer blk _off) _dir _cond _w _val _end) = do
        notStk <- W4.notPred sym =<< W4.natEq sym blk stackRegion
        inRng <- sequence
                  [ MT.memOpOverlapsRegion sym op addr len
                  | (addr, len) <- obsMem
                  ]
        inRng' <- foldM (W4.orPred sym) (W4.falsePred sym) inRng
        W4.andPred sym notStk inRng'
  liftIO (MT.observableEvents sym filterObservableMemOps mem)

-- | Classifying what kind of widening has occurred
data WidenKind =
    WidenValue -- ^ constant values disagree in the value domain
  | WidenEquality -- ^ values disagree between the original and patched binaries
  deriving Show

-- Result of attempting to widen.  Errors can occur for a couple of reasons:
-- UNKNOWN results from solvers; running out of gas in the widening loop,
-- or being unable to decide how to peform a widening step when a
-- counterexample is found.
data WidenResult sym arch v
  = NoWideningRequired
  | WideningError String (WidenLocs sym arch) (AbstractDomain sym arch v)
  | Widen WidenKind (WidenLocs sym arch) (AbstractDomain sym arch v)

-- | Try the given widening strategies one at a time,
--   until the first one that computes some nontrival
--   widening, or returns an error.
tryWidenings :: Monad m =>
  [m (WidenResult sym arch v)] ->
  m (WidenResult sym arch v)
tryWidenings [] = return NoWideningRequired
tryWidenings (x:xs) =
  x >>= \case
    NoWideningRequired -> tryWidenings xs
    res -> return res


data WidenCase =
    WidenCaseStart
  | WidenCaseStep WidenKind
  | WidenCaseErr String


data WidenState sym arch v = WidenState
  { 
    stDomain :: AbstractDomain sym arch v
  , stLocs :: WidenLocs sym arch
  , stWidenCase :: WidenCase
    -- ^ starting equivalence domain or accumulated widening result
  , stTracesEq :: PTc.TraceCollection sym arch
    -- ^ collected traces for equality widening steps
  , stTracesVal :: PTc.TraceCollection sym arch
    -- ^ collected traces for value widening steps
  , stTraceAsms :: WeakAssumptions sym arch
    -- ^ pre-computed assumptions to try to add when generating traces (i.e. from withTraceAssumptions)
  }

initWidenState ::
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenState sym arch v)
initWidenState bundle d = do
  traceAsms <- mkTraceAssumptions bundle
  return $ WidenState d (WidenLocs Set.empty) WidenCaseStart PTc.empty PTc.empty traceAsms


-- Compute a final 'WidenResult' from an (intermediate) 'WidenState' (surjective)
widenStateToResult :: WidenState sym arch v -> WidenResult sym arch v
widenStateToResult st = case stWidenCase st of
  WidenCaseStart -> NoWideningRequired
  WidenCaseStep k -> Widen k (stLocs st) (stDomain st)
  WidenCaseErr msg -> WideningError msg (stLocs st) (stDomain st)

-- | This gives a fixed amount of gas for traversing the
--   widening loop. Setting this value too low seems to
--   cause widening failures even for fairly reasonable
--   cases, so this is larger than the amount of gas
--   provided for the overall pair graph updates.
localWideningGas :: Gas
localWideningGas = Gas 100

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "widenresult" where
  type TraceNodeType '(sym,arch) "widenresult" = Some (WidenResult sym arch)
  prettyNode () (Some wr) = case wr of
    NoWideningRequired -> "No Widening Required"
    WideningError msg _ _ -> "Error while widening:\n" <+> pretty msg
    Widen _wk (WidenLocs _locs) d -> "Widened domain:" <+> PAD.ppAbstractDomain (\_ -> "") d
  nodeTags = [(Summary, \() (Some wr) -> case wr of
                NoWideningRequired -> "No Widening Required"
                WideningError{} -> "Error while widening"
                Widen _wk locs _ | (regs, cells) <- PAD.locsToRegsCells locs -> ("Widened:" <+> pretty (Set.size regs) <+> "registers and" <+> pretty (Set.size cells) <+> "memory cells"))]

widenPostcondition ::
  forall sym arch v.
  HasCallStack =>
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ predomain -} ->
  AbstractDomain sym arch v {- ^ postdomain -} ->
  EquivM sym arch (WidenResult sym arch v)
widenPostcondition scope bundle preD postD0 = do
  st <- withTracing @"debug" "widenPostcondition" $ withSym $ \sym -> do
    eqCtx <- equivalenceContext
    initSt <- initWidenState bundle postD0
    traceBundle bundle "Entering widening loop"
    subTree @"domain" "Widening Steps" $
      widenLoop sym localWideningGas eqCtx initSt
    
  case stWidenCase st of
    -- we use 'withSharedEnvEmit' so that the underlying 'TraceCollection's are serialized
    -- in a shared environment with the domain.
    WidenCaseStep _ -> withSharedEnvEmit "Equivalence Counter-example Traces" $ \emit -> do
      emit (CT.knownSymbol @"trace_collection") "Equality" (stTracesEq st)
      emit (CT.knownSymbol @"trace_collection") "Value" (stTracesVal st)
      emit (CT.knownSymbol @"domain") PAD.Postdomain (Some (stDomain st))
    _ -> return ()
  return $ widenStateToResult st
 where
   widenOnce ::
     WidenKind ->
     Gas ->
     Maybe (Some (PBi.WhichBinaryRepr)) ->
     WidenState sym arch v ->
     PL.Location sym arch nm k ->
     W4.Pred sym ->
     EquivM_ sym arch (WidenState sym arch v)
   widenOnce widenK (Gas i) mwb prevState loc goal = case stWidenCase prevState of
     WidenCaseErr{} -> return prevState
     _ -> withSym $ \sym -> do
       eqCtx <- equivalenceContext
       let 
        this_loc = WidenLocs (Set.singleton (PL.SomeLocation loc))
        postD = stDomain prevState

       curAsms <- currentAsm
       let emit r =
             withValid @() $ emitEvent (PE.SolverEvent (PS.simPair bundle) PE.EquivalenceProof r curAsms goal)
       emit PE.SolverStarted

       not_goal <- liftIO $ W4.notPred sym goal
       
       --(not_goal', ptrAsms) <- PVV.collectPointerAssertions not_goal
       emitTraceLabel @"expr" "goal" (Some goal)
       tryWithAsms (stTraceAsms prevState) not_goal $ \case
         Unsat _ -> do
           emit PE.SolverSuccess
           return prevState
         Unknown -> do
           emit PE.SolverError
           let msg = "UNKNOWN result evaluating postcondition: " ++ show widenK ++ " " ++ show (pretty loc)
           _ <- emitError $ PEE.WideningError msg
           -- this is a recoverable error, since we can conservatively consider the location
           -- under analysis as inequivalent in the resulting domain

           case widenK of
             WidenValue | Just (Some wb) <- mwb -> result <$> dropValueLoc wb loc postD
             WidenEquality ->
               case loc of
                 PL.Cell c -> result <$> widenCells [Some c] postD
                 PL.Register r -> result <$> widenRegs [Some r] postD
                 PL.Unit -> return $ result $ WideningError msg this_loc postD
                 _ -> throwHere $ PEE.UnsupportedLocation
             _ -> panic Verifier "widenPostcondition" [ "Unexpected widening case"]
         Sat evalFn -> do
           emit PE.SolverFailure
           emitTrace @"message" "equivalence failure"
           if i <= 0 then
             -- we ran out of gas
             do let msg = unlines [ "Ran out of gas performing local widenings" ]
                return $ result $ WideningError msg this_loc postD
           else do
             -- The current execution does not satisfy the postcondition, and we have
             -- a counterexample.
             -- FIXME: postCondAsm doesn't exist anymore, but needs to be factored
             -- out still
             res <- widenUsingCounterexample sym scope evalFn bundle eqCtx (W4.truePred sym) (PAD.absDomEq postD) preD postD
             case res of
               -- this location was made equivalent by a previous widening in this same loop
               NoWideningRequired -> case stWidenCase prevState of
                 WidenCaseStart ->  do
                   -- if we haven't performed any widenings yet, then this is an error
                   let msg = unlines [ "Could not find any values to widen!"
                                     , show (pretty loc)
                                     ]
                   return $ result $ WideningError msg this_loc postD
                 _ -> return prevState
               Widen widenk (WidenLocs locs) d -> do
                 let nextState = prevState
                      { stWidenCase = WidenCaseStep widenk
                      , stLocs = WidenLocs locs <> stLocs prevState
                      , stDomain = d }
                 tr <- getTraceFromModel scope evalFn bundle preD Nothing
                 let (regs,cells) = getTracedLocs (Set.toList locs)
                 return $ case widenk of
                   WidenEquality -> nextState { stTracesEq = PTc.insert regs cells tr (stTracesEq nextState) }
                   WidenValue -> nextState { stTracesVal = PTc.insert regs cells tr (stTracesVal nextState) }
               _ -> return $ result res
    where
      getTracedLocs :: [PL.SomeLocation sym arch] -> ([Some (MM.ArchReg arch)], [Some (PMc.MemCell sym arch)])
      getTracedLocs [] = ([],[])
      getTracedLocs ((PL.SomeLocation l):locs) =
        let (regs,cells) = getTracedLocs locs
        in case l of
          PL.Register r -> (Some r:regs,cells)
          PL.Cell c -> (regs,Some c:cells)
        -- other kinds of locations we can ignore for now: since this is just for reporting purposes we
        -- only need to index the traces by locations the user actually knows about
          _ -> (regs,cells)

      result :: WidenResult sym arch v -> WidenState sym arch v
      result r = case r of
        NoWideningRequired -> prevState
        WideningError err locs d -> prevState { stWidenCase = WidenCaseErr err, stLocs = locs <> stLocs prevState, stDomain = d }
        Widen widenk locs d -> prevState { stWidenCase = WidenCaseStep widenk, stLocs = locs <> stLocs prevState, stDomain = d }
   
   -- The main widening loop. For now, we constrain it's iteration with a Gas parameter.
   -- In principle, I think this shouldn't be necessary, so we should revisit at some point.
   --
   -- The basic strategy here is to ask the solver to prove that the current post-condition
   -- abstract domain is sufficent to describe the post state when we assume the pre-condition
   -- abstract domain.  If it can do so, we are done. If not, then we have a counterexample
   -- in hand that we can use to decide how to widen the current post-domain and try again.
   -- `widenUsingCounterexample` uses a fixed list of heuristics to decide how to do the widening.
   widenLoop ::
     sym ->
     Gas ->
     EquivContext sym arch ->
     WidenState sym arch v
     {- ^ A summary of any widenings that were done in previous iterations. -} ->
     NodeBuilderT '(sym,arch) "domain" (EquivM_ sym arch) (WidenState sym arch v)
   widenLoop sym (Gas i) eqCtx prevRes = 
    let postD = stDomain prevRes
    in subTraceLabel' PAD.Postdomain  (Some (stDomain prevRes)) $ \unlift -> do
        let (stO, stP) = PS.asStatePair scope (simOut bundle) PS.simOutState
        
        postVals <- PPa.forBinsC $ \bin -> do
          vals <- PPa.get bin (PAD.absDomVals postD)
          st <- PPa.get bin $ PPa.PatchPair stO stP
          liftIO $ PAD.absDomainValsToPostCond sym eqCtx st Nothing vals

        -- we reset the widen case so we can capture if this
        -- step did anything
        let res0 = prevRes { stWidenCase = WidenCaseStart }

        res2 <- case postVals of
          PPa.PatchPairSingle bin (Const valPost) ->
            PL.foldLocation @sym @arch sym valPost res0 (widenOnce WidenValue (Gas i) (Just (Some bin)))
          PPa.PatchPairC valPostO valPostP -> do
            res1 <- PL.foldLocation @sym @arch sym valPostO res0 (widenOnce WidenValue (Gas i) (Just (Some PBi.OriginalRepr)))
            PL.foldLocation @sym @arch sym valPostP res1 (widenOnce WidenValue (Gas i) (Just (Some PBi.PatchedRepr)))
        
        -- for single-sided verification the equality condition is that the updated value is equal to the
        -- input value.
        -- for two-sided verification, the equality condition is that the update original value is equal
        -- to the updated patched value.
        eqPost_eq <- (liftIO $ PEq.getPostdomain sym scope bundle eqCtx (PAD.absDomEq preD) (PAD.absDomEq postD))
        res <- PL.foldLocation @sym @arch sym eqPost_eq res2 (widenOnce WidenEquality (Gas i) Nothing)

        -- Re-enter the widening loop if we had to widen at this step.
        --
        -- If we did not have to widen in this iteration, and no widening
        -- was done in previous iterations (i.e., this is the first iteration)
        -- return `NoWideningRequired`.  Otherwise return the new abstract domain
        -- and a summary of the widenings we did.
        case stWidenCase res of
          -- Some kind of error occured while widening.
          WidenCaseErr msg ->
            do traceBundle bundle "== Widening error! =="
               traceBundle bundle msg
               traceBundle bundle "Partial widening at locations:"
               traceBundle bundle (show (stLocs res))
{-
               traceBundle bundle "===== PREDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody preD)))
               traceBundle bundle "===== POSTDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody postD')))
-}
               return res

          -- In this iteration, no additional widening was done, and we can exit the loop.
          -- The ultimate result we return depends on if we did any widening steps in
          -- previous iterations (i.e. we restore the previous widen case)
          WidenCaseStart -> return $ res { stWidenCase = stWidenCase prevRes }
          -- We had to do some widening in this iteration, so reenter the loop.
          WidenCaseStep{} ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show (stLocs res))
               unlift $ widenLoop sym (Gas (i-1)) eqCtx res


-- | Refine a given 'AbstractDomainBody' to contain concrete values for the
-- output of symbolic execution, where possible.
-- Uses the default concretization strategies from 'Pate.Verification.Concretize'
getInitalAbsDomainVals ::
  forall sym arch v.
  GraphNode arch ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  EquivM sym arch (PPa.PatchPair (PAD.AbstractDomainVals sym arch))
getInitalAbsDomainVals to bundle preDom = withTracing @"debug" "getInitalAbsDomainVals" $ withSym $ \sym -> do

  getConcreteRange <- PAD.mkGetAbsRange (\es -> TFC.fmapFC (PAD.extractAbsRange sym) <$> concretizeWithSolverBatch es)
  
  eqCtx <- equivalenceContext
  vals <- forkBins $ \bin -> do
    out <- PPa.get bin (PS.simOut bundle)
    pre <- PPa.get bin (PAD.absDomVals preDom)

    PAD.batchGetAbsRange getConcreteRange $ \getConcreteRangeBatch -> 
      PAD.initAbsDomainVals sym eqCtx getConcreteRangeBatch out pre
  PPa.matchShape (graphNodeBlocks to) vals $ \_ -> return PAD.emptyDomainVals


widenUsingCounterexample ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenUsingCounterexample sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD postD =
  tryWidenings
    [ -- First check for any disagreement in the constant values
      widenValues sym evalFn bundle postD
      -- Check for disagreement in metadata
    , widenMetaData sym scope evalFn bundle postD

    , widenRegisters sym scope evalFn bundle eqCtx postCondAsm postCondStatePred postD

      -- We first attempt to widen using writes that occured in the current CFAR/slice
      -- as these are most likely to be relevant.
    , widenStack sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD postD LocalChunkWrite
    , widenHeap sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD postD LocalChunkWrite

      -- After that, we check for widenings relating to the precondition, i.e., frame conditions.
    , widenStack sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD postD PreDomainCell
    , widenHeap sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD postD PreDomainCell
    ]

data MemCellSource = LocalChunkWrite | PreDomainCell

widenValues ::
  forall sym arch v.
  sym ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenValues sym evalFn bundle postD = do
  (postD', mlocs) <- PAD.widenAbsDomainVals sym postD getRange bundle
  case mlocs of
    Just (WidenLocs locs) -> do
      if Set.null locs then
        return NoWideningRequired
      else
        return $ Widen WidenValue (WidenLocs locs) postD'
    Nothing -> return $ WideningError "widenValues" mempty postD
  where
     getRange :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (PAD.AbsRange tp)
     getRange e = do
       g <- execGroundFn evalFn e
       return $ PAD.groundToAbsRange (W4.exprType e) g

widenMetaData ::
  forall sym arch v.
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenMetaData sym scope evalFn bundle postD = do
  (postD', mlocs) <- PAD.widenAbsDomainEqMetaData sym scope postD concretize bundle
  case mlocs of
    Just (WidenLocs locs) -> do
      if Set.null locs then
        return NoWideningRequired
      else
        return $ Widen WidenEquality (WidenLocs locs) postD'
    Nothing -> return $ WideningError "widenMetaData" mempty postD
  where
     concretize :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (W4.SymExpr sym tp)
     concretize e = do
       g <- execGroundFn evalFn e
       liftIO $ symbolicFromConcrete sym g e

dropValueLoc ::
  forall arch sym v nm k bin.
  PBi.WhichBinaryRepr bin ->
  PL.Location sym arch nm k ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
dropValueLoc wb loc postD = do
  vals <- PPa.get wb (PAD.absDomVals postD)
  let
    v = case loc of
      PL.Cell c -> vals { PAD.absMemVals = MapF.delete c (PAD.absMemVals vals) }
      PL.Register r ->
        vals { PAD.absRegVals = (PAD.absRegVals vals) & (MM.boundValue r) .~ (PAD.noAbsVal (MT.typeRepr r)) }
      PL.Unit -> vals
      _ -> error "unsupported location"
    locs = WidenLocs (Set.singleton (PL.SomeLocation loc))
  let vals' = PPa.set wb v (PAD.absDomVals postD) 
  return $ Widen WidenValue locs (postD { PAD.absDomVals = vals' })

widenCells ::
  [Some (PMc.MemCell sym arch)] ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenCells cells postD = withSym $ \sym -> do
  newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- cells ]
  -- the domain semantics will ignore cells which have the wrong region, so
  -- we can just add the cells to both at the cost of some redundancy
  let heapDom = PEE.eqDomainGlobalMemory (PAD.absDomEq $ postD)
  heapDom' <- liftIO $ PEM.intersect sym heapDom newCells
  let stackDom = PEE.eqDomainStackMemory (PAD.absDomEq $ postD)
  stackDom' <- liftIO $ PEM.intersect sym stackDom newCells
  let pred' = (PAD.absDomEq postD){ PEE.eqDomainGlobalMemory = heapDom', PEE.eqDomainStackMemory = stackDom' }
  let postD' = postD { PAD.absDomEq = pred' }
  let cellsLocs = map (\(Some c) -> PL.SomeLocation (PL.Cell c)) cells
  return (Widen WidenEquality (WidenLocs (Set.fromList cellsLocs)) postD')

widenRegs ::
  [Some (MM.ArchReg arch)] ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenRegs newRegs postD = withSym $ \sym -> do
  let
    regs' = foldl'
                 (\m (Some r) -> PER.update sym (\ _ -> W4.falsePred sym) r m)
                 (PEE.eqDomainRegisters (PAD.absDomEq $ postD))
                 newRegs
    pred' = (PAD.absDomEq postD) { PEE.eqDomainRegisters = regs' }
    postD' = postD { PAD.absDomEq = pred' }
    newRegsLocs = map (\(Some r) -> PL.SomeLocation (PL.Register r)) newRegs
    locs = WidenLocs (Set.fromList newRegsLocs)
  return (Widen WidenEquality locs postD')

-- TODO, lots of code duplication between the stack and heap cases.
--  should we find some generalization?
widenHeap ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch v)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenHeap sym scope evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalHeapWrites sym scope evalFn bundle eqCtx
             PreDomainCell   -> findUnequalHeapMemCells sym scope evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainGlobalMemory (PAD.absDomEq postD)) xs

     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- zs ]
          let heapDom = PEE.eqDomainGlobalMemory (PAD.absDomEq $ postD)
          heapDom' <- liftIO $ PEM.intersect sym heapDom newCells
          let pred' = (PAD.absDomEq postD){ PEE.eqDomainGlobalMemory = heapDom' }
          let postD' = postD { PAD.absDomEq = pred' }
          let cellsLocs = map (\(Some c) -> PL.SomeLocation (PL.Cell c)) zs
          return (Widen WidenEquality (WidenLocs (Set.fromList cellsLocs)) postD')


-- | Only return those cells not already excluded by the postdomain
filterCells :: forall sym arch.
  sym ->
  SymGroundEvalFn sym ->
  PEM.MemoryDomain sym arch ->
  [Some (PMc.MemCell sym arch)] ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
filterCells sym evalFn memDom xs = filterM filterCell xs
  where
    filterCell (Some c) =
      execGroundFn evalFn =<< liftIO (PEM.mayContainCell sym memDom c)

widenStack ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch v)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenStack sym scope evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalStackWrites sym scope evalFn bundle eqCtx
             PreDomainCell   -> findUnequalStackMemCells sym scope evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainStackMemory (PAD.absDomEq postD)) xs
     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- zs ]
          let stackDom = PEE.eqDomainStackMemory (PAD.absDomEq postD)
          stackDom' <- liftIO $ PEM.intersect sym stackDom newCells
          let pred' = (PAD.absDomEq $ postD){ PEE.eqDomainStackMemory = stackDom' }
          let postD' = postD { PAD.absDomEq = pred' }
          let cellsLocs = map (\(Some c) -> PL.SomeLocation (PL.Cell c)) zs
          return (Widen WidenEquality (WidenLocs (Set.fromList cellsLocs)) postD')


-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
-- TODO: what to do for singletons?
findUnequalHeapWrites ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalHeapWrites sym scope evalFn bundle eqCtx = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState

  footO <- liftIO $ MT.traceFootprint sym (PS.simMem oPostState)
  footP <- liftIO $ MT.traceFootprint sym (PS.simMem pPostState)
  let footprints = Set.union footO footP
  memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (Set.filter (MT.isDir MT.Write) footprints))
  execWriterT $ forM_ memWrites $ \(Some cell, cond) -> do
      cellEq <- liftIO $ resolveCellEquivMem sym eqCtx oPostState pPostState cell cond
      cellEq' <- lift $ execGroundFn evalFn cellEq
      unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackWrites ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalStackWrites sym scope evalFn bundle eqCtx = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState

  footO <- liftIO $ MT.traceFootprint sym (PS.simMem oPostState)
  footP <- liftIO $ MT.traceFootprint sym (PS.simMem pPostState)
  let footprints = Set.union footO footP
  memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (Set.filter (MT.isDir MT.Write) footprints))
  execWriterT $ forM_ memWrites $ \(Some cell, cond) -> do
    cellEq <- liftIO $ resolveCellEquivStack sym eqCtx oPostState pPostState cell cond
    cellEq' <- lift $ execGroundFn evalFn cellEq
    unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalHeapMemCells ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalHeapMemCells sym scope evalFn bundle eqCtx preD = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState
  let prestateHeapCells = PEM.toList (PEE.eqDomainGlobalMemory (PAD.absDomEq preD))

  execWriterT $ forM_ prestateHeapCells $ \(Some cell, cond) -> do
    cellEq <- liftIO $ resolveCellEquivMem sym eqCtx oPostState pPostState cell cond
    cellEq' <- lift $ execGroundFn evalFn cellEq
    unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackMemCells ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalStackMemCells sym scope evalFn bundle eqCtx preD = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState
  let prestateStackCells = PEM.toList (PEE.eqDomainStackMemory (PAD.absDomEq preD))

  execWriterT $ forM_ prestateStackCells $ \(Some cell, cond) -> do
      cellEq <- liftIO $ resolveCellEquivStack sym eqCtx oPostState pPostState cell cond
      cellEq' <- lift $ execGroundFn evalFn cellEq
      unless cellEq' (tell [Some cell])

widenRegisters ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenRegisters sym scope evalFn bundle eqCtx _postCondAsm postCondStatePred postD = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState

  newRegs <- findUnequalRegs sym evalFn eqCtx
                (PEE.eqDomainRegisters postCondStatePred)
                (PS.simRegs oPostState)
                (PS.simRegs pPostState)

  if null newRegs then
    return NoWideningRequired
  else
    -- TODO, widen less aggressively using the path condition or something?
    let regs' = foldl
                  (\m (Some r) -> PER.update sym (\ _ -> W4.falsePred sym) r m)
                  (PEE.eqDomainRegisters (PAD.absDomEq $ postD))
                  newRegs
        pred' = (PAD.absDomEq postD)
                { PEE.eqDomainRegisters = regs'
                }
        postD' = postD { PAD.absDomEq = pred' }
        newRegsLocs = map (\(Some r) -> PL.SomeLocation (PL.Register r)) newRegs
        locs = WidenLocs (Set.fromList newRegsLocs)
    in return (Widen WidenEquality locs postD')


-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalRegs ::
  sym ->
  SymGroundEvalFn sym ->
  EquivContext sym arch ->
  PER.RegisterDomain sym arch ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  EquivM sym arch [Some (MM.ArchReg arch)]
findUnequalRegs sym evalFn eqCtx regPred oRegs pRegs =
  execWriterT $ MM.traverseRegsWith_
    (\regName oRegVal ->
         do let pRegVal = MM.getBoundValue regName pRegs
            let pRegEq  = PER.registerInDomain sym regName regPred
            regEq <- lift $ execGroundFn evalFn pRegEq
            when regEq $
              do isEqPred <- liftIO (registerValuesEqual sym eqCtx regName oRegVal pRegVal)
                 isEq <- lift $ execGroundFn evalFn isEqPred
                 when (not isEq) (tell [Some regName]))
    oRegs