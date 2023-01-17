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

module Pate.Verification.Widening
  ( widenAlongEdge
  , WidenLocs(..)
  , getObservableEvents
  ) where

import           GHC.Stack
import           Control.Lens ( (.~), (&), (^.) )
import           Control.Monad (when, forM_, unless, filterM, foldM)
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
import           Data.List (foldl')
import           Data.Parameterized.Classes()
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF

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
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Location as PL
import qualified Pate.MemCell as PMc
import           Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Equivalence.EquivalenceDomain as PEE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Proof.Operations as PP
import qualified Pate.Proof.CounterExample as PP
import qualified Pate.Proof.Instances ()
import qualified Pate.ExprMappable as PEM
import qualified Pate.Solver as PSo

import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT

import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Config as PC

import           Pate.Verification.PairGraph
import qualified Pate.Verification.ConditionalEquiv as PVC
import qualified Pate.Verification.Validity as PVV
import           Pate.Verification.PairGraph.Node ( GraphNode(..), pattern GraphNodeEntry, pattern GraphNodeReturn, nodeFuns )
import qualified Pate.AssumptionSet as PAs
import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( WidenLocs(..) )
import           Pate.TraceTree
import qualified What4.ExprHelpers as WEH
import Lang.Crucible.Simulator.SymSequence
import qualified Pate.Monad.Context as PMC
import Data.Functor.Const (Const(..))
import Pate.Verification.Concretize (symbolicFromConcrete)

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
makeFreshAbstractDomain scope bundle preDom from _to = withTracing @"function_name" "makeFreshAbstractDomain" $ do
  case from of
    -- graph node
    GraphNodeEntry{} -> startTimer $ do
      initDom <- initialDomain
      vals <- getInitalAbsDomainVals bundle preDom
      evSeq <- getEventSequence scope bundle preDom
      return $ initDom { PAD.absDomVals = vals, PAD.absDomEvents = evSeq }
    -- return node
    GraphNodeReturn{} -> do
      initDom <- initialDomain
      -- as a small optimization, we know that the return nodes leave the values
      -- unmodified, and therefore any previously-established value constraints
      -- will still hold
      evSeq <- getEventSequence scope bundle preDom
      return $ initDom { PAD.absDomVals = PAD.absDomVals preDom
                       , PAD.absDomEvents = evSeq
                       }


getEquivPostCondition ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  GraphNode arch {- ^ target -} ->
  PairGraph sym arch ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
getEquivPostCondition scope _bundle to gr = withSym $ \sym -> do
  case getEquivCondition gr to of
    Just condSpec -> do
      -- FIXME: what to do with asm?
      (_asm, cond) <- liftIO $ PS.bindSpec sym (PS.scopeVars scope) condSpec
      return cond
    Nothing -> return $ PEC.universal sym

extractPtrs ::
  PSo.ValidSym sym =>
  CLM.LLVMPtr sym w1 ->
  CLM.LLVMPtr sym w2 ->
  [Some (W4.SymExpr sym)]
extractPtrs (CLM.LLVMPointer region1 off1) (CLM.LLVMPointer region2 off2) =
  [Some (W4.natToIntegerPure region1), Some off1, Some (W4.natToIntegerPure region2), Some off2]

computeEquivCondition ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ incoming predomain -} ->
  AbstractDomain sym arch v {- ^ resulting target postdomain -} ->
  (forall nm k. PL.Location sym arch nm k -> Bool) {- ^ filter for locations to force equal -} ->
  EquivM sym arch (PEC.EquivalenceCondition sym arch v)
computeEquivCondition scope bundle preD postD f = withTracing @"function_name" "computeEquivCondition" $ withSym $ \sym -> do
  eqCtx <- equivalenceContext
  emitTraceLabel @"domain" PAD.Postdomain (Some postD)
  PPa.PatchPairC regsO regsP <- PPa.forBinsC $ \bin -> PS.simOutRegs <$> PPa.get bin (PS.simOut bundle)
  PPa.PatchPairC memO memP <- PPa.forBinsC $ \bin -> PS.simOutMem <$> PPa.get bin (PS.simOut bundle)
  postD_eq' <- PL.traverseLocation @sym @arch sym (PAD.absDomEq postD) $ \loc p -> case f loc of
    False -> return (PL.getLoc loc, p)
    -- modify postdomain to unconditionally include target locations
    True -> return $ (PL.getLoc loc, W4.truePred sym)
  
  eqCond <- liftIO $ PEq.getPostdomain sym scope bundle eqCtx (PAD.absDomEq preD) postD_eq'
  eqCond' <- applyCurrentAsms eqCond
  
  subTree @"loc" "Locations" $
    PEC.fromLocationTraversable @sym @arch sym eqCond' $ \loc eqPred -> case f loc of
    -- irrelevant location
    False -> return $ W4.truePred sym
    True -> subTrace (PL.SomeLocation loc) $ do
      goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
      emitTraceLabel @"expr" "input" (Some eqPred)
      isPredTrue' goalTimeout eqPred >>= \case
        True -> return $ W4.truePred sym
        False -> do      
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

          values <- Set.fromList <$> mapM (\(Some e) -> Some <$> ((liftIO (WEH.stripAnnotations sym e)) >>= (\x -> applyCurrentAsmsExpr x))) values_

          (eqPred', ptrAsms) <- PVV.collectPointerAssertions eqPred
          --let values = Set.singleton (Some eqPred')
          withAssumptionSet ptrAsms $ do
            cond1 <- PVC.computeEqCondition bundle eqPred' values
            emitTraceLabel @"expr" "computeEqCondition" (Some cond1)
            cond2 <- PVC.weakenEqCondition bundle cond1 eqPred' values
            emitTraceLabel @"expr" "weakenEqCondition" (Some cond2)
            cond3 <- PVC.checkAndMinimizeEqCondition bundle cond2 eqPred
            emitTraceLabel @"expr" "checkAndMinimizeEqCondition" (Some cond3)
            goalSat "computeEquivCondition" cond3 $ \case
              Sat{} -> return cond3
              _ -> do
                emitError $ PEE.UnsatisfiableEquivalenceCondition (PEE.SomeExpr @_ @sym cond3)
                return $ W4.truePred sym

-- | After widening an edge, insert an equivalence condition
--   into the pairgraph for candidate functions
initializeCondition ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ incoming source predomain -} ->
  AbstractDomain sym arch v {- ^ resulting target postdomain -} ->
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
initializeCondition _ _ _ _ _ (GraphNode _) gr = return gr
initializeCondition scope bundle preD postD from to@(ReturnNode ret) gr = withSym $ \sym -> do
  case getEquivCondition gr to of
    Just{} -> return gr
    Nothing -> do
      eqCondFns <- CMR.asks envEqCondFns
      case Map.lookup (nodeFuns ret) eqCondFns of
        Just locFilter -> do
          eqCond <- computeEquivCondition scope bundle preD postD (\l -> locFilter (PL.SomeLocation l))
          pathCond <- CMR.asks envPathCondition >>= PAs.toPred sym
          eqCond' <- PEC.mux sym pathCond eqCond (PEC.universal sym)
          let gr1 = setEquivCondition to (PS.mkSimSpec scope eqCond') gr
          return $ dropDomain to (markEdge from to gr1)
        Nothing -> return gr

-- | Push an equivalence condition back up the graph.
--   Returns 'Nothing' if there is nothing to do (i.e. no condition or
--   existing condition is already implied)
--
--   FIXME: We may need to re-visit the path condition propagation
--   if we discover we can't satisfy the target constraint as a result
--   of traversing to this node via some new path
--
--   FIXME: Formally, any update to the equivalence condition requires
--   invalidating any subsequent nodes, since we now may be propagating
--   stronger equivalence domains

propagateCondition ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  GraphNode arch {- ^ from -} ->
  GraphNode arch {- ^ to -} ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
propagateCondition scope bundle from to gr = withSym $ \sym -> do
  pathCond <- CMR.asks envPathCondition >>= PAs.toPred sym
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  preCond <- case getEquivCondition gr from of
    Just condSpec -> do
      -- FIXME: what to do with asm?
      -- bind the pre-state condition to the initial variables
       (_asm, cond) <- liftIO $ PS.bindSpec sym (PS.bundleInVars bundle) condSpec
       return cond
    Nothing -> return $ PEC.universal sym
  case getEquivCondition gr to of
    -- no target equivalence condition, nothing to do
    Nothing -> return Nothing
    Just condSpec -> withTracing @"function_name" "propagateCondition" $ do
      -- FIXME: what to do with asm?
      -- bind the target condition to the result of symbolic execution
      -- FIXME: need to think harder about how to manage variable scoping,
      -- this isn't really properly tracking variable dependencies
      (_asm, cond) <- liftIO $ PS.bindSpec sym (PS.scopeVars scope) condSpec
      preCond_pred <- PEC.toPred sym preCond
      cond' <- withAssumption preCond_pred $ subTree @"loc" "Propagate Condition" $ do
        -- TODO: could do a scoped wither here just for clarity
        PL.witherLocation @sym @arch sym cond $ \loc postCond_pred -> subTrace (PL.SomeLocation loc) $ do
          emitTraceLabel @"expr" "input" (Some postCond_pred)
          isPredTrue' goalTimeout postCond_pred >>= \case
            -- pre-condition is already sufficient to imply the target post-condition, so
            -- nothing further to propagate
            -- (will also happen for entries that are not in the current path condition)
            True -> do
              emitTraceLabel @"bool" "Propagated" False
              return $ Nothing
            -- pre-condition is insufficient, so propagation is required
            False -> do
              emitTraceLabel @"bool" "Propagated" True
              return $ Just (PL.getLoc loc, postCond_pred)
      cond_pred <- PEC.toPred sym cond'
      case W4.asConstantPred cond_pred of
        -- nothing propagated, so no changes to the graph required
        Just True -> return Nothing
        _ -> do
          -- predicate the computed condition to only apply to the current path
          -- note that this condition is still scoped to the initial variables of the slice
          preCond' <- PEC.mux sym pathCond cond' preCond
          -- no rescoping required - this is the easy direction for propagation
          return $ Just $ setEquivCondition from (PS.mkSimSpec scope preCond') gr

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
widenAlongEdge scope bundle from d gr to = withSym $ \sym -> do
  propagateCondition scope bundle from to gr >>= \case
    Just gr_ -> do
      -- since this 'to' edge has propagated backwards
      -- an equivalence condition, we need to restart the analysis
      -- for 'from'
      -- 'dropDomain' clears domains for all nodes following 'from' (including 'to')
      -- and re-adds ancestors of 'from' to be considered for analysis
      emitTrace @"simplemessage" "Analysis Skipped - Equivalence Domain Propagation"
      
      return $ dropDomain from (markEdge from to gr_)
      -- if no postcondition propagation is needed, we continue under
      -- the strengthened assumption that the equivalence postcondition
      -- is satisfied (potentially allowing for a stronger equivalence
      -- domain to be established)
    Nothing -> do
      postCond <- getEquivPostCondition scope bundle to gr >>= PEC.toPred sym
      emitTraceLabel @"expr" "Assumed Postcondition" (Some postCond)
      
      withAssumption postCond $ do  
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
                  postSpec' <- abstractOverVars scope bundle from to postSpec d'
                  return (freshDomain gr to postSpec')
                WideningError msg _ d'' ->
                  do let msg' = ("Error during widening: " ++ msg)
                     err <- emitError' (PEE.WideningError msg')
                     postSpec' <- abstractOverVars scope bundle from to postSpec d''
                     return $ recordMiscAnalysisError (freshDomain gr to postSpec') to err
                Widen _ _ d'' -> do
                  postSpec' <- abstractOverVars scope bundle from to postSpec d''
                  let gr1 = freshDomain gr to postSpec'
                  initializeCondition scope bundle d d'' from to gr1

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
            (asm, d') <- liftIO $ PS.bindSpec sym (PS.bundleOutVars bundle) postSpec
            withAssumptionSet asm $ do
              md <- widenPostcondition scope bundle d d'
              case md of
                NoWideningRequired ->
                  do traceBundle bundle "Did not need to widen"
                     return gr

                WideningError msg _ d'' ->
                  do let msg' = ("Error during widening: " ++ msg)
                     err <- emitError' (PEE.WideningError msg')
                     postSpec' <- abstractOverVars scope bundle from to postSpec d''
                     case updateDomain gr from to postSpec' of
                       Left gr' ->
                         do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                            return $ recordMiscAnalysisError gr' to err
                       Right gr' -> return $ recordMiscAnalysisError gr' to err

                Widen _ _ d'' -> do
                  postSpec' <- abstractOverVars scope bundle from to postSpec d''
                  case updateDomain gr from to postSpec' of
                    Left gr' ->
                      do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                         return gr'
                    Right gr' -> return gr'

data MaybeF f tp where
  JustF :: f tp -> MaybeF f tp
  NothingF :: MaybeF f tp

runMaybeTF :: Monad m => MaybeT m (a tp) -> m (MaybeF a tp)
runMaybeTF m = runMaybeT m >>= \case
  Just a -> return $ JustF a
  Nothing -> return $ NothingF

toMaybe :: MaybeF a tp -> Maybe (a tp)
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
  result <- withTracing @"function_name" "abstractOverVars" $ go
  PS.viewSpec result $ \_ d -> do
    emitTraceLabel @"domain" PAD.ExternalPostDomain (Some d)
  return result
  where
    go :: EquivM sym arch (PAD.AbstractDomainSpec sym arch)
    go = withSym $ \sym -> do
      emitTraceLabel @"domain" PAD.Postdomain (Some postResult)
      -- the post-state of the slice phrased over 'pre'
      let outVars = PS.bundleOutVars bundle

      curAsm <- currentAsm
      emitTrace @"assumption" curAsm

      --traceBundle bundle $ "AbstractOverVars:  curAsm\n" ++ (show (pretty curAsm))

      withSimSpec (PS.simPair bundle) postSpec $ \(scope_post :: PS.SimScope sym arch post) _body -> do
        -- the variables representing the post-state (i.e. the target scope)
        let postVars = PS.scopeVars scope_post

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
          asConcrete :: forall v1 v2 tp. PS.ScopedExpr sym v1 tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym v2 tp)
          asConcrete se = do
            Just c <- return $ (W4.asConcrete (PS.unSE se))
            liftIO $ PS.concreteScope @v2 sym c

          asScopedConst :: forall v1 v2 tp. HasCallStack => W4.Pred sym -> PS.ScopedExpr sym v1 tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym v2 tp)
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
          simpleStackOffset :: forall bin tp. HasCallStack => PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym pre tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym post tp)
          simpleStackOffset bin se = do
            W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
            Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))
            pre_vars <- PPa.get bin (PS.scopeVars scope_pre)
            post_vars <- PPa.get bin postVars
            let preFrame = PS.unSB $ PS.simStackBase $ PS.simVarState pre_vars
            let postFrame = PS.unSB $ PS.simStackBase $ PS.simVarState post_vars

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


          asStackOffset :: forall bin tp. HasCallStack => PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym pre tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym post tp)
          asStackOffset bin se = do
            W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
            Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))
            -- se[v]
            post_vars <- PPa.get bin postVars
            let postFrame = PS.unSB $ PS.simStackBase $ PS.simVarState post_vars

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

          asSimpleAssign :: forall tp. HasCallStack => PS.ScopedExpr sym pre tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym post tp)
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

          doRescope :: forall tp nm k. PL.Location sym arch nm k -> PS.ScopedExpr sym pre tp -> EquivM_ sym arch (MaybeF (PS.ScopedExpr sym post) tp)
          doRescope _loc se = W4B.idxCacheEval cache (PS.unSE se) $ runMaybeTF $ do
              -- The decision of ordering here is only for efficiency: we expect only
              -- one strategy to succeed.
              -- NOTE: Although it is possible for multiple strategies to be applicable,
              -- they (should) all return semantically equivalent terms
              -- TODO: We could do better by picking the strategy based on the term shape,
              -- but it's not strictly necessary.

            asStackOffsetStrats <- PPa.catBins $ \bin -> do
              scope_vars_pre <- PPa.get bin (PS.scopeVars scope_pre)
              let stackbase = PS.unSE $ PS.unSB $ PS.simStackBase $ PS.simVarState scope_vars_pre
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
              , ("asScopedConst", asScopedConst (W4.truePred sym) se)
              , ("asSimpleAssign", asSimpleAssign se)
              ] ++ asStackOffsetStrats

            lift $ emitEvent (PE.ScopeAbstractionResult (PS.simPair bundle) se se')
            return se'
        -- First traverse the equivalence domain and rescope its entries
        -- In this case, failing to rescope is a (recoverable) error, as it results
        -- in a loss of soundness; dropping an entry means that the resulting domain
        -- is effectively now assuming equality on that entry.

        -- simplifier <- PSi.getSimplifier
        --domEq_simplified <- PSi.applySimplifier simplifier (PAD.absDomEq postResult)
        let domEq = PAD.absDomEq postResult
        eq_post <- subTree "equivalence" $ fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre domEq) $ \loc (se :: PS.ScopedExpr sym pre tp) ->
           subTrace @"loc" (PL.SomeLocation loc) $ do
            emitTraceLabel @"expr" "input" (Some (PS.unSE se))
            doRescope loc se >>= \case
              JustF se' -> do
                emitTraceLabel @"expr" "output" (Some (PS.unSE se'))
                return $ Just se'
              NothingF -> do
                -- failed to rescope, emit a recoverable error and drop this entry
                se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
                e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
                curAsms <- currentAsm
                _ <- emitError $ PEE.RescopingFailure curAsms se e''
                return Nothing

        let evSeq = PAD.absDomEvents postResult
        --nextSeq <- 
        evSeq_post <- subTree "events" $ fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre evSeq) $ \loc se ->
          subTrace @"loc" (PL.SomeLocation loc) $ do
            emitTraceLabel @"expr" "input" (Some (PS.unSE se))
            doRescope loc se >>= \case
              JustF se' -> return $ Just se'
              NothingF -> do
                se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
                e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
                curAsms <- currentAsm
                _ <- emitError $ PEE.RescopingFailure curAsms se e''
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
  PS.SimScope sym arch v  ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v ->
  EquivM sym arch (PPa.PatchPair (PAD.EventSequence sym arch))
getEventSequence _scope bundle preDom = withTracing @"function_name" "getEventSequence" $ withSym $ \sym -> do
  case PS.simOut bundle of
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

type WidenState sym arch v = Either (AbstractDomain sym arch v) (WidenResult sym arch v)

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
widenPostcondition scope bundle preD postD0 =
  withTracing @"function_name" "widenPostcondition" $ withSym $ \sym -> do
    eqCtx <- equivalenceContext
    traceBundle bundle "Entering widening loop"
    subTree @"domain" "Widening Steps" $
      widenLoop sym localWideningGas eqCtx postD0 Nothing


 where
   widenOnce ::
     WidenKind ->
     Gas ->
     Maybe (Some (PBi.WhichBinaryRepr)) ->
     WidenState sym arch v ->
     PL.Location sym arch nm k ->
     W4.Pred sym ->
     EquivM_ sym arch (WidenState sym arch v)
   widenOnce widenK (Gas i) mwb prevState loc goal = case prevState of
     Right NoWideningRequired -> return prevState
     Right (WideningError{}) -> return prevState
     _ -> startTimer $ withSym $ \sym -> do
       eqCtx <- equivalenceContext
       (prevLocs, postD) <- case prevState of
             Left prevDom -> return (mempty, prevDom)
             --FIXME: we're dropping the widening Kind now since we're
             --potentially doing multiple widenings in one iteration
             Right (Widen _ locs prevDom) -> return (locs, prevDom)
             -- NOTE: spurious missing case on some ghc versions
       curAsms <- currentAsm
       let emit r =
             withValid @() $ emitEvent (PE.SolverEvent (PS.simPair bundle) PE.EquivalenceProof r curAsms goal)
       emit PE.SolverStarted

       not_goal <- liftIO $ W4.notPred sym goal
       
       --(not_goal', ptrAsms) <- PVV.collectPointerAssertions not_goal
       emitTraceLabel @"expr" "goal" (Some goal)
       goalSat "prove postcondition" not_goal $ \case
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
             WidenValue | Just (Some wb) <- mwb -> Right <$> dropValueLoc wb loc postD
             WidenEquality ->
               case loc of
                 PL.Cell c -> Right <$> widenCells [Some c] postD
                 PL.Register r -> Right <$> widenRegs [Some r] postD
                 PL.Unit -> return $ Right $ WideningError msg prevLocs postD
                 _ -> throwHere $ PEE.UnsupportedLocation
             _ -> panic Verifier "widenPostcondition" [ "Unexpected widening case"]
         Sat evalFn -> do
           emit PE.SolverFailure
           if i <= 0 then
             -- we ran out of gas
             do slice <- PP.simBundleToSlice scope bundle
                ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice evalFn
                let msg = unlines [ "Ran out of gas performing local widenings"
                                  , show (pretty ineqRes)
                                  ]
                return $ Right $ WideningError msg prevLocs postD
           else do
             -- The current execution does not satisfy the postcondition, and we have
             -- a counterexample.
             -- FIXME: postCondAsm doesn't exist anymore, but needs to be factored
             -- out still
             res <- widenUsingCounterexample sym scope evalFn bundle eqCtx (W4.truePred sym) (PAD.absDomEq postD) preD prevLocs postD
             case res of
               -- this location was made equivalent by a previous widening in this same loop
               NoWideningRequired -> case prevState of
                 Left{} ->  do
                   -- if we haven't performed any widenings yet, then this is an error
                   slice <- PP.simBundleToSlice scope bundle
                   ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState
                                   (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice evalFn
                   let msg = unlines [ "Could not find any values to widen!"
                                     , show (pretty loc)
                                     , show (pretty ineqRes)
                                     ]
                   
                   return $ Right $ WideningError msg prevLocs postD
                 Right{} -> return prevState
               _ -> return $ Right res
   
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
     AbstractDomain sym arch v ->
     Maybe (WidenResult sym arch v)
     {- ^ A summary of any widenings that were done in previous iterations.
          If @Nothing@, than no previous widenings have been performed. -} ->
     NodeBuilderT '(sym,arch) "domain" (EquivM_ sym arch) (WidenResult sym arch v)
   widenLoop sym (Gas i) eqCtx postD mPrevRes = subTraceLabel' PAD.Postdomain  (Some postD) $ \unlift ->
     do
        postVals <- PPa.forBinsC $ \bin -> do
          vals <- PPa.get bin (PAD.absDomVals postD)
          output <- PPa.get bin $ PS.simOut bundle
          let st = PS.simOutState output
          liftIO $ PAD.absDomainValsToPostCond sym eqCtx st Nothing vals

        res2 <- case postVals of
          PPa.PatchPairSingle bin (Const valPost) -> 
            PL.foldLocation @sym @arch sym valPost (Left postD) (widenOnce WidenValue (Gas i) (Just (Some bin)))
          PPa.PatchPairC valPostO valPostP -> do
            res1 <- PL.foldLocation @sym @arch sym valPostO (Left postD) (widenOnce WidenValue (Gas i) (Just (Some PBi.OriginalRepr)))
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
        case res of

          -- Some kind of error occured while widening.
          Right er@(WideningError msg locs _postD') ->
            do traceBundle bundle "== Widening error! =="
               traceBundle bundle msg
               traceBundle bundle "Partial widening at locations:"
               traceBundle bundle (show locs)
{-
               traceBundle bundle "===== PREDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody preD)))
               traceBundle bundle "===== POSTDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody postD')))
-}
               return er

          -- In this iteration, no additional widening was done, and we can exit the loop.
          -- The ultimate result we return depends on if we did any widening steps in
          -- previous iterations.
          Right NoWideningRequired ->
            case mPrevRes of
              Nothing   -> return NoWideningRequired
              Just prevRes -> return prevRes
          -- no widening happened
          Left{} ->
            case mPrevRes of
              Nothing   -> return NoWideningRequired
              Just prevRes -> return prevRes
          -- We had to do some widening in this iteration, so reenter the loop.
          Right (Widen widenK locs postD') ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show locs)
               let newlocs = case mPrevRes of
                     Just (Widen _ prevLocs _) -> locs <> prevLocs
                     _ -> locs
               unlift $ widenLoop sym (Gas (i-1)) eqCtx postD' (Just $ Widen widenK newlocs postD')


-- | Refine a given 'AbstractDomainBody' to contain concrete values for the
-- output of symbolic execution, where possible.
-- Uses the default concretization strategies from 'Pate.Verification.Concretize'
getInitalAbsDomainVals ::
  forall sym arch v.
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  EquivM sym arch (PPa.PatchPair (PAD.AbstractDomainVals sym arch))
getInitalAbsDomainVals bundle preDom = withTracing @"function_name" "getInitalAbsDomainVals" $ withSym $ \sym -> do
  PEM.SymExprMappable asEM <- return $ PEM.symExprMappable sym
  let
    getConcreteRange :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (PAD.AbsRange tp)
    getConcreteRange e = do
      e' <- asEM @tp $ applyCurrentAsms e
      e'' <- concretizeWithSolver e'
      emitTraceLabel @"expr" "output" (Some e'')
      return $ PAD.extractAbsRange sym e''

  eqCtx <- equivalenceContext
  PPa.forBins $ \bin -> do
    out <- PPa.get bin (PS.simOut bundle)
    pre <- PPa.get bin (PAD.absDomVals preDom)
    PAD.initAbsDomainVals sym eqCtx getConcreteRange out pre

widenUsingCounterexample ::
  sym ->
  PS.SimScope sym arch v ->
  SymGroundEvalFn sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  WidenLocs sym arch {- ^ previous widening -}   ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenUsingCounterexample sym scope evalFn bundle eqCtx postCondAsm postCondStatePred preD _prevLocs postD =
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
  vals' <- PPa.set wb (PAD.absDomVals postD) v
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
  let (oPostState, pPostState) = PEq.asStatePair scope (PS.simOut bundle) PS.simOutState

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
  let (oPostState, pPostState) = PEq.asStatePair scope (PS.simOut bundle) PS.simOutState

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
  let (oPostState, pPostState) = PEq.asStatePair scope (PS.simOut bundle) PS.simOutState
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
  let (oPostState, pPostState) = PEq.asStatePair scope (PS.simOut bundle) PS.simOutState
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
  let (oPostState, pPostState) = PEq.asStatePair scope (PS.simOut bundle) PS.simOutState

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