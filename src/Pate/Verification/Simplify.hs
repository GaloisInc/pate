{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE OverloadedStrings #-}

module Pate.Verification.Simplify (
    simplifyPred
  , simplifySubPreds
  , simplifyPred_deep
  , simplifyWithSolver
  , simplifyBVOps_trace
  , Simplifier
  , applySimplifier
  , runSimplifier
  , getSimplifier
  , deepPredicateSimplifier
  , prettySimplifier
  ) where

import           Control.Monad (foldM)
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import           Data.Functor.Const ( Const(..) )
import           Data.Parameterized.Some
import           Debug.Trace ( traceM )
import           Data.Proxy
import           GHC.Stack ( HasCallStack )
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R

import qualified Pate.Config as PC
import qualified Pate.ExprMappable as PEM
import qualified Pate.Equivalence.Error as PEE
import           Pate.Monad
import qualified What4.ExprHelpers as WEH
import           Pate.TraceTree
import qualified Data.Set as Set
import Pate.AssumptionSet

-- | Under the current assumptions, attempt to collapse a predicate
-- into either trivially true or false
simplifyPred ::
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
simplifyPred p = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  isPredSat heuristicTimeout p >>= \case
    True -> isPredTrue' heuristicTimeout p >>= \case
      True -> return $ W4.truePred sym
      False -> return p
    False -> return $ W4.falsePred sym

simplifySubPreds ::
  forall sym arch f.
  HasCallStack =>
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
simplifySubPreds a = withValid $ withSym $ \sym -> do
  (cache :: W4B.IdxCache t (W4B.Expr t)) <- W4B.newIdxCache
  let
    simplifyPred' ::
      W4B.Expr t tp ->
      EquivM sym arch (W4B.Expr t tp)
    simplifyPred' e = case W4.exprType e of
      W4.BaseBoolRepr ->  W4B.idxCacheEval cache e $ simplifyPred e
      _ -> return e
  IO.withRunInIO $ \runInIO -> PEM.mapExpr sym (\e -> runInIO (simplifyPred' e)) a


simplifyBVOps_trace ::
  forall sym arch t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  WEH.SimpCheck sym (EquivM_ sym arch) ->
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
simplifyBVOps_trace sym checkWork outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> EquivM_ sym arch (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ WEH.simplifyBVOps' sym checkWork e
  go outer

-- | Performs the following simplifications:
-- Resolves any concrete array lookups with 'WEH.resolveConcreteLookups'
-- Simplifies various bitvector operations using 'WEH.simplifyBVOps'
-- The solver is used to decide equality for array accesses when resolving
-- concrete lookups, and it is used to validate the result of simplification
-- (i.e. the simplified expression should be provably equal to the original).
-- Solver timeouts are handled by considering the result to be unknown -
-- i.e. a 'Nothing' result from 'concretePred', which is treated the same
-- as the case where a predicate is neither concretely true nor false (i.e.
-- the simplifier cannot prune either branch).
simplifyWithSolver ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
simplifyWithSolver a = withValid $ withSym $ \sym -> do
  ecache <- W4B.newIdxCache
  pcache <- W4B.newIdxCache
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  let

    checkPred :: W4.Pred sym -> EquivM_ sym arch (Maybe Bool)
    checkPred p' = fmap (getConst) $ W4B.idxCacheEval pcache p' $
      Const <$> concretePred heuristicTimeout p'
  
    doSimp :: forall tp. W4.SymExpr sym tp -> EquivM sym arch (W4.SymExpr sym tp)
    doSimp e = W4B.idxCacheEval ecache e $ do
      e1 <- WEH.resolveConcreteLookups sym checkPred e
      e2 <- WEH.simplifyBVOps' sym tracedSimpCheck e1
      WEH.runSimpCheck tracedSimpCheck e e2

  IO.withRunInIO $ \runInIO -> PEM.mapExpr sym (\e -> runInIO (doSimp e)) a

tracedSimpCheck :: forall sym arch. WEH.SimpCheck sym (EquivM_ sym arch)
tracedSimpCheck = WEH.SimpCheck (emitTrace @"debug") $ \ce_trace e_orig e_simp -> withValid $ withSym $ \sym -> do
  not_valid <- liftIO $ (W4.isEq sym e_orig e_simp >>= W4.notPred sym)
  withTracing @"debug" "Goal" $ emitTrace @"expr" (Some not_valid)
  goalSat "tracedSimpCheck" not_valid $ \case
    W4R.Unsat{} -> return e_simp
    W4R.Unknown{} -> do
      withTracing @"debug" "Unknown Simplifier Check Result" $ do
        emitTraceLabel @"expr" "original" (Some e_orig)
        emitTraceLabel @"expr" "simplified" (Some e_simp)
        emitError $ PEE.InconsistentSimplificationResult (PEE.SimpResult (Proxy @sym) e_orig e_simp)
        return e_orig
    W4R.Sat fn -> do
      withTracing @"debug" "Invalid Simplifier Check Result" $ do
        emitTraceLabel @"expr" "original" (Some e_orig)
        emitTraceLabel @"expr" "simplified" (Some e_simp)
        e_orig_conc <- concretizeWithModel fn e_orig
        e_simp_conc <- concretizeWithModel fn e_simp
        do
          SymGroundEvalFn fn' <- return fn
          WEH.runCETracer ce_trace fn'
        vars <- fmap Set.toList $ liftIO $ WEH.boundVars e_orig
        binds <- foldM (\asms (Some var) -> do
          conc <- concretizeWithModel fn (W4.varExpr sym var)
          return $ asms <> (exprBinding @sym (W4.varExpr sym var) conc)) mempty vars
        withTracing @"debug" "Counterexample" $ do
          emitTraceLabel @"expr" "original concrete" (Some e_orig_conc)
          emitTraceLabel @"expr" "simplified concrete" (Some e_simp_conc)
          emitTrace @"assumption" binds
        emitError $ PEE.InconsistentSimplificationResult (PEE.SimpResult (Proxy @sym) e_orig e_simp)
        return e_orig

getSimpCheck :: EquivM sym arch (WEH.SimpCheck sym (EquivM_ sym arch))
getSimpCheck = do
  shouldCheck <- CMR.asks (PC.cfgCheckSimplifier . envConfig)
  case shouldCheck of
    True -> withSym $ \sym -> do
      cache_def_simp <- W4B.newIdxCache
      return $ WEH.wrapSimpSolverCheck (WEH.unfoldDefinedFns sym (Just cache_def_simp)) tracedSimpCheck
    False -> return WEH.noSimpCheck


-- | Simplify a predicate by considering the
-- logical necessity of each atomic sub-predicate under the current set of assumptions.
-- Additionally, simplify array lookups across unrelated updates.
simplifyPred_deep ::
  forall sym arch.
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
simplifyPred_deep p = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  cache <- W4B.newIdxCache
  fn_cache <- W4B.newIdxCache
  let
    checkPred :: W4.Pred sym -> EquivM sym arch Bool
    checkPred p' = fmap getConst $ W4B.idxCacheEval cache p' $ do
      p'' <- WEH.unfoldDefinedFns sym (Just fn_cache) p'
      Const <$> isPredTrue' heuristicTimeout p''
  -- remove redundant atoms
  p1 <- WEH.minimalPredAtoms sym (\x -> checkPred x) p
  -- resolve array lookups across unrelated updates
  p2 <- WEH.resolveConcreteLookups sym (\p' -> return $ W4.asConstantPred p') p1
  -- additional bitvector simplifications
  p3 <- liftIO $ WEH.simplifyBVOps sym p2
  -- drop any muxes across equality tests
  p4 <- liftIO $ WEH.expandMuxEquality sym p3
  -- remove redundant conjuncts
  p_final <- WEH.simplifyConjuncts sym (\x -> checkPred x) p4
  p_final' <- WEH.unfoldDefinedFns sym (Just fn_cache) p_final
  p' <- WEH.unfoldDefinedFns sym (Just fn_cache) p
  -- TODO: redundant sanity check that simplification hasn't clobbered anything
  validSimpl <- liftIO $ W4.isEq sym p' p_final'
  goal <- liftIO $ W4.notPred sym validSimpl
  r <- checkSatisfiableWithModel heuristicTimeout "SimplifierConsistent" goal $ \sr ->
    case sr of
      W4R.Unsat _ -> return p_final
      W4R.Sat _ -> do
        traceM "ERROR: simplifyPred_deep: simplifier broken"
        traceM "Original:"
        traceM (show (W4.printSymExpr p))
        traceM "Simplified:"
        traceM (show (W4.printSymExpr p_final))
        return p
      W4R.Unknown -> do
        traceM ("WARNING: simplifyPred_deep: simplifier timeout")
        return p
  case r of
    Left exn -> do
      traceM ("ERROR: simplifyPred_deep: exception " ++ show exn)
      return p
    Right r' -> return r'





data Simplifier sym arch = Simplifier { runSimplifier :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (W4.SymExpr sym tp) }

instance Semigroup (Simplifier sym arch) where
  (Simplifier f1) <> (Simplifier f2) = Simplifier $ \e -> f1 e >>= f2

instance Monoid (Simplifier sym arch) where
  mempty = Simplifier pure

applySimplifier ::
  PEM.ExprMappable sym v =>
  Simplifier sym arch ->
  v ->
  EquivM sym arch v
applySimplifier simplifier v = withSym $ \sym -> do
  shouldCheck <- CMR.asks (PC.cfgCheckSimplifier . envConfig)
  case shouldCheck of
    True -> withTracing @"debug_tree" "Simplifier" $ PEM.mapExpr sym (runSimplifier simplifier) v
    False -> withNoTracing $ PEM.mapExpr sym (runSimplifier simplifier) v

deepPredicateSimplifier :: forall sym arch. EquivM sym arch (Simplifier sym arch)
deepPredicateSimplifier = withSym $ \sym -> do
  Simplifier f <- getSimplifier
  return $ Simplifier $ \e0 ->  do
    e1 <- liftIO $ WEH.stripAnnotations sym e0
    e2 <- f e1
    e4 <- case W4.exprType e0 of
      W4.BaseBoolRepr -> simplifyPred_deep e2
      _ -> return e2
    applyCurrentAsms e4

-- | Simplified that should only be used to display terms
prettySimplifier :: forall sym arch. EquivM sym arch (Simplifier sym arch)
prettySimplifier = return $ Simplifier $ \e0 -> withSym $ \sym -> do
  simp_check <- getSimpCheck
  WEH.bvPrettySimplify sym simp_check e0

getSimplifier :: forall sym arch. EquivM sym arch (Simplifier sym arch)
getSimplifier = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  conccache <- W4B.newIdxCache
  ecache <- W4B.newIdxCache
  
  let
    concPred :: W4.Pred sym -> EquivM_ sym arch (Maybe Bool)
    concPred p | Just b <- W4.asConstantPred p = return $ Just b
    concPred p = getConst <$> (W4B.idxCacheEval conccache p $ do
                                  emitTraceLabel @"expr" "concPred_input" (Some p)
                                  concretePred heuristicTimeout p >>= \case
                                    Just b -> (emitTrace @"message" "concrete" >> return (Const (Just b)))
                                    Nothing -> (emitTrace @"message" "abstract" >> return (Const Nothing))
                               )
    simp_wrapped :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (W4.SymExpr sym tp)
    simp_wrapped e = W4B.idxCacheEval ecache e $ do
      e' <- withNoTracing $ simp WEH.noSimpCheck e
      shouldCheck <- CMR.asks (PC.cfgCheckSimplifier . envConfig)
      case shouldCheck of
        True -> withTracing @"debug_tree" "Simplifier Check" $ do
          e'' <- WEH.runSimpCheck tracedSimpCheck e e'
          case W4.testEquality e' e'' of
            Just W4.Refl -> return e''
            Nothing -> do
              -- re-run the simplifier with tracing enabled
              _ <- simp tracedSimpCheck e
              return e
        False -> return e'

    simp :: forall tp. WEH.SimpCheck sym (EquivM_ sym arch) -> W4.SymExpr sym tp -> EquivM_ sym arch (W4.SymExpr sym tp)
    simp _ e | Just{} <- W4.asConcrete e = return e
    simp simpCheck e = do
      -- TODO: clean up this tracing a bit
      e1 <- WEH.resolveConcreteLookups sym concPred e
      emitIfChanged "resolveConcreteLookups" e e1
      -- valid <- liftIO $ W4.isEq sym e e1
      e2 <- WEH.simplifyBVOps' sym simpCheck e1
      emitIfChanged "simplifyBVOps" e1 e2
      e3 <- liftIO $ WEH.fixMux sym e2
      emitIfChanged "fixMux" e2 e3
      return e3
  return $ Simplifier $ \v -> PEM.mapExpr sym simp_wrapped v

emitIfChanged ::
  ExprLabel ->
  W4.SymExpr sym tp ->
  W4.SymExpr sym tp ->
  EquivM sym arch ()
emitIfChanged msg e1 e2 = case W4.testEquality e1 e2 of
  Just W4.Refl -> return ()
  Nothing -> emitTraceLabel @"expr" msg (Some e2) >> return ()
