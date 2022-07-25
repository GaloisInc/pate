{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Verification.Simplify (
    simplifyPred
  , simplifySubPreds
  , simplifyPred_deep
  , simplifyWithSolver
  , simplifyBVOps_trace
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import           Data.Functor.Const ( Const(..) )
import           Debug.Trace ( traceM )
import           GHC.Stack ( HasCallStack )
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R

import qualified Pate.Config as PC
import qualified Pate.ExprMappable as PEM
import           Pate.Monad
import qualified What4.ExprHelpers as WEH

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
  (forall tp'.
     W4.SymExpr sym tp' ->
     W4.SymExpr sym tp' ->
     EquivM_ sym arch (W4.SymExpr sym tp')) ->
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
simplifyBVOps_trace sym checkWork outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> EquivM_ sym arch (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ WEH.simplifyBVOps' sym checkWork e
  go outer

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
      e2 <- liftIO $ WEH.simplifyBVOps sym e1
      e3 <- liftIO $ WEH.expandMuxEquality sym e2
      return e3

  IO.withRunInIO $ \runInIO -> PEM.mapExpr sym (\e -> runInIO (doSimp e)) a

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
  let
    checkPred :: W4.Pred sym -> EquivM sym arch Bool
    checkPred p' = fmap getConst $ W4B.idxCacheEval cache p' $
      Const <$> isPredTrue' heuristicTimeout p'
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
  -- TODO: redundant sanity check that simplification hasn't clobbered anything
  validSimpl <- liftIO $ W4.isEq sym p p_final
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
