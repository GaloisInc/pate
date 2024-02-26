{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}

module Pate.Verification.ConditionalEquiv (
  checkAndMinimizeEqCondition,
  weakenEqCondition,
  computeEqCondition
  ) where

import           Control.Monad ( join, foldM )
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.IO.Class ( liftIO )

import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import qualified Data.BitVector.Sized as BVS
import           Data.Functor.Const
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import           Data.Set (Set)
import qualified Data.Set as S

import qualified What4.SatResult as W4R
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4

import qualified Pate.AssumptionSet as PAS
import qualified Pate.Config as PC
import qualified Pate.Verification.Simplify as PSi
import           Pate.Monad

import qualified What4.PathCondition as WPC
import qualified What4.ExprHelpers as WEH
import           Pate.TraceTree
---------------------------------------------
-- Conditional Equivalence

computeEqConditionGas :: Int
computeEqConditionGas = 200

-- | Incrementally build an equivalence condition by negating path conditions which
-- induce inequality on the block slices.
-- For each counter example to equivalence, the negated corresponding path condition is assumed,
-- and then the equivalence check is re-attempted.
--
-- This process terminates when the resulting set of assumptions is sufficient to prove
-- equivalence. Termination is guaranteed, because eventually all possible paths through
-- the given slice will be considered.
-- If no equivalence condition is found, then the resulting path condition from this function will be
-- the negation of all possible path conditions, and therefore inconsistent (i.e. representing
-- the degenerate case that @false@ implies equivalence).
--
-- Notes:
--
-- - The 'W4.Pred' input is the postcondition that, if true, would make the original and patched programs equivalent
--
-- - When we get to this function, we know that the equivalence condition does not hold
--
-- - It looks like, at the beginning of this function, the assumptions in scope are:
--
--   1. The assumptions from 'bindSpec'
--   2. The assumptions generated by 'equateInitialStates'
--
-- - This function attempts to find the conditions that can be assumed to make the postcondition satisfiable
--
-- - It does this by repeatedly:
--
--   1. Asking whether or not the goal is satisfiable
--   2. If it is, using the resulting model to construct a blocking clause (via the 'getPathCondition' function)
--   3. Assuming the negation of that clause
--
-- - The computed path condition is the conjunction of the negations of the
--   blocking clauses (i.e., saying that if we don't take any of the problematic
--   paths, then the goal equivalence state is reached)
--
-- NOTE: The "gas" parameter prevents us from getting stuck in an infinite loop,
-- but if it does cut us off, we are likely to not be able to identify a
-- conditional equivalence condition (and will flag it as an unconditional
-- failure)
computeEqCondition ::
  forall sym arch.
  -- | target equivalence predicate
  W4.Pred sym ->
  -- | expressions to extract path conditions from
  Set (Some (W4.SymExpr sym)) ->
  EquivM sym arch (W4.Pred sym)
computeEqCondition eqPred vals = withTracing @"function_name" "computeEqCondition" $ withSym $ \sym -> do
  cond <- go (W4.truePred sym) (W4.truePred sym) computeEqConditionGas
  PSi.simplifyPred cond
  where
    go :: W4.Pred sym -> W4.Pred sym -> Int -> EquivM sym arch (W4.Pred sym)
    go _asms pathCond 0 = return pathCond
    go asms pathCond gas = withTracingLabel @"expr" "step" (Some pathCond) $ withSym $ \sym -> do
      -- can we satisfy equivalence, assuming that none of the given path conditions are taken?
      check <- IO.liftIO $ W4.notPred sym eqPred
      mresult <- goalSat "computeEqCondition" check $ \case
        W4R.Unsat _ -> return Nothing
        -- this is safe, because the resulting condition is still checked later
        W4R.Unknown -> return Nothing
        -- counter-example, compute another path condition and continue
        W4R.Sat fn_ -> Just <$> do
          fn <- wrapGroundEvalFn fn_ (S.singleton (Some eqPred))
          
          binds <- extractBindings fn vals
          subTree @"expr" "Bindings" $ do
            mapM_ (\(MapF.Pair var val) -> subTrace (Some var) $ emitTrace @"expr" (Some val)) (MapF.toList binds)
          

          pathCond' <- getPathCondition fn vals
          emitTraceLabel @"expr" "Assumptions" (Some asms)
          emitTraceLabel @"expr" "Path Condition" (Some pathCond')
          --isSat <- getSatIO

          case W4.asConstantPred pathCond' of
            Just True -> do
   
              return $ pathCond'
            _ -> return pathCond'
      case mresult of
        -- no result, returning the accumulated path conditions
        Nothing -> return pathCond
      -- indeterminate result, failure
        Just unequalPathCond -> do
          notThis <- liftIO $ W4.notPred sym unequalPathCond
          pathCond' <- liftIO $ W4.andPred sym notThis pathCond

          allAsms <- liftIO $ W4.andPred sym notThis asms
          -- assume this path is not taken (if possible) and continue
          mcond <- withSatAssumption (PAS.fromPred notThis) $
            go allAsms pathCond' (gas -1)
          case mcond of
            Just cond_ -> return cond_
            -- if it is not possible to avoid this path, then we've
            -- explored all paths
            Nothing -> return pathCond

addPathCondition ::
  SymGroundEvalFn sym ->
  (W4.Pred sym -> IO (Maybe Bool)) ->
  W4.Pred sym ->
  Some (W4.SymExpr sym) ->
  EquivM_ sym arch (W4.Pred sym)  
addPathCondition fn isSat p (Some e) = withTracing @"function_name" "addPathCondition" $ withValid $ withSym $ \sym -> do
  emitTraceLabel @"expr" "Path Condition For:" (Some e)
  p' <- withGroundEvalFn fn $ \fn' -> do
    WPC.getPathCondition sym fn' isSat e
  emitTraceLabel @"expr" "Path Condition Result:" (Some p')
  liftIO $ W4.andPred sym p p'  

getPathCondition ::
  forall sym arch.
  SymGroundEvalFn sym ->
  Set (Some (W4.SymExpr sym)) ->
  EquivM sym arch (W4.Pred sym)
getPathCondition fn exprs = withSym $ \sym -> do
  isSat <- getSatIO
  foldM (addPathCondition fn isSat) (W4.truePred sym) (S.toList exprs)


-- | Return a function for deciding predicate satisfiability based on the current
-- assumption state. The function caches the result on each predicate, and therefore is
-- only valid under the current set of assumptions (i.e. the 'envCurrentFrame').
-- FIXME: Functionality overlaps with WrappedSolver
getSatIO ::
  forall sym arch.
  EquivM sym arch (W4.Pred sym -> IO (Maybe Bool))
getSatIO = withValid $ do
  cache <- W4B.newIdxCache
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  let
    isSat :: W4.Pred sym -> EquivM sym arch (Maybe Bool)
    isSat p' = case W4.asConstantPred p' of
      Just b -> return $ Just b
      Nothing -> fmap getConst $ W4B.idxCacheEval cache p' $ fmap Const $ do
        r <- checkSatisfiableWithModel goalTimeout "getPathCondition" p' $ \res -> case res of
          W4R.Unsat _ -> return $ Just False
          W4R.Sat _ -> return $ Just True
          W4R.Unknown -> return Nothing
        case r of
          Left _ -> return Nothing
          Right a -> return a

  IO.withRunInIO $ \runInIO -> return (\p -> runInIO (isSat p))

-- | Weaken a given equality condition with alternative paths which also
-- induce equality.
--
-- Similar to computing a sufficient condition, this process necessarily terminates, as
-- eventually the given predicate will cover all possible paths through the slice.
weakenEqCondition ::
  forall sym arch.
  -- | path conditions that (should) induce equivalence
  W4.Pred sym ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  -- | expressions to extract path conditions from
  Set (Some (W4.SymExpr sym)) ->
  EquivM sym arch (W4.Pred sym)
weakenEqCondition pathCond_outer eqPred vals = withSym $ \sym -> do
  let
    go :: W4.Pred sym -> W4.Pred sym -> EquivM sym arch (W4.Pred sym)
    go notPathCond pathCond = do
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      -- we use the heuristic timeout here because we're refining the equivalence condition
      -- and failure simply means we fail to refine it further

      result <- fmap join $ withSatAssumption (PAS.fromPred notPathCond) $ do
        heuristicSat "weakenEqCondition" eqPred $ \case
          W4R.Unsat _ -> return Nothing
          W4R.Unknown -> return Nothing
          -- counter-example, compute another path condition and continue
          W4R.Sat fn_ -> Just <$> do
            fn <- wrapGroundEvalFn fn_ (S.insert (Some eqPred) vals)
            getPathCondition fn vals
      case result of
        Nothing -> return pathCond
        Just unequalPathCond -> do
          isSufficient <- withAssumption (unequalPathCond) $
            isPredTrue' heuristicTimeout eqPred
          pathCond' <- case isSufficient of
            True -> liftIO $ W4.orPred sym unequalPathCond pathCond
            False -> return pathCond
          notPathCond' <- liftIO $ W4.andPred sym notPathCond =<< W4.notPred sym unequalPathCond
          go notPathCond' pathCond'
  notPathCond_outer <- liftIO $ W4.notPred sym pathCond_outer
  go notPathCond_outer pathCond_outer

-- | Given a pair of path conditions, minimize the predicates and
-- verify that they imply equivalence of the block slice.
-- If no equivalence condition exists, then the given pair of path conditions is
-- inconsistent and the result of this function will simply be @false@.
--
-- The resulting predicate is simplified under the current set of assumptions.
checkAndMinimizeEqCondition ::
  forall sym arch.
  -- | path condition that is assumed to imply equivalence
  W4.Pred sym ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
checkAndMinimizeEqCondition cond goal = fnTrace "checkAndMinimizeEqCondition" $ withValid $ withSym $ \sym -> do
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- this check is not strictly necessary, as the incremental checks should guarantee it
  -- for the moment it's a sanity check on this process as well as the final simplifications
  cond' <- PSi.simplifyPred_deep cond >>= \cond' -> (liftIO $ WEH.stripAnnotations sym cond')
  result <- withSatAssumption (PAS.fromPred cond') $ do
    isPredTrue' goalTimeout goal
  case result of
    Just True -> do
      emitTraceLabel @"expr" "success" (Some cond')
      return cond'
    Just False -> do
      notgoal <- liftIO $ W4.notPred sym goal
      
      withAssumption cond' $ 
        goalSat "checkAndMinimizeEqCondition" notgoal $ \case
          W4R.Sat fn -> do
            binds <- extractBindings fn (S.singleton (Some notgoal))
            subTree @"expr" "Bindings" $ do
              mapM_ (\(MapF.Pair var val) ->
                       subTrace (Some var) $ do
                         emitTrace @"expr" (Some val)
                         case W4.exprType var of
                           W4.BaseBVRepr w -> do
                             case W4.asBV val of
                               Just bv -> emitTrace @"message" (show (BVS.clz w bv))
                               Nothing -> return ()
                           _ -> return ()
                    ) (MapF.toList binds)

            emitTraceLabel @"expr" "failure" (Some cond')
            emitTraceLabel @"expr" "goal" (Some goal)
            cond'' <- liftIO $ WEH.applyExprBindings sym binds cond'
            emitTraceLabel @"expr" "failure2" (Some cond'')
            --cond_c <- execGroundFn fn cond'
            --emitTraceLabel @"bool" "Goal Concrete" cond_c
            return $ W4.falsePred sym
          -- unreachable?
          W4R.Unknown -> do
            emitTraceLabel @"expr" "???" (Some cond')
            return $ W4.falsePred sym
          W4R.Unsat{} -> do
            emitTraceLabel @"expr" "success???" (Some cond')
            return $ W4.falsePred sym
    Nothing -> do
      emitTraceLabel @"expr" "unsat" (Some cond')
      -- the computed path condition is not satisfiable
      return $ W4.falsePred sym
