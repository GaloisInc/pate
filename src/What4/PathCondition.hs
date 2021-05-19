{-|
Module           : What4.PathCondition
Copyright        : (c) Galois, Inc 2021
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Computing path conditions over What4 expressions from
SAT models
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module What4.PathCondition
  ( getPathCondition
  , resolveStaticMuxes
  )
  where

import           Control.Applicative
import           Control.Monad.Except
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans.Maybe as MaybeT

import           Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Parameterized.TraversableFC as TFC

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Expr.BoolMap as BM

-- | Compute a predicate representing the path condition of the
-- expression according to its internal mux structure.
-- i.e. given the model @[x := 2, y := 5]@ and the expression
-- @if x > y then (x - y) else (y - x)@,
-- it will produce the predicate @x < y@.
-- Recurses into the sub-structure of predicates to yield a minimal result.
-- i.e. given @if A OR B OR C then D else E@ and a model that sets @A@ to true,
-- but @B@ and @C@ as false, the path condition will contain only @A@.
getPathCondition ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4G.GroundEvalFn t ->
  W4B.Expr t tp -> 
  IO (W4.Pred sym)
getPathCondition sym fn expr = snd <$> runPathM sym fn (withPathCond expr)

resolveStaticMuxes ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4G.GroundEvalFn t ->
  W4B.Expr t tp -> 
  IO (W4B.Expr t tp)
resolveStaticMuxes sym fn expr = fst <$> runPathM sym fn (withPathCond expr)

runPathM ::
  forall sym t solver fs a.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4G.GroundEvalFn t ->
  PathM sym a ->
  IO (a, W4.Pred sym)
runPathM sym fn f = do
  cache <- W4B.newIdxCache
  let
    env = PathMEnv sym fn (W4.truePred sym) cache
    PathM f' = do
      a <- f
      p <- getFullPath
      return (a, p)
  mpred <- liftIO $ MaybeT.runMaybeT $ CMS.evalStateT (CMR.runReaderT f' env) (PathCondition (W4.truePred sym))
  case mpred of
    Just r -> return r
    Nothing -> fail "runPathM: Unexpected inconsistent path condition"

data PathMEnv sym where
  PathMEnv ::
    sym ~ (W4B.ExprBuilder t solver fs) => 
    { _sym :: W4B.ExprBuilder t solver fs
    , _fn :: W4G.GroundEvalFn t
    , pathAsms ::  W4.Pred sym
    , _pathCondCache :: W4B.IdxCache t (ExprAsms sym)
    } ->
    PathMEnv sym

newtype PathCondition sym = PathCondition (W4.Pred sym)

-- | Monad for computing a path condition of an expression
-- with respect to a particular model. The "current" path condition is the conjunction
-- of the path in the environment and the path in the state. The 'MaybeT' transformer
-- allows for early termination when a path in the expression is determined to be infeasible.
newtype PathM sym a = PathM (CMR.ReaderT (PathMEnv sym) (CMS.StateT (PathCondition sym) (MaybeT.MaybeT IO)) a)
  deriving (Functor
           , Applicative
           , Alternative
           , Monad
           , IO.MonadIO
           , CMR.MonadReader (PathMEnv sym)
           , MonadPlus
           , CMS.MonadState (PathCondition sym)
           )

-- | Run a sub-computation, returning the computed predicate, and false on early termination
evalPath ::
  PathM sym a ->
  PathM sym (Maybe a, W4.Pred sym)
evalPath f = withSym $ \sym -> do
  env <- CMR.ask
  path <- getFullPath
  let env' = env { pathAsms = path }
  let (PathM f') = f
  res <- liftIO $ MaybeT.runMaybeT $ CMS.runStateT (CMR.runReaderT f' env') (PathCondition (W4.truePred sym))
  case res of
    Just (a, PathCondition p) -> return (Just a, p)
    Nothing -> return $ (Nothing, W4.falsePred sym)

evalPath_ ::
  PathM sym () ->
  PathM sym (W4.Pred sym)
evalPath_ f = snd <$> evalPath f

-- | Run the sub-computation, and return the resulting path condition.
watchPath ::
  PathM sym a ->
  PathM sym (a, W4.Pred sym)
watchPath f = evalPath f >>= \case
  (Just a, p) -> return (a, p)
  (Nothing, _) -> mzero

withSym :: (W4.IsExprBuilder sym => sym -> PathM sym a) -> PathM sym a
withSym f = do
  PathMEnv sym _ _ _ <- CMR.ask
  f sym

withValid :: forall a sym. (forall t solver fs. sym ~ (W4B.ExprBuilder t solver fs) => PathM sym a) -> PathM sym a
withValid f = do
  PathMEnv{} <- CMR.ask
  f

getFullPath :: PathM sym (W4.Pred sym)
getFullPath = withSym $ \sym -> do
  asms <- CMR.asks pathAsms
  PathCondition path <- CMS.get
  liftIO $ W4.andPred sym asms path

-- | Drop the current path condition if it is inconsistent (i.e. assumes false).
dropInconsistent :: PathM sym ()
dropInconsistent = withValid $ do
  p <- getFullPath
  case W4.asConstantPred p of
    Just False -> mzero
    _ -> return ()

-- | Run the given sub-computation with the given predicate assumed
-- (with the given polarity). Terminates early if the resulting set of
-- assumptions is inconsistent.
addAsm ::
  W4.Pred sym ->
  BM.Polarity ->
  PathM sym ()
addAsm p pol = withSym $ \sym -> do
  p' <- applyPolarity pol p 
  PathCondition path <- CMS.get
  path' <- liftIO $ W4.andPred sym path p'
  CMS.put (PathCondition path')
  dropInconsistent


applyPolarity ::
  BM.Polarity ->
  W4.Pred sym ->
  PathM sym (W4.Pred sym)  
applyPolarity BM.Positive p = return p
applyPolarity BM.Negative p = withSym $ \sym -> liftIO $ W4.notPred sym p

groundEval ::
  W4.SymExpr sym tp ->
  PathM sym (W4G.GroundValue tp)
groundEval e = do
  PathMEnv _ fn _ _ <- CMR.ask
  liftIO (W4G.groundEval fn e)

forMuxes ::
  forall sym tp a.
  W4.SymExpr sym tp ->
  (W4.SymExpr sym tp -> PathM sym a) ->
  PathM sym a
forMuxes e_outer f = go e_outer
  where
    go :: W4.SymExpr sym tp -> PathM sym a
    go e = withValid $ case W4B.asApp e of
      Just (W4B.BaseIte _ _ cond eT eF) ->
        do
          getPredCase BM.Positive cond
          go eT
        <|> do
          getPredCase BM.Negative cond
          go eF
      _ -> f e

forMuxes2 ::
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  (W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> PathM sym a) ->
  PathM sym a
forMuxes2 e1_outer e2_outer f = forMuxes e1_outer (\e1 -> forMuxes e2_outer (f e1))


fromPolarity ::
  BM.Polarity -> Bool
fromPolarity BM.Positive = True
fromPolarity BM.Negative = False

liftBinOp ::
  (sym -> W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO a) ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  PathM sym a
liftBinOp f e1 e2 = withSym $ \sym -> liftIO $ f sym e1 e2

altBinOp ::
  (W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> PathM sym a) ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  PathM sym a
altBinOp f e1 e2 = forMuxes2 e1 e2 $ \e1' e2' -> do
  e1'' <- withPathCond e1'
  e2'' <- withPathCond e2'
  f e1'' e2''

-- | From a signed operation, consider separately the case where both
-- operands are signed
altBVOp ::
  (W4.SymBV sym w1  -> W4.SymBV sym w2  -> PathM sym a) ->
  W4.SymBV sym w1 ->
  W4.SymBV sym w2 ->
  PathM sym a
altBVOp f_signed e1 e2 = withSym $ \sym -> forMuxes2 e1 e2 $ \e1' e2' -> do
  e1'' <- withPathCond e1'
  e2'' <- withPathCond e2'  
  unsigned1 <- liftIO $ isUnsigned sym e1''
  unsigned2 <- liftIO $ isUnsigned sym e2''
  unsigned <- liftIO $ W4.andPred sym unsigned1 unsigned2
  (do    
      getPredCase BM.Positive unsigned 
      f_signed e1'' e2'')
   <|>
    (do
      getPredCase BM.Negative unsigned 
      f_signed e1'' e2'')


-- | True if this bitvector has the same signed vs. unsigned interpretation
isUnsigned ::
  W4.IsExprBuilder sym =>
  sym ->
  W4.SymBV sym w ->
  IO (W4.Pred sym)
isUnsigned sym bv = do
  W4.BaseBVRepr _ <- return $ W4.exprType bv
  clz <- W4.bvCountLeadingZeros sym bv
  -- must have at least one leading zero
  W4.bvIsNonzero sym clz  

  
-- | Compute a set of assumptions that are sufficient for the given predicate to
-- have the given polarity in the given model.
-- If the predicate disagrees with the given polarity, then no results
-- are produced (i.e. this branch was not taken in the model).
-- 
getPredCase ::
  forall sym. 
  BM.Polarity ->
  W4.Pred sym ->
  PathM sym ()
getPredCase pol_outer e_outer = do
  p <- go pol_outer e_outer
  addAsm p BM.Positive
  where
    
    binOp ::
      forall tp1 tp2.
      BM.Polarity ->
      (sym -> W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO (W4.Pred sym)) ->
      W4.SymExpr sym tp1 ->
      W4.SymExpr sym tp2 ->
      PathM sym (W4.Pred sym)
    binOp pol f e1 e2 = altBinOp (\e1' e2' -> liftBinOp f e1' e2' >>= applyPolarity pol) e1 e2

    bvOp ::
      forall w1 w2.
      BM.Polarity ->
      (sym -> W4.SymBV sym w1  -> W4.SymBV sym w2  -> IO (W4.Pred sym)) ->
      W4.SymBV sym w1 ->
      W4.SymBV sym w2 ->
      PathM sym (W4.Pred sym)      
    bvOp pol f e1 e2 =
      altBVOp
        (\e1' e2' -> liftBinOp f e1' e2' >>= applyPolarity pol)
        e1 e2 
    
    go :: BM.Polarity -> W4.Pred sym -> PathM sym (W4.Pred sym)
    go pol e_inner = withValid $ withSym $ \sym -> forMuxes e_inner $ \e -> do
      -- only consider cases where the polarity agrees with the model
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e)
      predAgrees pol e
      case e of
          -- recurse into substructure
          W4B.AppExpr a0 -> case W4B.appExprApp a0 of
            (W4B.ConjPred bm) -> do
              case pol of
                -- each conjunct must be true
                -- yield a single set of predicates which makes all conjuncts true when assumed
                BM.Positive -> do
                  let eval (x, pol') = do
                        p <- go pol' x
                        addAsm p BM.Positive
                        
                  case BM.viewBoolMap bm of
                     BM.BoolMapUnit -> return $ W4.truePred sym
                     BM.BoolMapDualUnit -> return $ W4.falsePred sym
                     BM.BoolMapTerms (t:|ts) -> evalPath_ $ mapM_ eval (t:ts)
                -- one conjunct must be false
                -- for each conjuct: yield a disjunction of primitive conditions
                -- which falsify this predicate in the model
                BM.Negative -> do
                  let eval p (x, pol') = (evalPath $ go (BM.negatePolarity pol') x) >>= \case
                        (Just p', p'') -> do
                          p''' <- liftIO $ W4.andPred sym p' p''
                          liftIO $ W4.orPred sym p p'''
                        (Nothing, _) -> return p
                  case BM.viewBoolMap bm of
                    -- a statically true boolmap cannot be made false
                    BM.BoolMapUnit -> return $ W4.falsePred sym
                    BM.BoolMapDualUnit -> return $ W4.truePred sym
                    -- any one result can be made false 
                    BM.BoolMapTerms (t:|ts) -> foldM eval (W4.falsePred sym) (t:ts)

            W4B.NotPred p -> go (BM.negatePolarity pol) p
            W4B.BaseEq _ e1 e2 -> binOp pol W4.isEq e1 e2
            W4B.BVUlt e1 e2 -> binOp pol W4.bvUlt e1 e2
             
            -- add explicit signed check to signed comparison
            W4B.BVSlt e1 e2 -> bvOp pol W4.bvSlt e1 e2

            -- catch-all: assume the entire predicate
            _ -> applyPolarity pol e
          _ -> applyPolarity pol e

-- | No-op if the predicate agrees with the given polarity in the model.
-- Otherwise, terminates early.
predAgrees ::
  BM.Polarity ->
  W4.Pred sym ->
  PathM sym ()  
predAgrees pol p = do
  result <- groundEval p
  case result == (fromPolarity pol) of
    True -> return ()
    False -> mzero


data ExprAsms sym tp where
  ExprAsms :: W4.SymExpr sym tp -> W4.Pred sym -> ExprAsms sym tp

-- | Compute the set of assumptions used to induce the value of the given
-- expression in the model, based on its internal mux structure.
-- Resolve to an expression that is equal to the given one in the given model, but
-- which contains no muxes internally (i.e. all muxes have been statically resolved).
withPathCond ::
  forall sym tp.
  W4.SymExpr sym tp ->
  PathM sym (W4.SymExpr sym tp)
withPathCond e_outer = withValid $ do
  PathMEnv sym _ _ cache <- CMR.ask
  let
    watch :: forall tp'.
      PathM sym (W4.SymExpr sym tp') ->
      PathM sym (ExprAsms sym tp')
    watch f = fmap (uncurry ExprAsms) $ watchPath f
    
    bvOp ::
      forall w1 w2 tp3.
      (sym -> W4.SymBV sym w1  -> W4.SymBV sym w2  -> IO (W4.SymExpr sym tp3)) ->
      W4.SymBV sym w1 ->
      W4.SymBV sym w2 ->
      PathM sym (ExprAsms sym tp3)      
    bvOp f e1 e2 =
      altBVOp
        (\e1' e2' -> watch $ liftBinOp f e1' e2')
        e1 e2 
    
    go :: forall tp'. W4.SymExpr sym tp' -> PathM sym (W4.SymExpr sym tp')
    go e_inner = do
      ExprAsms e' p <- go_rec e_inner
      addAsm p BM.Positive
      return e'
    
    go_rec :: forall tp'. W4.SymExpr sym tp' -> PathM sym (ExprAsms sym tp')
    go_rec e_inner = W4B.idxCacheEval cache e_inner $ do
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e_inner)
      
      forMuxes e_inner $ \e -> do
        case e of
          W4B.AppExpr a0 -> case W4B.appExprApp a0 of
            W4B.BVAshr _ e1 e2 -> bvOp W4.bvAshr e1 e2
            W4B.BVSdiv _ e1 e2 -> bvOp W4.bvSdiv e1 e2
            W4B.BVSext w e1 -> bvOp (\_sym e1' _ -> W4.bvSext sym w e1') e1 e1
            app -> watch $ do
              a0' <- W4B.traverseApp go app
              if (W4B.appExprApp a0) == a0' then return e
              else liftIO $ W4B.sbMakeExpr sym a0'
          W4B.NonceAppExpr a0 -> watch $ do
            a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
            if (W4B.nonceExprApp a0) == a0' then return e
            else liftIO $ W4B.sbNonceExpr sym a0'
          _ -> return $ ExprAsms e (W4.truePred sym)
  go e_outer
