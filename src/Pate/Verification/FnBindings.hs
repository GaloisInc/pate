{-|
Module           : Pate.Verification.FnBindings
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Representation of post-hoc definitions for uninterpreted functions.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Pate.Verification.FnBindings
  ( FnBindings
  , FnBindingsSpec
  , init
  , merge
  , toScopedPred
  , toPred
  , addUsedFns
  ) where

import           Prelude hiding (init)
import           Control.Monad.Reader
import           Control.Monad.Trans.State
import           Data.Functor.Identity

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.Map ( MapF )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set
import           Data.Set ( Set )

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

import qualified Pate.Binary as PBi
import qualified Pate.ExprMappable as PEM
import qualified Pate.SimState as PS
import qualified Data.Parameterized.TraversableF as TF
import qualified What4.ExprHelpers as WEH

newtype BoundFn sym tp = BoundFn (W4.BoundVar sym tp)

-- | By convention we know that a 'BoundFn' is uninterpreted, so it
--   can be lifted to the global scope
evalBoundFn :: 
  W4.IsSymExprBuilder sym =>
  sym ->
  BoundFn sym tp ->
  IO (PS.ScopedExpr sym tp PS.GlobalScope)
evalBoundFn sym (BoundFn bv) = do
  Some e_scoped <- return $ PS.mkScopedExpr (W4.varExpr sym bv)
  return $ PS.unsafeCoerceScope e_scoped

instance W4.IsSymExprBuilder sym => W4.TestEquality (BoundFn sym) where
  testEquality (BoundFn fn1) (BoundFn fn2) = case W4.testEquality fn1 fn2 of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance W4.IsSymExprBuilder sym => OrdF (BoundFn sym) where
  compareF (BoundFn fn1) (BoundFn fn2) = case compareF fn1 fn2 of
    LTF -> LTF
    EQF -> EQF
    GTF -> GTF

-- | Bindings for uninterpreted functions (i.e. functions that
--   are initially uninterpreted but lazily defined).
--   The functions are implicitly scoped to some global scope
--   (i.e. the state at the point of divergence).
--   The bindings are scoped to the given 'v', with the intention that
--   when 'v' is the same scope as the uninterpreted functions, the
--   binding can then be unfolded.
--   i.e. given a global set of variables 'X' we may start with the bindings
--   F(X) == f_0(y), G(X) == g_0(z)
--   And then when propagated through some number of transformation we eventually
--   reach a point such that:
--   F(X) ==  f_0(f_1(...f_i(X))), G(X) == g_0(g_1(...g_i(X))
--   At which point we can rewrite these functions in any expression
--   containing F(X) or G(X)
--   i.e. P(X)[F(X)/f_0(f_1(...f_i(X))), G(X)/g_0(g_1(...g_i(X))]
--
--   Note that X is implicitly understood (since it is globally defined)
--   and so does not need to actually be passed to the uninterpreted functions.
--
--   The 'bin' parameter specifies which side of the analysis these
--   bindings belong to. Specifically, these functions define the
--   semantics for a single-sided transition that may occur in terms
--   in the other side of the analysis.
data FnBindings sym (bin :: PBi.WhichBinary) (v :: PS.VarScope) =
  FnBindings
    { fnBindings :: MapF (BoundFn sym) (PS.PopScope (PS.ScopedExpr sym) v)
    , fnBindingsUsed :: Set (Some (BoundFn sym))
    }



type FnBindingsSpec sym arch = PS.AbsT (PS.SimSpec sym arch) (FnBindings sym)

instance PS.Scoped (FnBindings sym bin) 

-- | Transform the given value to be globally-scoped by replacing its internal expressions
--   with uninterpreted functions
init ::
  W4.IsSymExprBuilder sym =>
  PS.Scoped f =>
  PEM.ExprMappable sym (f v) =>
  sym ->
  f v ->
  IO (f PS.GlobalScope, FnBindings sym bin v)
init sym e = runStateT (PS.scopedExprMap sym e (mkFreshFns sym)) (FnBindings MapF.empty Set.empty)

mkFreshFns ::
  W4.IsSymExprBuilder sym =>
  sym ->
  PS.ScopedExpr sym tp v ->
  StateT (FnBindings sym bin v) IO (PS.ScopedExpr sym tp PS.GlobalScope)
mkFreshFns sym_ e_scoped = do
  (PS.PopT fn, e_global) <- lift $ PS.liftScope0Ret sym_ $ \sym -> do
    bv <- W4.freshBoundVar sym W4.emptySymbol (W4.exprType (PS.unSE e_scoped))
    return (PS.PopT (BoundFn bv), W4.varExpr sym bv)
  modify $ \(FnBindings binds s) -> FnBindings (MapF.insert fn (PS.PopScope e_scoped) binds) s
  return e_global

-- | Merge the two given function bindings, muxing the individual bindings
--   with the given predicate (i.e. path condition) in the case of 
--   key (uninterpreted function) clashes
merge ::
  forall sym bin v.
  W4.IsSymExprBuilder sym =>
  sym ->
  PS.ScopedExpr sym W4.BaseBoolType v ->
  FnBindings sym bin v ->
  FnBindings sym bin v ->
  IO (FnBindings sym bin v)
merge sym p (FnBindings binds1 s1) (FnBindings binds2 s2) = do
  FnBindings <$> MapF.mergeWithKeyM go return return binds1 binds2 <*> (return $ Set.union s1 s2)
  where
    go :: forall tp.
        BoundFn sym tp ->
        PS.PopScope (PS.ScopedExpr sym) v tp -> 
        PS.PopScope (PS.ScopedExpr sym) v tp -> 
        IO (Maybe (PS.PopScope (PS.ScopedExpr sym) v tp))
    go _fn se1@(PS.PopScope e1) se2@(PS.PopScope e2) = case W4.testEquality se1 se2 of
      Just{} -> return $ Just (PS.PopScope e1)
      Nothing -> (Just . PS.PopScope) <$> (liftIO $ (PS.liftScope3 sym W4.baseTypeIte p e1 e2 ))


toScopedPred ::
  forall sym bin v.
  W4.IsSymExprBuilder sym =>
  sym ->
  FnBindings sym bin v ->
  IO (PS.ScopedExpr sym W4.BaseBoolType v)
toScopedPred sym (FnBindings binds _) = do
  true_ <- PS.liftScope0 sym $ \sym_ -> return $ W4.truePred sym_
  MapF.foldlMWithKey go true_ binds
    where
      go :: forall tp. 
        PS.ScopedExpr sym W4.BaseBoolType v -> 
        BoundFn sym tp -> 
        PS.PopScope (PS.ScopedExpr sym) v tp -> 
        IO (PS.ScopedExpr sym W4.BaseBoolType v)
      go p f (PS.PopScope e) = do
        f_app <- evalBoundFn sym f
        p' <- PS.liftScope2 sym W4.isEq (PS.fromGlobalScope f_app) e
        PS.liftScope2 sym W4.andPred p p'

toPred ::
  forall sym bin v.
  W4.IsSymExprBuilder sym =>
  sym ->
  FnBindings sym bin v ->
  IO (W4.Pred sym)
toPred sym binds = PS.unSE <$> toScopedPred sym binds



-- Note we don't require that 'f' has the same scope as
-- the bindings, since we can collect used bindings from any scope
addUsedFns ::
  PEM.ExprFoldable sym f =>
  (W4B.ExprBuilder t st fs ~ sym) =>
  sym ->
  f ->
  FnBindings sym bin v ->
  FnBindings sym bin v
addUsedFns sym a (FnBindings fns used) =
  let
    collected = runIdentity $ PEM.foldExpr sym (\e coll -> Identity $ WEH.collectVars e coll) a mempty
    usedNew = Set.fromList $ filter (\(Some (BoundFn v)) -> Set.member (Some v) (WEH.colVars collected))  (MapF.keys fns)
  in FnBindings fns (Set.union used usedNew)


instance PEM.ExprMappable sym (FnBindings sym bin v) where
  mapExpr sym f (FnBindings binds s) =
    FnBindings <$> TF.traverseF (\(PS.PopScope se) -> PS.PopScope <$> PEM.mapExpr sym f se) binds <*> return s