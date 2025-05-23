{-|
Module           : What4.ExprHelpers
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Helper functions for manipulating What4 expressions
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
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings   #-}

module What4.ExprHelpers (
    iteM
  , impM
  , andM
  , orM
  , allPreds
  , anyPred
  , ExprBindings
  , mergeBindings
  , applyExprBindings
  , applyExprBindings'
  , VarBindCache
  , freshVarBindCache
  , rewriteSubExprs
  , rewriteSubExprs'
  , mapExprPtr
  , mapExprPtr2
  , freshPtr
  , freshPtrBytes
  , ExprFilter(..)
  , getIsBoundFilter
  , BoundVarBinding(..)
  , groundToConcrete
  , fixMux
  , ExprSet
  , ppExprSet
  , getPredAtoms
  , abstractOver
  , resolveConcreteLookups
  , minimalPredAtoms
  , expandMuxEquality
  , simplifyBVOps
  , simplifyBVOps'
  , simplifyConjuncts
  , boundVars
  , idxCacheEvalWriter
  , Tagged
  , assumePositiveInt
  , integerToNat
  , asConstantOffset
  , HasIntegerToNat(..)
  , stripAnnotations
  , assertPositiveNat
  , printAtoms
  , iteToImp
  , unfoldDefinedFns
  -- re-exports from What4.Simplify
  , setProgramLoc
  , Simplifier(..)
  , mkSimplifier
  , SimpStrategy(..)
  , joinStrategy
  , mkSimpleStrategy
  , SimpCheck(..)
  , wrapSimpSolverCheck
  , runSimpCheck
  , noSimpCheck
  -- re-exports from What4.Simplify.Bitvector
  , W4SBV.bvPrettySimplify
  , W4SBV.memReadPrettySimplify
  , W4SBV.collapseBVOps
  , bvUMax
  , bvUMin
  , SymFnCollector(..)
  , collectSymFns
  , VarCollector(..)
  , collectVars
  ) where

import           GHC.TypeNats
import           Unsafe.Coerce ( unsafeCoerce ) -- for mulMono axiom

import           Control.Applicative
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.ST ( RealWorld, stToIO )
import qualified Control.Monad.Writer as CMW

import           Control.Monad.Trans (lift, MonadTrans(..))
import           Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import qualified System.IO as IO

import qualified Prettyprinter as PP

import           Data.Foldable (foldlM, foldrM)
import qualified Data.BitVector.Sized as BVS
import qualified Data.HashTable.ST.Basic as H
import           Data.Word (Word64)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List ( foldl' )
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Proxy (Proxy(..))

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( Pair(..) )

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.ArrayUpdateMap as AUM
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Interface as W4
import qualified What4.Concrete as W4C
import qualified What4.SemiRing as SR
import qualified What4.Expr.BoolMap as BM
import qualified What4.Symbol as WS
import qualified What4.Utils.AbstractDomains as W4AD
import           What4.Simplify

import           Data.Parameterized.SetF (SetF)
import qualified Data.Parameterized.SetF as SetF
import Data.Maybe (fromMaybe)
import qualified What4.Simplify.Bitvector as W4SBV
import           What4.Simplify.Bitvector (asSimpleSum)

bvUMax :: 
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  1 <= w =>
  sym ->
  W4.SymBV sym w ->
  W4.SymBV sym w ->
  m (W4.SymBV sym w)
bvUMax sym bv1 bv2 = IO.liftIO $ do
  ult <- W4.bvUlt sym bv1 bv2
  W4.bvIte sym ult bv2 bv1

bvUMin :: 
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  1 <= w =>
  sym ->
  W4.SymBV sym w ->
  W4.SymBV sym w ->
  m (W4.SymBV sym w)
bvUMin sym bv1 bv2 = IO.liftIO $ do
  ult <- W4.bvUlt sym bv1 bv2
  W4.bvIte sym ult bv1 bv2

-- | Sets the abstract domain of the given integer to assume
--   that it is positive. 
assumePositiveInt ::
  W4.IsExprBuilder sym =>
  sym ->
  W4.SymExpr sym W4.BaseIntegerType ->
  W4.SymExpr sym W4.BaseIntegerType
assumePositiveInt _sym e = 
  let
    rng = W4AD.rangeMax (W4AD.singleRange 0) (W4.integerBounds e)
  in W4.unsafeSetAbstractValue rng e

-- | Redundant assumption that ensures regions are consistent
assertPositiveNat ::
  W4.IsExprBuilder sym =>
  sym ->
  W4.SymNat sym ->
  IO (W4.Pred sym)
assertPositiveNat sym e = do
  let i = W4.natToIntegerPure e
  let e' = W4.unsafeSetAbstractValue W4AD.unboundedRange i
  zero <- W4.intLit sym 0
  W4.intLe sym zero e'

-- | Copied from https://github.com/GaloisInc/what4/commit/de5e73170b98e1f7e9c9baa9f044e2dfd21016cb
--   Using this definition for 'intMax' allows more abstract domain information to be used
--   in order to statically determine the result. Additionally the resulting expression
--   contains a more precise abstract domain based on the semantics of 'max'.
intMax ::
  W4.IsExprBuilder sym =>
  sym ->
  W4.SymInteger sym ->
  W4.SymInteger sym ->
  IO (W4.SymInteger sym)
intMax sym x y =
  do x_le_y <- W4.intLe sym x y
     y_le_x <- W4.intLe sym y x
     case (W4.asConstantPred x_le_y, W4.asConstantPred y_le_x) of
       -- x <= y
       (Just True, _) -> return y
       -- x < y
       (_, Just False) -> return y
       -- y < x
       (Just False, _) -> return x
       -- y <= x
       (_, Just True) -> return x
       _ ->
         do let rng_x = W4.integerBounds x
            let rng_y = W4.integerBounds y
            W4.unsafeSetAbstractValue (W4AD.rangeMax rng_x rng_y) <$>
              W4.intIte sym x_le_y y x

-- | Overriding 'W4.integerToNat' to use a modified 'intMax' that
--   statically evaluates in more cases. In particular this ensures that
--   integers with a positive abstract domain aren't wrapped in any additional checks,
--   and that the inner integer is statically known to be positive.
integerToNat ::
  W4.IsExprBuilder sym =>
  sym ->
  W4.SymExpr sym W4.BaseIntegerType ->
  IO (W4.SymNat sym)
integerToNat sym x = unsafeIntToNat <$> (intMax sym x =<< W4.intLit sym 0)

unsafeIntToNat ::
  W4.IsExprBuilder sym =>
  W4.SymExpr sym W4.BaseIntegerType ->
  W4.SymNat sym
unsafeIntToNat i = unsafeCoerce i


iteM ::
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  m (W4.Pred sym) ->
  m (W4.SymExpr sym tp) ->
  m (W4.SymExpr sym tp) ->
  m (W4.SymExpr sym tp)
iteM sym p fT fF = do
  p' <- p
  case W4.asConstantPred p' of
    Just True -> fT
    Just False -> fF
    Nothing -> do
      fT' <- fT
      fF' <- fF
      IO.liftIO $ W4.baseTypeIte sym p' fT' fF'

impM ::
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  m (W4.Pred sym) ->
  m (W4.Pred sym) ->
  m (W4.Pred sym)
impM sym pPre pPost = do
  pPre' <- pPre
  case W4.asConstantPred pPre' of
    Just True -> pPost
    Just False -> return $ W4.truePred sym
    _ -> do
      pPost' <- pPost
      IO.liftIO $ W4.impliesPred sym pPre' pPost'

andM ::
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  m (W4.Pred sym) ->
  m (W4.Pred sym) ->
  m (W4.Pred sym)
andM sym p1 p2 = do
  p1' <- p1
  case W4.asConstantPred p1' of
    Just True -> p2
    Just False -> return $ W4.falsePred sym
    _ -> do
      p2' <- p2
      IO.liftIO $ W4.andPred sym p1' p2'


orM ::
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  m (W4.Pred sym) ->
  m (W4.Pred sym) ->
  m (W4.Pred sym)
orM sym p1 p2 = do
  p1' <- p1
  case W4.asConstantPred p1' of
    Just True -> return $ W4.truePred sym
    Just False -> p2
    _ -> do
      p2' <- p2
      IO.liftIO $ W4.orPred sym p1' p2'

allPreds ::
  W4.IsExprBuilder sym =>
  sym ->
  [W4.Pred sym] ->
  IO (W4.Pred sym)
allPreds sym preds = foldr (\p -> andM sym (return p)) (return $ W4.truePred sym) preds

anyPred ::
  W4.IsExprBuilder sym =>
  sym ->
  [W4.Pred sym] ->
  IO (W4.Pred sym)
anyPred sym preds = foldr (\p -> orM sym (return p)) (return $ W4.falsePred sym) preds


-- | A variable binding environment used internally by 'rewriteSubExprs', associating
-- sub-expressions which have been replaced by variables
newtype VarBinds sym = VarBinds (MapF.MapF (W4.SymExpr sym) (SetF (W4.BoundVar sym)))

instance (OrdF (W4.BoundVar sym), OrdF (W4.SymExpr sym)) => Semigroup (VarBinds sym) where
  (VarBinds v1) <> (VarBinds v2) = VarBinds $
    MapF.mergeWithKey (\_ bvs1 bvs2 -> Just (bvs1 <> bvs2)) id id v1 v2

instance (OrdF (W4.BoundVar sym), OrdF (W4.SymExpr sym)) => Monoid (VarBinds sym) where
  mempty = VarBinds MapF.empty

toAssignmentPair ::
  [Pair f g] ->
  Pair (Ctx.Assignment f) (Ctx.Assignment g)
toAssignmentPair [] = Pair Ctx.empty Ctx.empty
toAssignmentPair ((Pair a1 a2):xs) | Pair a1' a2' <- toAssignmentPair xs =
  Pair (a1' Ctx.:> a1) (a2' Ctx.:> a2)

flattenVarBinds ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  VarBinds sym ->
  [Pair (W4.BoundVar sym) (W4.SymExpr sym)]
flattenVarBinds (VarBinds binds) = concat $ map go (MapF.toList binds)
  where
    go :: Pair (W4.SymExpr sym) (SetF (W4.BoundVar sym)) -> [Pair (W4.BoundVar sym) (W4.SymExpr sym)]
    go (Pair e bvs) = map (\bv -> Pair bv e) $ SetF.toList bvs

toBindings ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  VarBinds sym ->
  Pair (Ctx.Assignment (W4.BoundVar sym)) (Ctx.Assignment (W4.SymExpr sym))
toBindings varBinds = toAssignmentPair (flattenVarBinds varBinds)

-- | Traverse an expression and rewrite any sub-expressions according to the given
-- replacement function, rebuilding as necessary. If a replacement occurs, the resulting
-- sub-expression is not traversed any further.
rewriteSubExprs ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  (forall tp'. W4B.Expr t tp' -> Maybe (W4B.Expr t tp')) ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rewriteSubExprs sym f e = do
  cache <- freshVarBindCache
  rewriteSubExprs' sym cache f e
  
data VarBindCache sym where
  VarBindCache :: sym ~ W4B.ExprBuilder t solver fs =>
    W4B.IdxCache t (Tagged (VarBinds sym) (W4B.Expr t))
    -> W4B.IdxCache t (W4B.Expr t)
    -> VarBindCache sym

freshVarBindCache ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  IO (VarBindCache sym)
freshVarBindCache = VarBindCache <$> W4B.newIdxCache <*> W4B.newIdxCache

rewriteSubExprs' ::
  forall sym tp m.
  IO.MonadIO m =>
  sym ->
  VarBindCache sym ->
  (forall tp'. W4.SymExpr sym tp' -> Maybe (W4.SymExpr sym tp')) ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
rewriteSubExprs' sym (VarBindCache taggedCache resultCache) = rewriteSubExprs'' sym taggedCache resultCache

rewriteSubExprs'' ::
  forall sym t solver fs tp m.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (Tagged (VarBinds sym) (W4B.Expr t))  ->
  W4B.IdxCache t (W4B.Expr t) ->
  (forall tp'. W4B.Expr t tp' -> Maybe (W4B.Expr t tp')) ->
  W4B.Expr t tp ->
  m (W4B.Expr t tp)
rewriteSubExprs'' sym taggedCache resultCache f e_outer = W4B.idxCacheEval resultCache e_outer $ do
  -- During this recursive descent, we find any sub-expressions which need to be rewritten
  -- and perform an in-place replacement with a bound variable, and track that replacement
  -- in the 'VarBinds' environment.
  -- i.e. given a map which takes 'x -> a' and 'z -> b', we would replace 'x + z' with 'bv_0 + bv_1' and
  -- record that 'a -> bv_0' and 'b -> bv_1'.
  let
    go :: forall tp'. W4B.Expr t tp' -> CMW.WriterT (VarBinds sym) m (W4B.Expr t tp')
    go e = idxCacheEvalWriter taggedCache e $ case f e of
      Just e' -> do
        bv <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.exprType e')
        CMW.tell $ VarBinds $ MapF.singleton e' (SetF.singleton bv)
        return $ W4.varExpr sym bv
      Nothing -> case e of
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else IO.liftIO $ W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else IO.liftIO $ W4B.sbNonceExpr sym a0'
        _ -> return e
  (e', binds) <- CMW.runWriterT (go e_outer)
  -- Now we take our rewritten expression and use it to construct a function application.
  -- i.e. we define 'f(bv_0, bv_1) := bv_0 + bv_1', and then return 'f(a, b)', unfolding in-place.
  -- This ensures that the What4 expression builder correctly re-establishes any invariants it requires
  -- after rebinding.
  Pair vars vals <- return $ toBindings binds
  case Ctx.viewSize (Ctx.size vals) of
    -- no replacement
    Ctx.ZeroSize -> return e_outer
    _ -> IO.liftIO $ do
      fn <- W4.definedFn sym W4.emptySymbol vars e' W4.AlwaysUnfold
      W4.applySymFn sym fn vals >>= fixMux sym

-- | An expression binding environment. When applied to an expression 'e'
-- with 'applyExprBindings', each sub-expression of 'e' is recursively inspected
-- and rebound if it appears in the environment.
-- Note that this does not apply iteratively, once a sub-expression has been rebound the result
-- is not traversed further. This implicitly assumes that
-- the expressions used for the domain do not appear anywhere in the range.
type ExprBindings sym = MapF.MapF (W4.SymExpr sym) (W4.SymExpr sym)

-- | Merge two 'ExprBindings' together.
-- Throws a runtime exception if there are any clashes between the environments
-- (i.e. each environment binds an expression to different values)
mergeBindings ::
  OrdF (W4.SymExpr sym) =>
  sym ->
  ExprBindings sym ->
  ExprBindings sym ->
  IO (ExprBindings sym)
mergeBindings _sym binds1 binds2 =
  MapF.mergeWithKeyM (\_ e1 e2 -> case testEquality e1 e2 of
                         Just _ -> return $ Just e1
                         Nothing -> fail "mergeBindings: unexpected variable clash")
    return
    return
    binds1
    binds2


asConstantOffset ::
  forall sym t solver fs w.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym (W4.BaseBVType w) ->
  Maybe (W4.SymExpr sym (W4.BaseBVType w), W4C.ConcreteVal (W4.BaseBVType w))
asConstantOffset _sym e =
  case W4B.asApp e of
    (Just (W4B.SemiRingSum ws)) |
      SR.SemiRingBVRepr SR.BVArithRepr w <- WSum.sumRepr ws
      , Just (coef1, off1, coef2) <- WSum.asAffineVar ws
      , coef1 == BVS.one w -> Just (off1, W4C.ConcreteBV w coef2)
    _ -> Nothing

-- | Rewrite the sub-expressions of an expression according to the given binding environment.
applyExprBindings ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  ExprBindings sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
applyExprBindings sym binds = rewriteSubExprs sym (\e' -> MapF.lookup e' binds)

applyExprBindings' ::
  forall sym tp.
  OrdF (W4.SymExpr sym) =>
  sym ->
  VarBindCache sym ->
  ExprBindings sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
applyExprBindings' sym cache binds = rewriteSubExprs' sym cache (\e' -> MapF.lookup e' binds)

mapExprPtr ::
  forall sym m w.
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (forall tp. W4.SymExpr sym tp -> m (W4.SymExpr sym tp)) ->
  CLM.LLVMPtr sym w ->
  m (CLM.LLVMPtr sym w)
mapExprPtr sym f (CLM.LLVMPointer reg off) = do
  regInt <- f (W4.natToIntegerPure reg)
  reg' <- IO.liftIO $ integerToNat sym (assumePositiveInt sym regInt)
  off' <- f off
  return $ CLM.LLVMPointer reg' off'

class HasIntegerToNat sym where
  intToNat :: sym -> W4.SymExpr sym W4.BaseIntegerType -> IO (W4.SymNat sym)

instance W4.IsExprBuilder sym => HasIntegerToNat sym where
  intToNat sym e = integerToNat sym (assumePositiveInt sym e)

mapExprPtr2 ::
  forall sym sym' m w.
  W4.IsExprBuilder sym =>
  HasIntegerToNat sym' =>
  IO.MonadIO m =>
  sym ->
  sym' ->
  (forall tp. W4.SymExpr sym tp -> m (W4.SymExpr sym' tp)) ->
  CLM.LLVMPtr sym w ->
  m (CLM.LLVMPtr sym' w)
mapExprPtr2 _sym sym' f (CLM.LLVMPointer reg off) = do
  regInt <- f (W4.natToIntegerPure reg)
  reg' <- IO.liftIO $ intToNat sym' regInt
  off' <- f off
  return $ CLM.LLVMPointer reg' off'

freshPtrBytes ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  String ->
  W4.NatRepr w ->
  IO (CLM.LLVMPtr sym (8 W4.* w))
freshPtrBytes sym name w
  | bvwidth <- W4.natMultiply (W4.knownNat @8) w
  , W4.LeqProof <- mulMono (W4.knownNat @8) w
  = freshPtr sym name bvwidth

freshPtr ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  String ->
  W4.NatRepr w ->
  IO (CLM.LLVMPtr sym w)
freshPtr sym name w = do
  off <- W4.freshConstant sym (WS.safeSymbol (name ++ "_offset")) (W4.BaseBVRepr w)
  regI <- W4.freshBoundedInt sym (WS.safeSymbol (name ++ "_region")) (Just 0) Nothing
  reg <- integerToNat sym regI
  return $ (CLM.LLVMPointer reg off)

mulMono :: forall p q x w. (1 <= x, 1 <= w) => p x -> q w -> W4.LeqProof 1 (x W4.* w)
mulMono _x w = unsafeCoerce (W4.leqRefl w)


-- Clagged from What4.Builder
type BoundVarMap t = H.HashTable RealWorld Word64 (Set (Some (W4B.ExprBoundVar t)))

boundVarsMap :: W4B.Expr t tp -> IO (BoundVarMap t)
boundVarsMap e0 = do
  visited <- stToIO $ H.new
  _ <- boundVars' visited e0
  return visited

cacheExec :: (Eq k, CC.Hashable k) => H.HashTable RealWorld k r -> k -> IO r -> IO r
cacheExec h k m = do
  mr <- stToIO $ H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      stToIO $ H.insert h k r
      return r

boundVars' :: BoundVarMap t
           -> W4B.Expr t tp
           -> IO (Set (Some (W4B.ExprBoundVar t)))
boundVars' visited (W4B.AppExpr e) = do
  let idx = N.indexValue (W4B.appExprId e)
  cacheExec visited idx $ do
    sums <- sequence (TFC.toListFC (boundVars' visited) (W4B.appExprApp e))
    return $ foldl' S.union S.empty sums
boundVars' visited (W4B.NonceAppExpr e) = do
  let idx = N.indexValue (W4B.nonceExprId e)
  cacheExec visited idx $ do
    sums <- sequence (TFC.toListFC (boundVars' visited) (W4B.nonceExprApp e))
    return $ foldl' S.union S.empty sums
boundVars' visited (W4B.BoundVarExpr v) = do
      let idx = N.indexValue (W4B.bvarId v)
      cacheExec visited idx $
        return (S.singleton (Some v))
boundVars' _ (W4B.SemiRingLiteral{}) = return S.empty
boundVars' _ (W4B.BoolExpr{}) = return S.empty
boundVars' _ (W4B.StringExpr{}) = return S.empty
boundVars' _ (W4B.FloatExpr {}) = return S.empty
-- End Clag

boundVars :: W4B.Expr t tp -> IO (Set (Some (W4B.ExprBoundVar t)))
boundVars e0 = do
  visited <- stToIO $ H.new
  boundVars' visited e0

newtype ExprFilter sym = ExprFilter (forall tp'. W4.SymExpr sym tp' -> IO Bool)

data SymFnCollector sym =
  SymFnCollector
    { colSymFns :: Set (Some (W4.SymFnWrapper sym))
    , colVisited :: Set (Some (W4.SymExpr sym))
    }

instance (OrdF (W4.SymExpr sym), W4.IsSymFn (W4.SymFn sym)) => Semigroup (SymFnCollector sym) where
  (SymFnCollector a1 b1) <> (SymFnCollector a2 b2) = SymFnCollector (a1 <> a2) (b1 <> b2)

instance (OrdF (W4.SymExpr sym), W4.IsSymFn (W4.SymFn sym)) => Monoid (SymFnCollector sym) where
  mempty = SymFnCollector mempty mempty

-- | Collects all functions used anywhere in the given expression.
--   The 'SymFnCollector' caches visited expressions to avoid redundant
--   traversals.
collectSymFns ::
  forall sym t st fs tp.
  sym ~ W4B.ExprBuilder t st fs => W4B.Expr t tp -> SymFnCollector sym -> SymFnCollector sym
collectSymFns = go
  where
    goFn :: forall args tp'. W4.SymFn sym args tp' -> SymFnCollector sym -> SymFnCollector sym
    goFn fn coll_ = case W4B.symFnInfo fn of
      W4B.DefinedFnInfo _ fnBody _ -> go fnBody coll
      _ -> coll
      where
        coll = coll_ { colSymFns = S.insert (Some (W4.SymFnWrapper fn)) (colSymFns coll_) }

    go :: forall tp'. W4.SymExpr sym tp' -> SymFnCollector sym -> SymFnCollector sym
    go e coll_ = case e of
      W4B.SemiRingLiteral{} -> coll_
      W4B.BoolExpr{} -> coll_
      W4B.FloatExpr{} -> coll_
      W4B.StringExpr{} -> coll_
      W4B.BoundVarExpr{} -> coll_
      _ | S.member (Some e) (colVisited coll_) -> coll_
      W4B.AppExpr a0 -> TFC.foldrFC go coll (W4B.appExprApp a0)
      W4B.NonceAppExpr a0 -> case W4B.nonceExprApp a0 of
        W4B.FnApp fn args -> TFC.foldrFC go (goFn fn coll) args
        W4B.ArrayFromFn fn -> goFn fn coll
        napp -> TFC.foldrFC go coll napp
      where
        coll = coll_ { colVisited = S.insert (Some e) (colVisited coll_) }


data VarCollector sym =
  VarCollector
    { colVars :: Set (Some (W4.BoundVar sym))
    , colVarsVisited :: Set (Some (W4.SymExpr sym))
    }

instance (OrdF (W4.SymExpr sym), OrdF (W4.BoundVar sym)) => Semigroup (VarCollector sym) where
  (VarCollector a1 b1) <> (VarCollector a2 b2) = VarCollector (a1 <> a2) (b1 <> b2)

instance (OrdF (W4.SymExpr sym), OrdF (W4.BoundVar sym)) => Monoid (VarCollector sym) where
  mempty = VarCollector mempty mempty

-- | Collects all unbound vars used anywhere in the expression.
--   (similar to existing interface function but retains cache).
--   Descends into function definitions, but discards variables scoped to them.
collectVars ::
  forall sym t st fs tp.
  sym ~ W4B.ExprBuilder t st fs => W4B.Expr t tp -> VarCollector sym -> VarCollector sym
collectVars = go
  where
    goFn :: forall args tp'. W4.SymFn sym args tp' -> VarCollector sym -> VarCollector sym
    goFn fn coll = case W4B.symFnInfo fn of
      W4B.DefinedFnInfo args_vars body _ ->
        let
          coll_body = go body coll
          args_vars_set = TFC.foldrFC (\v s -> S.insert (Some v) s) S.empty args_vars
        in coll_body { colVars = S.difference (colVars coll_body) args_vars_set }
      _ -> coll

    go :: forall tp'. W4.SymExpr sym tp' -> VarCollector sym -> VarCollector sym
    go e coll_ = case e of
      W4B.SemiRingLiteral{} -> coll_
      W4B.BoolExpr{} -> coll_
      W4B.FloatExpr{} -> coll_
      W4B.StringExpr{} -> coll_
      W4B.BoundVarExpr bv -> coll { colVars = S.insert (Some bv) (colVars coll) }

      _ | S.member (Some e) (colVarsVisited coll_) -> coll_
      W4B.AppExpr a0 -> TFC.foldrFC go coll (W4B.appExprApp a0)
      W4B.NonceAppExpr a0 -> case W4B.nonceExprApp a0 of
        W4B.FnApp fn args -> TFC.foldrFC go (goFn fn coll) args
        W4B.ArrayFromFn fn -> goFn fn coll
        napp -> TFC.foldrFC go coll napp
      where
        coll = coll_ { colVarsVisited = S.insert (Some e) (colVarsVisited coll_) }



-- | Return an 'ExprFilter' that is filters expressions which are bound variables
-- that appear somewhere in the given expression.
getIsBoundFilter ::
  sym ~ (W4B.ExprBuilder t solver fs) =>
  -- | source expression potentially containing bound variables
  W4.SymExpr sym tp ->
  IO (ExprFilter sym)
getIsBoundFilter expr = do
  bvs <- liftIO $ boundVarsMap expr
  return $ ExprFilter $ \bv -> do
    case bv of
      W4B.BoundVarExpr bv' -> do
        let idx = N.indexValue (W4B.bvarId bv')
        stToIO $ H.lookup bvs idx >>= \case
          Just bvs' -> return $ S.member (Some bv') bvs'
          _ -> return False
      _ -> return False


newtype BoundVarBinding sym = BoundVarBinding (forall tp'. W4.BoundVar sym tp' -> IO (Maybe (W4.SymExpr sym tp')))

-- | Simplify 'ite (eq y x) y x' into 'x'
fixMux ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
fixMux sym e = do
  cache <- W4B.newIdxCache
  fixMux' sym cache e

fixMux' ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
fixMux' sym cache e_outer = do
  let
    go_eq :: forall tp'. W4B.Expr t tp' -> W4B.Expr t tp' -> Maybe (IO (W4B.Expr t W4.BaseBoolType))
     -- x = (ite cond x y) --> cond \/ x == y
    go_eq e1 e2 | 
        Just (W4B.BaseIte _ _ cond e2T e2F) <- W4B.asApp e2
      , Just Refl <- testEquality e1 e2T
      = Just $ do
        branches_eq <- W4.isEq sym e2T e2F
        go =<< W4.orPred sym cond branches_eq
    -- y = (ite cond x y) --> not cond \/ x == y
    go_eq e1 e2 | 
        Just (W4B.BaseIte _ _ cond e2T e2F) <- W4B.asApp e2
      , Just Refl <- testEquality e1 e2F
      = Just $ do
        branches_eq <- W4.isEq sym e2T e2F
        not_cond <- W4.notPred sym cond
        go =<< W4.orPred sym not_cond branches_eq
    go_eq _ _ = Nothing

    go :: forall tp'. W4B.Expr t tp' -> IO (W4B.Expr t tp')
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.AppExpr a0
        | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
        , Just (W4B.BaseEq _ eT' eF') <- W4B.asApp cond
        , Just W4.Refl <- W4.testEquality eT eT'
        , Just W4.Refl <- W4.testEquality eF eF'
        -> go eF
      W4B.AppExpr a0
         | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
         -> do
             eT' <- go eT
             eF' <- go eF
             if | Just (W4B.BaseIte _ _ cond2 eT2 _) <- W4B.asApp eT'
                , cond == cond2 -> W4.baseTypeIte sym cond eT2 eF'
                | Just (W4B.BaseIte _ _ cond2 _ eF2) <- W4B.asApp eF'
                , cond == cond2 ->  W4.baseTypeIte sym cond eT' eF2
                | eT' == eT, eF' == eF -> return e
                | otherwise -> W4.baseTypeIte sym cond eT' eF'
      W4B.AppExpr a0
         | W4B.BaseIte _ _ cond eT eF <- W4B.appExprApp a0
         , Just (W4B.BaseIte _ _ cond2 eT2 _) <- W4B.asApp eT
         , cond == cond2
         -> go =<< W4.baseTypeIte sym cond eT2 eF
      W4B.AppExpr a0
         | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
         , Just (W4B.BaseIte _ _ cond2 _ eF2) <- W4B.asApp eF
         , cond == cond2
         -> go =<< W4.baseTypeIte sym cond eT eF2
      W4B.AppExpr a0
         | (W4B.BaseEq _ e1 e2) <- W4B.appExprApp a0
         , Just f <- go_eq e1 e2
         -> f
      W4B.AppExpr a0
         | (W4B.BaseEq _ e1 e2) <- W4B.appExprApp a0
         , Just f <- go_eq e2 e1
         -> f
      W4B.AppExpr a0 -> do
        a0' <- W4B.traverseApp go (W4B.appExprApp a0)
        if (W4B.appExprApp a0) == a0' then return e
        else W4B.sbMakeExpr sym a0'
      W4B.NonceAppExpr a0 -> do
        a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
        if (W4B.nonceExprApp a0) == a0' then return e
        else W4B.sbNonceExpr sym a0'
      _ -> return e
  go e_outer


groundToConcrete ::
  W4.BaseTypeRepr tp ->
  W4G.GroundValue tp ->
  Maybe (W4C.ConcreteVal tp)
groundToConcrete repr gv = case repr of
  W4.BaseBoolRepr -> return $ W4C.ConcreteBool gv
  W4.BaseBVRepr w -> return $ W4C.ConcreteBV w gv
  W4.BaseIntegerRepr -> return $ W4C.ConcreteInteger gv
  W4.BaseStructRepr srepr -> do
    let
      go (W4G.GVW gv') repr' = groundToConcrete repr' gv'
    W4C.ConcreteStruct <$> Ctx.zipWithM go gv srepr
  _ -> fail "Unsupported ground value"

type ExprSet sym = SetF (W4.SymExpr sym)

type PredSet sym = ExprSet sym W4.BaseBoolType

ppExprSet ::
  W4.IsExpr (W4.SymExpr sym) =>
  Proxy sym ->
  ExprSet sym tp ->
  PP.Doc a
ppExprSet _ es = SetF.ppSetF W4.printSymExpr es

-- | Get the atomic predicates which appear anywhere in the given predicate.
-- TODO: does not consider all possible predicate constructors.
getPredAtoms ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.Pred sym ->
  IO (PredSet sym)
getPredAtoms sym e_outer = do
  cache <- W4B.newIdxCache
  let    
    muxes ::
      forall tp1.
      W4.SymExpr sym tp1 ->
      (W4.SymExpr sym tp1 -> IO (PredSet sym)) ->
      IO (PredSet sym)
    muxes e f = case W4B.asApp e of
      Just (W4B.BaseIte _ _ cond eT eF) -> do
        condAtoms <- go cond
        eTAtoms <- muxes eT f 
        eFAtoms <- muxes eF f
        return $ condAtoms <> eTAtoms <> eFAtoms
      _ -> f e

    muxes2 ::
      forall tp1 tp2.
      W4.SymExpr sym tp1 ->
      W4.SymExpr sym tp2 ->
      (W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO (PredSet sym)) ->
      IO (PredSet sym)
    muxes2 e1 e2 f = muxes e1 (\e1' -> muxes e2 (f e1'))

    liftPred ::
      forall tp1 tp2.
      (sym -> W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO (W4.Pred sym)) ->
      (W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO (PredSet sym))
    liftPred f e1 e2 = SetF.singleton <$> f sym e1 e2
      
    binOp ::
      forall tp1 tp2.
      (W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> IO (PredSet sym)) ->
      W4.SymExpr sym tp1 ->
      W4.SymExpr sym tp2 ->
      IO (PredSet sym)
    binOp f e1 e2 = muxes2 e1 e2 $ \e1' e2' -> do
      e1Atoms <- go e1'
      e2Atoms <- go e2'
      leafAtoms <- f e1' e2'
      return $ leafAtoms <> e1Atoms <> e2Atoms

    unOp ::
      forall tp1.
      (W4.SymExpr sym tp1 -> IO (PredSet sym)) ->
      W4.SymExpr sym tp1 ->
      IO (PredSet sym)
    unOp f e1 = muxes e1 $ \e1' -> do
      e1Atoms <- go e1'
      leafAtoms <- f e1'
      return $ e1Atoms <> leafAtoms
  
    go :: forall tp'. W4.SymExpr sym tp' -> IO (PredSet sym)
    go p_inner = muxes p_inner $ \p -> fmap getConst $ W4B.idxCacheEval cache p $ do
      setProgramLoc sym p
      case p of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
           W4B.BaseEq _ e1 e2 -> Const <$> binOp (liftPred W4.isEq) e1 e2 
           W4B.BVUlt e1 e2 -> Const <$> binOp (liftPred W4.bvUlt) e1 e2 
           W4B.BVSlt e1 e2 -> Const <$> binOp (liftPred W4.bvSlt) e1 e2
           W4B.SemiRingLe SR.OrderedSemiRingIntegerRepr e1 e2 -> Const <$> binOp (liftPred W4.intLe) e1 e2
           W4B.SemiRingLe SR.OrderedSemiRingRealRepr e1 e2 -> Const <$> binOp (liftPred W4.realLe) e1 e2
           W4B.BVTestBit n e -> Const <$> unOp (\e' -> SetF.singleton <$> W4.testBitBV sym n e') e
           _ -> TFC.foldrMFC acc mempty (W4B.appExprApp a0)
        W4B.NonceAppExpr a0 -> TFC.foldrMFC acc mempty (W4B.nonceExprApp a0)
        _ -> return $ mempty

    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Const (PredSet sym) tp2 -> IO (Const (PredSet sym) tp2)
    acc p (Const exprs) = do
      exprs' <- go p
      return $ Const $ exprs <> exprs'

  go e_outer


-- | Lambda abstraction: given a term @a@ and a term @e@ which contains @a@,
-- generate a function @f(x) = e[a/x]@.
abstractOver ::
  forall sym t solver fs tp1 tp2.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  -- | subterm
  W4.SymExpr sym tp1 ->
  -- | outer term
  W4.SymExpr sym tp2 ->
  IO (W4.SymFn sym (Ctx.EmptyCtx Ctx.::> tp1) tp2)
abstractOver sym sub outer = do
  sub_bv <- W4.freshBoundVar sym W4.emptySymbol (W4.exprType sub)
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e
      | Just Refl <- testEquality (W4.exprType e) (W4.exprType sub), e == sub
         = return $ W4.varExpr sym sub_bv
    go e = W4B.idxCacheEval cache e $ do
      setProgramLoc sym e
      case e of
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else W4B.sbNonceExpr sym a0'
        _ -> return e
  outer_abs <- go outer
  W4.definedFn sym W4.emptySymbol (Ctx.empty Ctx.:> sub_bv) outer_abs W4.AlwaysUnfold

stripAnnotations ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
stripAnnotations sym outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      setProgramLoc sym e
      case e of
        W4B.NonceAppExpr a0 | W4B.Annotation _ _ e' <- W4B.nonceExprApp a0 -> go e'
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else W4B.sbNonceExpr sym a0'
        _ -> return e
  go outer

simplifyIte ::
  forall m sym t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp {- ^ original expression (returned when recursive calls make no changes) -} ->
  (W4.Pred sym -> m (Maybe Bool)) {- ^ predicate decider -} ->
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) {- ^ recursive simplification -} ->
  W4.Pred sym {- ^ condition -} ->
  W4.SymExpr sym tp {- ^ true case -} ->
  W4.SymExpr sym tp {- ^ false case -} ->
  m (W4.SymExpr sym tp)
simplifyIte sym e_outer check go p e_true e_false =
  check p >>= \case
    Just True -> go e_true
    Just False -> go e_false
    Nothing -> do
      e_true' <- go e_true
      e_false' <- go e_false
      p' <- go p
      if e_true == e_true' && e_false == e_false' && p == p' then
        return e_outer
      else liftIO $ W4.baseTypeIte sym p' e_true' e_false'

-- | Resolve array lookups across array updates which are known to not alias.
-- i.e. @select (update arr A V) B --> select arr B@ given that @f(A, B) = Just False@ (i.e.
-- they are statically known to be inequivalent according to the given testing function)
resolveConcreteLookups ::
  forall m sym t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  (W4.Pred sym -> m (Maybe Bool)) ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
resolveConcreteLookups sym check e_outer = do
  cache <- W4B.newIdxCache
  let
    resolveArr ::
      forall idx idx1 idx2 tp'.
      idx ~ (idx1 Ctx.::> idx2) =>
      W4.SymExpr sym (W4.BaseArrayType idx tp') ->
      Ctx.Assignment (W4.SymExpr sym) idx ->
      m (Maybe (W4.SymExpr sym tp'))
    resolveArr arr idx = do
      case arr of
        W4B.BoundVarExpr{} -> do
          idx' <- TFC.traverseFC go idx
          case idx == idx' of
            True -> return Nothing
            False -> Just <$> (liftIO $ W4.arrayLookup sym arr idx')
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.UpdateArray _ _ arr' idx' upd_val -> do
            equalIndexes idx idx' >>= \case
              Just True -> Just <$> (go upd_val)
              Just False -> resolveArr arr' idx
              Nothing -> return Nothing
          W4B.SelectArray _ inner_arr inner_idx -> resolveArr inner_arr inner_idx >>= \case
            Just arr' -> resolveArr arr' idx
            Nothing -> do
              inner_arr' <- go inner_arr
              inner_idx' <- TFC.traverseFC go inner_idx
              case inner_arr == inner_arr' && inner_idx' == inner_idx of
                True -> return Nothing
                False -> do
                  arr' <- liftIO $ W4.arrayLookup sym inner_arr' inner_idx'
                  idx' <- TFC.traverseFC go idx
                  Just <$> (liftIO $ W4.arrayLookup sym arr' idx')
          W4B.ArrayMap _ _ aum arr' -> do
            case asConcreteIndices idx of
              Just cidx | Just e <- AUM.lookup cidx aum -> Just <$> (go e)
              Just{} -> resolveArr arr' idx
              _ -> (runMaybeT $ checkConcMap idx (AUM.toList aum)) >>= \case
                -- got an equal result
                Just (Just upd_val) -> Just <$> (go upd_val)
                -- proved that no entries equal this one
                Just Nothing -> resolveArr arr' idx
                -- inconclusive result, give up
                Nothing -> return Nothing
          W4B.BaseIte _ _ cond eT eF -> do
            check cond >>= \case
              Just True -> resolveArr eT idx
              Just False -> resolveArr eF idx
              Nothing -> do
                cond' <- go cond
                mvalT <- resolveArr eT idx >>= \case
                  Just valT -> Just <$> go valT
                  Nothing -> return Nothing
                mvalF <- resolveArr eF idx >>= \case
                  Just valF -> Just <$> go valF
                  Nothing -> return Nothing
                case (mvalT, mvalF) of
                  (Just valT, Just valF) -> do
                    Just <$> (liftIO $ W4.baseTypeIte sym cond' valT valF)
                  (Just valT, Nothing) -> do
                    eF' <- go eF
                    idx' <- TFC.traverseFC go idx
                    valF <- liftIO $ W4.arrayLookup sym eF' idx'
                    Just <$> (liftIO $ W4.baseTypeIte sym cond' valT valF)
                  (Nothing, Just valF) -> do
                    eT' <- go eT
                    idx' <- TFC.traverseFC go idx
                    valT <- liftIO $ W4.arrayLookup sym eT' idx'
                    Just <$> (liftIO $ W4.baseTypeIte sym cond' valT valF)
                  (Nothing, Nothing) -> do
                    eF' <- go eF
                    eT' <- go eT
                    case cond == cond' && eT == eT' && eF == eF' of
                      True -> return Nothing
                      False -> do
                        idx' <- TFC.traverseFC go idx
                        valT <- liftIO $ W4.arrayLookup sym eT' idx'
                        valF <- liftIO $ W4.arrayLookup sym eF' idx'
                        Just <$> (liftIO $ W4.baseTypeIte sym cond' valT valF)

          _ -> return Nothing
        _ -> return Nothing

    equalIndexes ::
      Ctx.Assignment (W4.SymExpr sym) ctx ->
      Ctx.Assignment (W4.SymExpr sym) ctx ->
      m (Maybe Bool)
    equalIndexes Ctx.Empty Ctx.Empty = return (Just True)
    equalIndexes (asn1 Ctx.:> e1) (asn2 Ctx.:> e2) = do
      p <- liftIO $ W4.isEq sym e1 e2
      check p >>= \case
        Just True -> equalIndexes asn1 asn2
        Just False -> return $ Just False
        Nothing -> return Nothing

    checkConcMap ::
      forall ctx tp'.
      Ctx.Assignment (W4.SymExpr sym) ctx ->
      [(Ctx.Assignment W4B.IndexLit ctx, W4.SymExpr sym tp')] ->
      MaybeT m (Maybe (W4.SymExpr sym tp'))
    checkConcMap _ [] = return Nothing
    checkConcMap symIdx ((concIdx, val) : xs) = do
      symIdx' <- liftIO $ asSymbolicIndex sym concIdx
      (lift $ equalIndexes symIdx symIdx') >>= \case
        Just True -> return $ Just val
        Just False -> checkConcMap symIdx xs
        Nothing -> fail ""
    
    go :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      setProgramLoc sym e
      case e of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.SelectArray _ arr idx -> do
            resolveArr arr idx >>= \case
              Just e' -> return e'
              Nothing -> do
                arr' <- go arr
                idx' <- TFC.traverseFC go idx
                case arr' == arr && idx == idx' of
                  True -> return e
                  False -> liftIO $ W4.arrayLookup sym arr' idx'
          W4B.BaseIte _ _ p e_true e_false ->
            simplifyIte sym e check go p e_true e_false
          app -> do
            a0' <- W4B.traverseApp go app
            if (W4B.appExprApp a0) == a0' then return e
            else liftIO $ W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else liftIO $ W4B.sbNonceExpr sym a0'
        _ -> return e
  go e_outer

-- Debugging
printAtoms ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
printAtoms sym e_outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      liftIO $ IO.putStrLn $ (show (W4.printSymExpr e))
      case e of
        W4B.BoundVarExpr{} -> liftIO $ IO.putStrLn "BoundVarExpr"
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.SelectArray{} -> liftIO $ IO.putStrLn "SelectArray"
          W4B.UpdateArray{} -> liftIO $ IO.putStrLn "UpdateArray"
          W4B.BaseIte{} -> liftIO $ IO.putStrLn "BaseIte"
          W4B.ArrayMap{} -> liftIO $ IO.putStrLn "BaseIte"
          _ -> return ()
        W4B.NonceAppExpr{} -> liftIO $ IO.putStrLn "NonceExpr"
        _ -> return ()
      case e of
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else W4B.sbNonceExpr sym a0'
        _ -> return e
  go e_outer

asSymbolicIndex ::
  W4.IsExprBuilder sym =>
  sym ->
  Ctx.Assignment W4B.IndexLit ctx ->
  IO (Ctx.Assignment (W4.SymExpr sym) ctx)
asSymbolicIndex _ Ctx.Empty = return Ctx.Empty
asSymbolicIndex sym (idx Ctx.:> W4B.IntIndexLit i) = do
  idx' <- asSymbolicIndex sym idx
  i' <- W4.intLit sym i
  return $ (idx' Ctx.:> i')
asSymbolicIndex sym (idx Ctx.:> W4B.BVIndexLit w bv) = do
  idx' <- asSymbolicIndex sym idx
  bv' <- W4.bvLit sym w bv
  return $ (idx' Ctx.:> bv')

-- FIXME: clagged from What4.Expr.Builder
asConcreteIndices :: W4.IsExpr e
                  => Ctx.Assignment e ctx
                  -> Maybe (Ctx.Assignment W4B.IndexLit ctx)
asConcreteIndices = TFC.traverseFC f
  where f :: W4.IsExpr e => e tp -> Maybe (W4B.IndexLit tp)
        f x =
          case W4.exprType x of
            W4.BaseIntegerRepr  -> W4B.IntIndexLit <$> W4.asInteger x
            W4.BaseBVRepr w -> W4B.BVIndexLit w <$> W4.asBV x
            _ -> Nothing

-- TODO: it's unclear if What4's existing abstract domains are
-- precise enough to capture what we need here
leadingZeros ::
  forall sym t solver fs w1.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  W4.SymBV sym w1 ->
  Integer
leadingZeros bv_outer = go bv_outer
  where
    go :: forall w. W4.SymBV sym w -> Integer
    go bv =
      let W4.BaseBVRepr w_large = W4.exprType bv
      in case W4B.asApp bv of
        Just (W4B.BVZext _ bv')
          | W4.BaseBVRepr w_small <- W4.exprType bv'
          , zlead <- go bv'
          , cexti <- (W4.intValue w_large) - (W4.intValue w_small)
          -> cexti + zlead
        Just (W4B.BVShl _ bv' shift)
          | Just cshift <- W4.asBV shift
          , zlead <- leadingZeros bv'
          -> max 0 (zlead - (BVS.asUnsigned cshift))
        Just (W4B.BVLshr _ bv' shift)
          | Just cshift <- W4.asBV shift
          , zlead <- leadingZeros bv'
          -> zlead + (BVS.asUnsigned cshift)
        Just (W4B.SemiRingSum s) | SR.SemiRingBVRepr SR.BVArithRepr _ <- WSum.sumRepr s ->
          let
            allzeros = W4.intValue w_large

            doAdd i1 i2 | i1 == allzeros = i2
            doAdd i1 i2 | i2 == allzeros = i1
            doAdd i1 i2 = max 0 ((min i1 i2) -1)

            doMul coef bv' = case BVS.asUnsigned coef of
              1 -> go bv'
              _ -> 0

            doConst c = BVS.asUnsigned (BVS.clz w_large c)
          in WSum.eval doAdd doMul doConst s
        Just (W4B.SemiRingSum s) | SR.SemiRingBVRepr SR.BVBitsRepr _ <- WSum.sumRepr s ->
          let
             doAdd i1 i2 = min i1 i2
             doMul coef bv' = max (doConst coef) (leadingZeros bv')
             doConst c = BVS.asUnsigned (BVS.clz w_large c)

           in WSum.eval doAdd doMul doConst s

        Just (W4B.BVSelect idx n bv')
          | 0 <- W4.intValue idx
          , zlead <- go bv'
          -> max 0 (zlead - (W4.intValue n))
        _ -> case W4.asBV bv of
          Just cbv -> BVS.asUnsigned (BVS.clz w_large cbv)
          Nothing -> 0

-- | (ite P A B) == (ite P' A' B') --> (P && P' && A == A') || (P && not(P') && A == B') ...
expandMuxEquality ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
expandMuxEquality sym outer = do
  cache <- W4B.newIdxCache
  let
    expandIte ::
      forall tp'.
      W4.Pred sym ->
      W4.SymExpr sym tp' ->
      W4.SymExpr sym tp' ->
      W4.SymExpr sym tp' ->
      IO (W4.Pred sym)
    expandIte cond eT eF that = do
      eT_eq <- W4.isEq sym that eT
      eF_eq <- W4.isEq sym that eF
      eT_case <- W4.andPred sym cond eT_eq
      notCond <- W4.notPred sym cond
      eF_case <- W4.andPred sym notCond eF_eq
      W4.orPred sym eT_case eF_case

    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      setProgramLoc sym e
      case e of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.BaseEq _ lhs rhs
            | Just (W4B.BaseIte _ _ cond eT eF) <- W4B.asApp rhs
            -> expandIte cond eT eF lhs >>= go
          W4B.BaseEq _ lhs rhs
            | Just (W4B.BaseIte _ _ cond eT eF) <- W4B.asApp lhs
            -> expandIte cond eT eF rhs >>= go
          app -> do
            a0' <- W4B.traverseApp go app
            if app == a0' then return e
            else W4B.sbMakeExpr sym a0' >>= go
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else W4B.sbNonceExpr sym a0' >>= go
        _ -> return e
  go outer

-- | Simplification cases for 'simplifyBVOps'
simplifyBVOpInner ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  SimpCheck sym IO {- ^ double-check simplification step (unused currently) -} ->
  -- | Recursive call to outer simplification function
  (forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')) ->
  W4B.App (W4B.Expr t) tp ->
  Maybe (IO (W4.SymExpr sym tp))
simplifyBVOpInner sym simp_check go app = case app of
  W4B.BVConcat w u v -> do
      W4B.BVSelect upper n bv <- W4B.asApp u
      W4B.BVSelect lower n' bv' <- W4B.asApp v
      Refl <- testEquality bv bv'
      W4.BaseBVRepr bv_w <- return $ W4.exprType bv
      Refl <- testEquality upper (W4.addNat lower n')
      total <- return $ W4.addNat n n'
      W4.LeqProof <- W4.testLeq (W4.addNat lower total) bv_w
      return $ W4.bvSelect sym lower total bv >>= go
    <|> do
      u' <- W4.asBV u
      0 <- return $ BVS.asUnsigned u'
      W4.BaseBVRepr v_w <- return $ W4.exprType v
      W4.LeqProof <- W4.testLeq (W4.incNat v_w) w
      return $ W4.bvZext sym w v >>= go
    <|> do
      v' <- W4.asBV v
      0 <- return $ BVS.asUnsigned v'
      W4.BaseBVRepr u_w <- return $ W4.exprType u
      W4.BaseBVRepr v_w <- return $ W4.exprType v
      W4.LeqProof <- W4.testLeq (W4.incNat u_w) w
      return $ do
        shift <- W4.bvLit sym w (BVS.mkBV w (W4.intValue v_w))
        bv <- W4.bvZext sym w u
        W4.bvShl sym bv shift >>= go

  --   ((Zext z a) << n) >> n) == a given n <= z
  W4B.BVLshr _ bv shift -> do
    W4B.BVShl _ bv' shift' <- W4B.asApp bv
    Refl <- testEquality shift shift'
    cshift <- W4.asBV shift
    zlead <- return $ leadingZeros bv'
    True <- return $ BVS.asUnsigned cshift <= zlead
    return $ go bv'
  -- simplify the operands of a shift if either can be simplified

  -- unclear if this is a good idea in general, but bubbling conditionals
  -- up tends to expose simplifications that are otherwise not possible
  W4B.BVShl _ bv shift -> do
    W4B.BaseIte _ _ cond t f <- W4B.asApp bv
    -- we restrict this to constant shifts to avoid duplicating
    -- complicated shift terms
    W4C.ConcreteBV{} <- W4.asConcrete shift
    return $ do
      t_shift <- W4.bvShl sym t shift >>= go
      f_shift <- W4.bvShl sym f shift >>= go
      W4.baseTypeIte sym cond t_shift f_shift >>= go


  W4B.BVZext w_outer bv -> do
    W4B.BVZext _ bv' <- W4B.asApp bv
    W4.BaseBVRepr bv_w <- return $ W4.exprType bv'
    W4.LeqProof <- W4.testLeq (W4.incNat bv_w) w_outer
    return $ W4.bvZext sym w_outer bv' >>= go

  W4B.BVSext w bv -> do
    True <- return $ 0 < leadingZeros bv
    return $ W4.bvZext sym w bv >>= go

  W4B.BVSelect idx n bv -> do
      W4B.BVShl _ bv' shift <- W4B.asApp bv
      cshift <- W4.asBV shift
      True <- return $ BVS.asUnsigned cshift <= BVS.asUnsigned (BVS.maxUnsigned n)
      return $ do
          shift' <- W4.bvLit sym n (BVS.mkBV n (BVS.asUnsigned cshift))
          bv'' <- W4.bvSelect sym idx n bv'
          W4.bvShl sym bv'' shift' >>= go
    <|> do
     -- select 0 16 (bvXor (bvAnd 0xffff var)) --> select 0 16 var
      Refl <- testEquality idx (W4.knownNat @0)
      W4B.SemiRingSum s <- W4B.asApp bv
      SR.SemiRingBVRepr SR.BVBitsRepr w_large <- return $ WSum.sumRepr s
      W4.LeqProof <- W4.testLeq (W4.incNat n) w_large
      one_small <- return $ BVS.zext w_large (SR.one (SR.SemiRingBVRepr SR.BVBitsRepr n))
      (coeff, var) <- WSum.asWeightedVar s
      True <- return $ one_small == coeff
      return $ W4.bvSelect sym idx n var >>= go
     -- push selection into bit operations
    <|> do
      W4B.SemiRingSum s <- W4B.asApp bv
      SR.SemiRingBVRepr SR.BVBitsRepr w <- return $ WSum.sumRepr s
      let
        doAdd bv1 bv2 = W4.bvXorBits sym bv1 bv2

        doMul coef bv' = do
          coef_bv <- W4.bvLit sym w coef
          coef_bv' <- W4.bvSelect sym idx n coef_bv
          bv'' <- W4.bvSelect sym idx n bv' >>= go
          W4.bvAndBits sym coef_bv' bv''

        doConst c = W4.bvLit sym w c >>= W4.bvSelect sym idx n

      return $ WSum.evalM doAdd doMul doConst s
    
    <|> do
      W4B.SemiRingSum s <- W4B.asApp bv
      SR.SemiRingBVRepr SR.BVArithRepr w <- return $ WSum.sumRepr s
      let zero = BVS.mkBV w 0
      Refl <- testEquality idx (W4.knownNat @0)
      (terms, offset) <- asSimpleSum sym w s
      (count :: Integer) <- case offset == zero of
        True -> return $ fromIntegral (length terms)
        False -> return $ fromIntegral (length terms) + 1
      -- do we have enough outer bits to contain all possible overflows
      -- from the inner sums without overflowing the outer bitvector?
      True <- return $ ((W4.intValue w - W4.intValue n) + 1) >= count
      -- if so, we can push the slice into the individual terms, since we
      -- are necessarily slicing off any overflow bits
      return $ do
        offsetLit <- W4.bvLit sym w offset >>= W4.bvSelect sym idx n
        result <- foldM (\r term -> W4.bvSelect sym idx n term >>= go >>= \term' -> W4.bvAdd sym term' r) offsetLit terms
        originalExpr <- W4B.sbMakeExpr sym app
        runSimpCheck simp_check originalExpr result
    <|> do
      W4B.BVOrBits _ s <- W4B.asApp bv
      (b:bs) <- return $ W4B.bvOrToList s
      return $ do
        let doOr bv1 bv2 = do
              bv2' <- W4.bvSelect sym idx n bv2 >>= go
              W4.bvOrBits sym bv1 bv2'
        b' <- W4.bvSelect sym idx n b >>= go
        foldM doOr b' bs
    <|> do
      W4B.BaseIte _ _ cond bv1 bv2 <- W4B.asApp bv
      return $ do
        bv1' <- W4.bvSelect sym idx n bv1 >>= go
        bv2' <- W4.bvSelect sym idx n bv2 >>= go
        cond' <- go cond
        W4.baseTypeIte sym cond' bv1' bv2'
  W4B.BaseEq _ lhs rhs -> do
      W4.BaseBVRepr lhs_w <- return $ W4.exprType lhs
      lhs_lz <- return $ leadingZeros lhs
      rhs_lz <- return $ leadingZeros rhs
      lz <- return $ min lhs_lz rhs_lz
      True <- return $ 0 < lz
      Some top <- W4.someNat ((W4.intValue lhs_w) - lz)
      W4.LeqProof <- W4.isPosNat top
      W4.LeqProof <- W4.testLeq top lhs_w
      return $ do
        lhs' <- W4.bvSelect sym (W4.knownNat @0) top lhs
        rhs' <- W4.bvSelect sym (W4.knownNat @0) top rhs
        W4.isEq sym lhs' rhs' >>= go
    <|> do
      W4.BaseBVRepr lhs_w <- return $ W4.exprType lhs
      lhs_lz <- return $ leadingZeros lhs
      True <- return $ 0 < lhs_lz
      W4B.BVSext _ rhs' <- W4B.asApp rhs
      W4.BaseBVRepr rhs_w <- return $ W4.exprType rhs'
      diff <- return $ (W4.intValue lhs_w - W4.intValue rhs_w)
      True <- return $ diff < lhs_lz
    -- TODO: provable
      W4.LeqProof <- W4.testLeq rhs_w lhs_w
      return $ do
        lhs' <- W4.bvSelect sym (W4.knownNat @0) rhs_w lhs
        W4.isEq sym lhs' rhs' >>= go
    <|> do
      W4B.BVConcat u_p_v inner_left inner_right <- W4B.asApp lhs
      W4.BaseBVRepr u <- return $ W4.exprType inner_left
      W4.BaseBVRepr v <- return $ W4.exprType inner_right
      W4.LeqProof <- W4.testLeq u u_p_v
      W4.LeqProof <- W4.testLeq v u_p_v
      v_p_u <- return $ W4.addNat v u
      Refl <- testEquality u_p_v v_p_u
      return $ do
        rhs1 <- W4.bvSelect sym (W4.knownNat @0) v rhs
        rhs2 <- W4.bvSelect sym v u rhs
        eq1 <- W4.isEq sym inner_left rhs2 >>= go 
        eq2 <- W4.isEq sym inner_right rhs1 >>= go 
        W4.andPred sym eq1 eq2
    <|> do
      W4B.BVConcat u_p_v inner_left inner_right <- W4B.asApp rhs
      W4.BaseBVRepr u <- return $ W4.exprType inner_left
      W4.BaseBVRepr v <- return $ W4.exprType inner_right
      W4.LeqProof <- W4.testLeq u u_p_v
      W4.LeqProof <- W4.testLeq v u_p_v
      v_p_u <- return $ W4.addNat v u
      Refl <- testEquality u_p_v v_p_u
      return $ do
        lhs1 <- W4.bvSelect sym (W4.knownNat @0) v lhs
        lhs2 <- W4.bvSelect sym v u lhs
        eq1 <- W4.isEq sym lhs2 inner_left >>= go 
        eq2 <- W4.isEq sym lhs1 inner_right >>= go 
        W4.andPred sym eq1 eq2
    <|> do
      -- t1 + (t2 xor 0xff..ff) + 1 --> t1 == t2
      W4C.ConcreteBV w lhs_c <- W4.asConcrete lhs
      True <- return $ lhs_c == BVS.zero w
      W4B.SemiRingSum s <- W4B.asApp rhs
      SR.SemiRingBVRepr SR.BVArithRepr _ <- return $ WSum.sumRepr s
      ([t2, t1],offset) <- asSimpleSum sym w s
      True <- return $ offset == BVS.one w
      W4B.SemiRingSum t2_s <- W4B.asApp t2
      SR.SemiRingBVRepr SR.BVBitsRepr _ <- return $ WSum.sumRepr t2_s
      ([t3],t2_s_offset) <- asSimpleSum sym w t2_s
      True <- return $ BVS.maxUnsigned w == t2_s_offset
      return $ W4.isEq sym t1 t3 >>= go
    <|> do
      W4C.ConcreteBV w lhs_c <- W4.asConcrete lhs
      True <- return $ lhs_c == BVS.zero w
      W4B.BVShl _ bv shift <- W4B.asApp rhs
      W4C.ConcreteBV _ shift_c <- W4.asConcrete shift
      -- as long as we are only shifting off leading zeros, the
      -- result is unchanged by the shift
      True <- return $ (BVS.asUnsigned shift_c) <= (leadingZeros bv)
      return $ do
        zero <- W4.bvLit sym w (BVS.zero w)
        W4.isEq sym zero bv >>= go


  _ -> Nothing

-- | Deep simplification of bitvector operations by removing redundant
-- shifts, pushing slices through arithmetic operations, and dropping
-- zero-extensions where possible.
simplifyBVOps ::
  forall sym m t solver fs tp.
  IO.MonadUnliftIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
simplifyBVOps sym outer = simplifyBVOps' sym noSimpCheck outer


simplifyBVOps' ::
  forall sym m t solver fs tp.
  IO.MonadUnliftIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  SimpCheck sym m {- ^ double-check simplification step -} ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
simplifyBVOps' sym simp_check outer = do
  simp_check' <- unliftSimpCheck simp_check
  IO.withRunInIO $ \inIO -> do
    cache1 <- W4B.newIdxCache
    cache2 <- W4B.newIdxCache
    let
      f :: forall tp'. W4B.App (W4B.Expr t) tp' -> m (Maybe (W4.SymExpr sym tp'))
      f app = case simplifyBVOpInner sym simp_check' (\e' -> inIO (go e')) app of
        Just g -> Just <$> liftIO g
        Nothing -> return Nothing

      go :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')
      go e = W4B.idxCacheEval cache1 e $ simplifyApp sym cache2 simp_check f e

    inIO (go outer)

unfoldDefinedFns ::
  forall sym m t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  IO.MonadIO m =>
  sym ->
  Maybe (W4B.IdxCache t (W4B.Expr t)) ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
unfoldDefinedFns sym mcache e_outer = do
  cache <- fromMaybe W4B.newIdxCache (fmap return mcache) 
  let
    go :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp') 
    go = simplifyGenApp sym cache noSimpCheck (\_ -> return Nothing) goNonceApp

    goNonceApp :: forall tp'. W4B.NonceApp t (W4B.Expr t) tp' -> m (Maybe (W4.SymExpr sym tp'))
    goNonceApp (W4B.FnApp fn args) | W4B.DefinedFnInfo vars body _ <- W4B.symFnInfo fn = do
      fn' <- IO.liftIO $ W4.definedFn sym W4.emptySymbol vars body W4.AlwaysUnfold
      e <- IO.liftIO $ W4.applySymFn sym fn' args
      Just <$> go e
    goNonceApp _ = return Nothing
  go e_outer

-- (if x then y else z) ==> (x -> y) AND (NOT(x) -> z)
--   Truth table:
---  x | y | z | expr | simp
---  T | T | T |   T  |  T
--   T | T | F |   T  |  T
--   T | F | T |   F  |  F
--   T | F | F |   F  |  F
--   F | T | T |   T  |  T
--   F | T | F |   F  |  F
--   F | F | T |   T  |  T
--   F | F | F |   F  |  F
iteToImp' ::
  forall sym.
  W4.IsExprBuilder sym =>
  sym ->
  W4.Pred sym {-^ if -} ->
  W4.Pred sym {-^ then -} ->
  W4.Pred sym {-^ else -} ->
  IO (W4.Pred sym)
iteToImp' sym i t e = do
  i_imp_t <- W4.impliesPred sym i t
  not_i <- W4.notPred sym i
  not_i_imp_e <- W4.impliesPred sym not_i e
  W4.andPred sym i_imp_t not_i_imp_e

-- | Rewrite subterms with: (if x then y else z) ==> (x -> y) AND (NOT(x) -> z)
iteToImp ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
iteToImp sym e_outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go = simplifyApp sym cache noSimpCheck goApp

    goApp :: forall tp'. W4B.App (W4B.Expr t) tp' -> IO (Maybe (W4.SymExpr sym tp'))
    goApp = \case
      W4B.BaseIte W4.BaseBoolRepr _ p t e -> do
        p' <- go p
        t' <- go t
        e' <- go e
        Just <$> iteToImp' sym p' t' e'
      _ -> return Nothing
  go e_outer

-- | Simplify the given predicate by deciding which atoms are logically necessary
-- according to the given provability function.
--
-- Starting with @p@, for each atom @a@ in @p@ and intermediate result @p'@, either:
--   * if @p'[a/true] == p'[a/false]: return @p'[a/true]@
--   * if @a@ is provable: return @p'[a/true]@
--   * if @a@ is disprovable: return @p'[a/false]@
--   * if @p' --> a@ is provable: return @a && p'[a/true]@
--   * if @p' --> not(a)@ is provable: return @not(a) && p'[a/false]@
--   * otherwise, return @p'@
minimalPredAtoms ::
  forall m sym t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  -- | decision for the provability of a predicate
  (W4.Pred sym -> m Bool) ->
  W4.Pred sym ->
  m (W4.Pred sym)
minimalPredAtoms sym provable p_outer = do
  let
    applyAtom :: W4.Pred sym -> W4.Pred sym -> m (W4.Pred sym)
    applyAtom p' atom = do
      notAtom <- liftIO $ W4.notPred sym atom
      p_fn <- liftIO $ abstractOver sym atom p'
      p_fn_true <- liftIO $ W4.applySymFn sym p_fn (Ctx.empty Ctx.:> W4.truePred sym)
      p_fn_false <- liftIO $ W4.applySymFn sym p_fn (Ctx.empty Ctx.:> W4.falsePred sym)
      indep <- liftIO $ W4.isEq sym p_fn_true p_fn_false

      trueCase <- liftIO $ W4.orPred sym atom indep
      implies_atom <- liftIO $ W4.impliesPred sym p' atom
      implies_notAtom <- liftIO $ W4.impliesPred sym p' notAtom
      
      provable trueCase >>= \case
        True -> return p_fn_true
        False -> provable notAtom >>= \case
          True -> return p_fn_false
          False -> provable implies_atom >>= \case
            True -> liftIO $ W4.andPred sym atom p_fn_true
            False -> provable implies_notAtom >>= \case
              True -> liftIO $ W4.andPred sym notAtom p_fn_false
              False -> return p'

  atoms <- liftIO $ getPredAtoms sym p_outer
  foldM applyAtom p_outer (SetF.toList atoms)

data ConjunctFoldDir = ConjunctFoldRight | ConjunctFoldLeft

simplifyConjuncts ::
  forall m sym t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  -- | decision for the provability of a predicate
  (W4.Pred sym -> m Bool) ->
  W4.Pred sym ->
  m (W4.Pred sym)
simplifyConjuncts sym provable p_outer = do
  cache <- W4B.newIdxCache
  let
    go :: ConjunctFoldDir -> W4.Pred sym -> W4.Pred sym -> m (W4.Pred sym)
    go foldDir asms p = W4B.idxCacheEval cache p $ do
      setProgramLoc sym p
      case W4B.asApp p of
        Just (W4B.ConjPred bm) -> do
          let
            eval' :: (W4.Pred sym, BM.Polarity) -> m (W4.Pred sym)
            eval' (x, BM.Positive) = return x
            eval' (x, BM.Negative) = liftIO $ W4.notPred sym x

            eval :: (W4.Pred sym, W4.Pred sym) -> (W4.Pred sym, BM.Polarity) -> m (W4.Pred sym, W4.Pred sym)
            eval (asms', p') atom = do
              atom' <- eval' atom
              test <- liftIO $ W4.impliesPred sym asms' atom'
              provable test >>= \case
                True -> return $ (asms', p')
                False -> do
                  atom'' <- go foldDir asms' atom'
                  p'' <- liftIO $ W4.andPred sym p' atom''
                  asms'' <- liftIO $ W4.andPred sym asms' p''
                  return (asms'', p'')
          case BM.viewBoolMap bm of
            BM.BoolMapUnit -> return $ W4.truePred sym
            BM.BoolMapDualUnit -> return $ W4.falsePred sym
            BM.BoolMapTerms (t:|ts) -> case foldDir of
              ConjunctFoldRight -> snd <$> foldrM (\a b -> eval b a) (asms, W4.truePred sym) (t:ts)
              ConjunctFoldLeft ->  snd <$> foldlM eval (asms, W4.truePred sym) (t:ts)

        Just (W4B.NotPred p') -> do
          p'' <- go foldDir asms p'
          if p' == p'' then return p
            else liftIO $ W4.notPred sym p''
        _ -> return p
  p <- go ConjunctFoldRight (W4.truePred sym) p_outer
  go ConjunctFoldLeft (W4.truePred sym) p




data Tagged w f tp where
  Tagged :: w -> f tp -> Tagged w f tp

-- | Cached evaluation that retains auxiliary results
idxCacheEvalWriter ::
  MonadIO m =>
  CMW.MonadWriter w m =>
  W4B.IdxCache t (Tagged w f) ->
  W4B.Expr t tp ->
  m (f tp) ->
  m (f tp)
idxCacheEvalWriter cache e f = do
  Tagged w result <- W4B.idxCacheEval cache e $ do
    (result, w) <- CMW.listen $ f
    return $ Tagged w result
  CMW.tell w
  return result