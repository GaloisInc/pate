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

module What4.ExprHelpers (
    iteM
  , impM
  , andM
  , orM
  , allPreds
  , anyPred
  , VarBinding(..)
  , mapExprPtr
  , freshPtr
  , freshPtrBytes
  , stripAsserts
  , mkSafeAsserts
  , ExprFilter(..)
  , getIsBoundFilter
  , assertPrefix
  , BoundVarBinding(..)
  , groundToConcrete
  , fixMux
  , getPathCondition
  , ExprSet
  , singletonExpr
  , listToExprSet
  , exprSetToList
  , exprSetSize
  , inExprSet
  , getPredAtoms
  , independentOf
  ) where

import           GHC.TypeNats
import           Unsafe.Coerce -- for mulMono axiom

import           Control.Applicative
import           Control.Monad.Except
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.ST ( RealWorld, stToIO )
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans.Maybe as MaybeT

import qualified Data.HashTable.ST.Basic as H
import qualified Data.Text as T
import           Data.Word (Word64)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List ( foldl' )
import           Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Concrete as W4C
import qualified What4.Symbol as W4
import qualified What4.Expr.BoolMap as BM

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


data VarBinding sym tp =
  VarBinding
   {
     bindVar :: W4.SymExpr sym tp
   , bindVal :: W4.SymExpr sym tp
   }

mapExprPtr ::
  forall sym w.
  (W4.IsExprBuilder sym) =>
  sym ->
  (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
  CLM.LLVMPtr sym w ->
  IO (CLM.LLVMPtr sym w)  
mapExprPtr sym f (CLM.LLVMPointer reg off) = do
  regInt <- W4.natToInteger sym reg
  reg' <- W4.integerToNat sym =<< f regInt
  off' <- f off
  return $ CLM.LLVMPointer reg' off'  

freshPtrBytes ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  W4.NatRepr w ->
  IO (CLM.LLVMPtr sym (8 W4.* w))
freshPtrBytes sym w
  | bvwidth <- W4.natMultiply (W4.knownNat @8) w
  , W4.LeqProof <- mulMono (W4.knownNat @8) w
  = freshPtr sym bvwidth

freshPtr ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  W4.NatRepr w ->
  IO (CLM.LLVMPtr sym w)
freshPtr sym w = do
  off <- W4.freshConstant sym W4.emptySymbol (W4.BaseBVRepr w)
  reg <- W4.freshNat sym W4.emptySymbol
  return $ CLM.LLVMPointer reg off


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

newtype ExprFilter sym = ExprFilter (forall tp'. W4.SymExpr sym tp' -> IO Bool)

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
    go :: forall tp'. W4B.Expr t tp' -> IO (W4B.Expr t tp')
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.AppExpr a0
        | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
        , Just (W4B.BaseEq _ eT' eF') <- W4B.asApp cond
        , Just W4.Refl <- W4.testEquality eT eT'
        , Just W4.Refl <- W4.testEquality eF eF'
        -> return eF
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

assertPrefix :: String
assertPrefix = "assert"

-- | Handles all polymorphic assertion functions generated by
-- 'Pate.Memory.MemTrace.mkUndefinedPtrOps'
isAssert :: W4.SolverSymbol -> Bool
isAssert symbol = T.isPrefixOf (T.pack assertPrefix) $ W4.solverSymbolAsText symbol


type GroundM t a = ExceptT (W4B.Expr t W4.BaseBoolType) IO a

-- | Pop any asserts up to the nearest mux that cases on it, and erase
-- the assertion by taking the other case.
-- This is meant to remove assertions introduced by Pate.Memory.MemTrace
-- prior to printing counterexamples, to ensure that the ground term evaluator
-- doesn't encounter uninterpreted functions.
stripAsserts ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
stripAsserts sym cache e_outer = do
  let
    go :: forall tp'. W4B.Expr t tp' -> GroundM t (W4B.Expr t tp')
    go e = W4B.idxCacheEval cache e $ do
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e)
      case e of
        _
          | Just (W4B.FnApp efn args) <- W4B.asNonceApp e
          , isAssert (W4B.symFnName efn)
          , W4B.UninterpFnInfo argtps _ <- W4B.symFnInfo efn
          , Ctx.Empty Ctx.:> _ Ctx.:> cond <- args
          , Ctx.Empty Ctx.:> _ Ctx.:> W4.BaseBoolRepr <- argtps
          -> throwError cond
        W4B.AppExpr a0
          | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
          -> do
              cond' <- go cond
              notcond <- lift $ W4.notPred sym cond
              eT' <- lift $ runExceptT $ go eT
              eF' <- lift $ runExceptT $ go eF
              case (eT', eF') of
                -- FIXME: It'd be better to key this more precisely
                (Left condT, Right eF'') ->
                  (W4.asConstantPred <$> (lift $ W4.isEq sym condT notcond)) >>= \case
                    Just True -> return eF''
                    _ -> throwError condT
                (Right eT'', Left condF) -> do          
                  (W4.asConstantPred <$> (lift $ W4.isEq sym condF cond)) >>= \case
                    Just True -> return eT''
                    _ -> throwError condF
                (Right eT'', Right eF'') ->
                  if cond' == cond && eT'' == eT && eF'' == eF then return e
                  else lift $ W4.baseTypeIte sym cond' eT'' eF''
                (Left condT, Left _) -> throwError condT
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else lift $ W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else lift $ W4B.sbNonceExpr sym a0'
        _ -> return e
  (runExceptT $ go e_outer) >>= \case
    Left _ -> fail "stripAsserts: assertion not guarded by a corresponding mux"
    Right x -> return x

  

-- | Peel off any "assert" uninterpreted functions while evaluating to a ground
-- value
mkSafeAsserts ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4G.GroundEvalFn t ->
  IO (W4G.GroundEvalFn t)
mkSafeAsserts sym (W4G.GroundEvalFn fn) = do
  cache <- W4B.newIdxCache
  return $ W4G.GroundEvalFn (\e -> stripAsserts sym cache e >>= fn)

newtype SetF f tp = SetF (Set (AsOrd f tp))

type ExprSet sym = SetF (W4.SymExpr sym)

data AsOrd f tp where
  AsOrd :: OrdF f => { unAsOrd :: f tp } -> AsOrd f tp

instance Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) = case compareF a b of
    EQF -> True
    _ -> False

instance Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

deriving instance Semigroup (SetF sym tp)
deriving instance Monoid (SetF sym tp)


singletonExpr :: OrdF (W4.SymExpr sym) => W4.SymExpr sym tp -> ExprSet sym tp
singletonExpr e = SetF (S.singleton (AsOrd e))

listToExprSet :: W4.IsSymExprBuilder sym => [W4.SymExpr sym tp] -> ExprSet sym tp
listToExprSet l = SetF $ S.fromList $ map AsOrd l

exprSetToList :: ExprSet sym tp -> [W4.SymExpr sym tp]
exprSetToList (SetF es) = map unAsOrd $ S.toList es

exprSetSize :: ExprSet sym tp -> Int
exprSetSize (SetF es) = S.size es

inExprSet :: OrdF (W4.SymExpr sym) => W4.SymExpr sym tp -> ExprSet sym tp -> Bool
inExprSet e (SetF es) = S.member (AsOrd e) es

setFUnion :: OrdF f => SetF f tp -> SetF f tp -> SetF f tp
setFUnion (SetF s1) (SetF s2) = SetF (S.union s1 s2)

setFEmpty :: SetF f tp
setFEmpty = SetF S.empty

-- -- | Compute a list of predicates that, if any one is true,
-- -- under the given assumptions, the predicate is equal to the given polarity.
-- toDisjunction ::
--   forall sym t solver fs tp.
--   sym ~ (W4B.ExprBuilder t solver fs) =>
--   sym ->
--   Bool ->
--   [W4.Pred sym] ->
--   W4.Pred sym ->
--   IO [W4.Pred sym]
-- toDisjunction sym = go
--   where
--     go :: Bool -> [W4.Pred sym] -> W4.Pred sym -> IO [W4.Pred sym]
--     go pol asms (W4B.BaseIte _ _ cond pT pF) = do
--       cond_neg <- go False asms cond
--       cond_pos <- go True asms cond
--       pT_disj <- concat <$> mapM (\cond_pos' -> go pol (cond_pos' : asms) pT) cond_pos
--       pT_disj <- concat <$> mapM (\cond_neg' -> go pol (cond_neg' : asms) pF) cond_neg
--       return $ pT_disj ++ pT_disj
--     go asms (W4B.NotPred p) = go (not pol) asms p
--     go asms (W4B.ConjPred bm) =
--       let pol (x,BM.Positive) = go pol [] x
--           pol (x,BM.Negative) = go (not pol) [] x
--       in
--       case BM.viewBoolMap bm of
--         BM.BoolMapUnit -> go pol (W4.truePred sym)
--         BM.BoolMapDualUnit -> go pol (W4.falsePred sym)
--         BM.BoolMapTerms (t:|ts),-> mulLists (t:ts)
--           foldl' (&&) <$> pol t <*> mapM pol ts

-- mulLists :: [[a]] -> [[a]]
-- mulLists [] = [[]]
-- mulLists (xs:xss) = [ x:xs_ | x <- xs, xs_ <- mulLists xss ]

-- -- | A list of predicates where, if any one is true, the predicate is true.
-- toDisjunction ::
--   forall sym t solver fs tp.
--   sym ~ (W4B.ExprBuilder t solver fs) =>
--   sym ->
--   [W4.Pred sym] ->
--   W4.Pred sym ->
--   IO [W4.Pred sym]
-- toDisjunction sym asms_outer p_outer = go p_outer
--   where
--     go :: [W4.Pred sym] -> W4.Pred sym -> IO [W4.Pred sym]
--     go assuming (W4B.BaseIte _ _ cond pT pF) = do
--       cond_neg <- go assuming cond
--       pT_neg <- go (cond : assuming) pT
--       pF_neg <- concat <$> mapM (\cond_neg' -> go (cond_neg' : assuming) pF) cond_neg
--       return $ pT_neg ++ pF_neg
--     go assuming (W4B.NotPred p) = do
--       p_neg <- go assuming p    

-- data GroundValue' tp where
--   GroundValue' tp :: W4.BaseTypeRepr tp -> W4G.GroundValue tp -> GroundValue' tp

-- fromWrapped ::
--   W4.BaseTypeRepr tp ->
--   W4G.GroundValueWrapper tp ->
--   GroundValue' tp
-- fromWrapped repr (W4G.GroundValueWrapper v) = GroundValue' repr v

-- instance Eq (GroundValue' tp) where
--   (GroundValue' repr1 v1) == (GroundValue' repr2 v2) = case repr of
--     W4.BaseBoolType -> v1 == v2
--     W4.BaseNatType -> v1 == v2
--     W4.BaseIntegerType -> v1 == v2
--     W4.BaseRealType -> v1 == v2
--     W4.BaseBVType _ -> v1 == v2
--     W4.BaseFloatType _ -> v1 == v2
--     W4.BaseComplexType -> v1 == v2
--     W4.BaseStringType -> v1 == v2
--     W4.BaseArrayType _ -> case (v1, v2) of
--       (W4G.ArrayConcrete default1 map1, W4G.ArrayConcrete default2 map2)
--         -> default1 == default2 &&  map1 == map2
--       (W4G.ArrayMapping _, W4G.ArrayMapping _) -> error "GroundValue': cannot compare non-concrete arrays"
--     W4.BaseStructType repr' -> (Ctx.zipWith fromWrapped repr' v1) == (Ctx.zipWith fromWrapped repr' v2)
    
-- instance TestEquality GroundValue'where
--   testEquality (GroundValue' repr1 v1) (GroundValue' repr2 v2)
--     | Just Refl <- testEquality repr1 repr2, v1 == v2 = Just Refl
--   testEquality _ _ = Nothing

-- evalGround ::
--   forall sym t solver fs tp.
--   sym ~ (W4B.ExprBuilder t solver fs) =>
--   sym ->
--   W4G.GroundEvalFn t ->
--   W4B.Expr t tp ->
--   IO (GroundValue' tp)
-- evalGround _sym fn e = GroundValue' (W4.exprType e) <$> W4G.groundEval fn e

-- maybeTDefault ::
--   -- | computation to run
--   MaybeT m a ->
--   -- | default value if it fails
--   MaybeT m a ->
--   MaybeT m a ->
-- maybeTDefault f default_ = lift (runMaybeT f) >>= \case
--   Just a -> return a
--   Nothing -> default_



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
getPathCondition sym fn expr = do
  cache <- W4B.newIdxCache
  let
    env = PathMEnv sym fn (W4.truePred sym) cache
    PathM f = withPathCond expr >> getFullPath
  mpred <- liftIO $ MaybeT.runMaybeT $ CMS.evalStateT (CMR.runReaderT f env) (PathCondition (W4.truePred sym))
  case mpred of
    Just p -> return p
    Nothing -> fail "getPathCondition: Unexpected inconsistent path condition"


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

-- Monad for computing a path condition
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

toPolarity ::
  Bool -> BM.Polarity
toPolarity True = BM.Positive
toPolarity False = BM.Negative


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

  -- | unsigned case
  (W4.SymBV sym w1  -> W4.SymBV sym w2  -> PathM sym a) ->
  -- | signed case
  (W4.SymBV sym w1  -> W4.SymBV sym w2  -> PathM sym a) ->
  W4.SymBV sym w1 ->
  W4.SymBV sym w2 ->
  PathM sym a
altBVOp f_unsigned f_signed e1 e2 = withSym $ \sym -> forMuxes2 e1 e2 $ \e1' e2' -> do
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
  W4.BaseBVRepr w <- return $ W4.exprType bv
  clz <- W4.bvCountLeadingZeros sym bv
  -- must have at least one leading zero
  W4.bvIsNonzero sym clz  

  
-- | compute a set of assumptions that will cause the given predicate to
-- have the given polarity in the given model.
-- If the predicate disagrees with the given polarity, then no results
-- are produced (i.e. this branch was not taken in the model)
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
      (sym -> W4.SymBV sym w1  -> W4.SymBV sym w2  -> IO (W4.Pred sym)) ->
      W4.SymBV sym w1 ->
      W4.SymBV sym w2 ->
      PathM sym (W4.Pred sym)      
    bvOp pol f_unsigned f_signed e1 e2 =
      altBVOp
        (\e1' e2' -> liftBinOp f_unsigned e1' e2' >>= applyPolarity pol)
        (\e1' e2' -> liftBinOp f_signed e1' e2' >>= applyPolarity pol)
        e1 e2 
    
    go :: BM.Polarity -> W4.Pred sym -> PathM sym (W4.Pred sym)
    go pol e_inner = withValid $ withSym $ \sym -> forMuxes e_inner $ \e -> do
      -- only consider cases where the polarity agrees with the model
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
                  let eval p (x, pol') = do
                        p' <- go (BM.negatePolarity pol') x
                        liftIO $ W4.orPred sym p p'
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
            W4B.BVSlt e1 e2 -> bvOp pol W4.bvUlt W4.bvSlt e1 e2

            -- catch-all: assume the entire predicate
            _ -> applyPolarity pol e
          _ -> applyPolarity pol e

-- | No-op if the predicate agrees with the given polarity in the model.
-- Otherwise, yields no results.
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
-- Resolve to the resulting expression with the given mux structure.
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
      (sym -> W4.SymBV sym w1  -> W4.SymBV sym w2  -> IO (W4.SymExpr sym tp3)) ->
      W4.SymBV sym w1 ->
      W4.SymBV sym w2 ->
      PathM sym (ExprAsms sym tp3)      
    bvOp f_unsigned f_signed e1 e2 =
      altBVOp
        (\e1' e2' -> watch $ liftBinOp f_unsigned e1' e2')
        (\e1' e2' -> watch $ liftBinOp f_signed e1' e2')
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
            W4B.BVAshr _ e1 e2 -> bvOp W4.bvLshr W4.bvAshr e1 e2
            W4B.BVSdiv _ e1 e2 -> bvOp W4.bvUdiv W4.bvSdiv e1 e2
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


-- | Get the atoms of a composite predicate.
getPredAtoms ::
  forall sym t solver fs.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.Pred sym ->
  IO (ExprSet sym W4.BaseBoolType)
getPredAtoms _sym e_outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (Const (ExprSet sym W4.BaseBoolType) tp')
    go p =  W4B.idxCacheEval cache p $ case p of
      W4B.AppExpr a0 -> case W4B.appExprApp a0 of
         W4B.BaseEq{} -> return $ Const $ singletonExpr @sym p
         W4B.BVUlt{} -> return $ Const $ singletonExpr @sym p
         W4B.BVSlt{} -> return $ Const $ singletonExpr @sym p
         _ -> TFC.foldrMFC acc (Const setFEmpty) (W4B.appExprApp a0)
      W4B.NonceAppExpr a0 -> TFC.foldrMFC acc (Const setFEmpty) (W4B.nonceExprApp a0)
      _ -> return $ Const setFEmpty

    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Const (ExprSet sym W4.BaseBoolType) tp2 -> IO (Const (ExprSet sym W4.BaseBoolType) tp2)
    acc p (Const exprs) = do
      Const exprs' <- go p
      return $ Const $ setFUnion exprs exprs'

  getConst <$> go e_outer


-- | Freshen the bound variables in the given term
freshBVs ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
freshBVs sym e_outer = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> W4.freshConstant sym W4.emptySymbol (W4.exprType e)
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



-- | Predicate stating that the value of the outer term is independent of the value
-- of the inner term.
independentOf ::
  forall sym t solver fs tp1 tp2.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  -- | subterm
  W4.SymExpr sym tp1 ->
  -- | outer term
  W4.SymExpr sym tp2 ->
  IO (W4.Pred sym)
independentOf sym sub outer = do
  sub_fresh <- freshBVs sym sub
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
    go e | Just Refl <- testEquality (W4.exprType e) (W4.exprType sub), e == sub = return $ sub_fresh
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.AppExpr a0 -> do
        a0' <- W4B.traverseApp go (W4B.appExprApp a0)
        if (W4B.appExprApp a0) == a0' then return e
        else W4B.sbMakeExpr sym a0'
      W4B.NonceAppExpr a0 -> do
        a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
        if (W4B.nonceExprApp a0) == a0' then return e
        else W4B.sbNonceExpr sym a0'
      _ -> return e
  outer_fresh <- go outer
  W4.isEq sym outer outer_fresh

-- getPathCondition ::
--   forall sym t solver fs.
--   sym ~ (W4B.ExprBuilder t solver fs) =>
--   sym ->
--   W4B.Expr t tp ->
--   [W4.Pred sym]
-- getPathCondition sym e = go e
--   let
--     go :: forall tp'. W4B.Expr t tp' -> [W4.Pred sym]
--     go e = case e of
--       W4B.AppExpr a0
--         | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
--         -> let
--             cond_conds = go cond
--             eT_conds = go eT
--             eF_conds = go eF
--            in cond_conds ++ eT_conds ++ eF_conds
            
--             notcond <- lift $ W4.notPred sym cond
--             eT' <- lift $ runExceptT $ go eT
--             eF' <- lift $ runExceptT $ go eF
--             case (eT', eF') of
--               -- FIXME: It'd be better to key this more precisely
--               (Left condT, Right eF'') ->
--                 (W4.asConstantPred <$> (lift $ W4.isEq sym condT notcond)) >>= \case
--                   Just True -> return eF''
--                   _ -> throwError condT
--               (Right eT'', Left condF) -> do          
--                 (W4.asConstantPred <$> (lift $ W4.isEq sym condF cond)) >>= \case
--                   Just True -> return eT''
--                   _ -> throwError condF
--               (Right eT'', Right eF'') ->
--                 if cond' == cond && eT'' == eT && eF'' == eF then return e
--                 else lift $ W4.baseTypeIte sym cond' eT'' eF''
--               (Left condT, Left _) -> throwError condT
--       W4B.AppExpr a0 -> do
--         a0' <- W4B.traverseApp go (W4B.appExprApp a0)
--         if (W4B.appExprApp a0) == a0' then return e
--         else lift $ W4B.sbMakeExpr sym a0'
--       W4B.NonceAppExpr a0 -> do
--         a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
--         if (W4B.nonceExprApp a0) == a0' then return e
--         else lift $ W4B.sbNonceExpr sym a0'
--       _ -> return e
--   (runExceptT $ go e_outer) >>= \case
--     Left _ -> fail "stripAsserts: assertion not guarded by a corresponding mux"
--     Right x -> return x  
