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
  , abstractOver
  , resolveConcreteLookups
  , minimalPredAtoms
  ) where

import           GHC.TypeNats
import           Unsafe.Coerce -- for mulMono axiom
import           GHC.Stack ( HasCallStack )

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

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Concrete as W4C
import qualified What4.Symbol as W4
import qualified What4.Expr.BoolMap as BM
import qualified What4.SemiRing as SR

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
  HasCallStack =>
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

type PredSet sym = ExprSet sym W4.BaseBoolType

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
    liftPred f e1 e2 = singletonExpr @sym <$> f sym e1 e2
      
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
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc p)
      case p of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
           W4B.BaseEq _ e1 e2 -> Const <$> binOp (liftPred W4.isEq) e1 e2 
           W4B.BVUlt e1 e2 -> Const <$> binOp (liftPred W4.bvUlt) e1 e2 
           W4B.BVSlt e1 e2 -> Const <$> binOp (liftPred W4.bvSlt) e1 e2
           W4B.SemiRingLe SR.OrderedSemiRingIntegerRepr e1 e2 -> Const <$> binOp (liftPred W4.intLe) e1 e2
           W4B.SemiRingLe SR.OrderedSemiRingRealRepr e1 e2 -> Const <$> binOp (liftPred W4.realLe) e1 e2
           W4B.BVTestBit n e -> Const <$> unOp (\e' -> singletonExpr @sym <$> W4.testBitBV sym n e') e
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
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e)
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

-- | Resolve array lookups across array updates which are known to not alias.
-- i.e. @select (update arr A V) B --> select arr B@ given that @f(A, B) = Just False@ (i.e.
-- they are statically known to be inequivalent according to the given testing function)
resolveConcreteLookups ::
  forall m sym t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  (forall tp'. W4.SymExpr sym tp' -> W4.SymExpr sym tp' -> m (Maybe Bool)) ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
resolveConcreteLookups sym f e_outer = do
  cache <- W4B.newIdxCache
  let
    andPred ::
      forall (tp' :: W4.BaseType).
      Const (Maybe Bool) tp' ->
      Maybe Bool ->
      Maybe Bool
    andPred (Const p) (Just b) = case p of
      Just b' -> Just (b && b')
      Nothing -> Nothing
    andPred _ Nothing = Nothing
    
    resolveArr ::
      forall idx idx1 idx2 tp'.
      idx ~ (idx1 Ctx.::> idx2) =>
      W4.SymExpr sym (W4.BaseArrayType idx tp') ->
      Ctx.Assignment (W4.SymExpr sym) idx ->
      m (W4.SymExpr sym tp')
    resolveArr arr_base idx_base = do
      arr <- go arr_base
      idx <- TFC.traverseFC go idx_base
      val <- liftIO $ W4.arrayLookup sym arr idx
      case arr of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.UpdateArray _ _ arr' idx' upd_val -> do
            eqIdx <- Ctx.zipWithM (\e1 e2 -> Const <$> f e1 e2) idx idx'
            case TFC.foldrFC andPred (Just True) eqIdx of
              Just True -> return $ upd_val
              Just False -> resolveArr arr' idx
              _ -> return val
          W4B.SelectArray _ arr' idx' -> do
            arr'' <- resolveArr arr' idx'
            case arr'' == arr of
              True -> return val
              False -> resolveArr arr'' idx
          _ -> return val
        _ -> return val
    
    go :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e)
      case e of
        W4B.AppExpr a0 -> case W4B.appExprApp a0 of
          W4B.SelectArray _ arr idx -> resolveArr arr idx
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
  -- | individual "atoms" of a predicate
  PredSet sym ->
  -- | decision for the provability of a predicate
  (W4.Pred sym -> m Bool) ->
  W4.Pred sym ->
  m (W4.Pred sym)
minimalPredAtoms sym atoms provable p = do
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
  CMS.foldM applyAtom p (exprSetToList @sym atoms)
