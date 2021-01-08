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

module What4.ExprHelpers (
    iteM
  , impM
  , andM
  , orM
  , allPreds
  , anyPred
  , VarBinding(..)
  , rebindExpr
  , mapExprPtr
  , freshPtr
  , freshPtrVar
  , freshPtrBytes
  , mkSafeAsserts
  , ExprFilter(..)
  , getIsBoundFilter
  , assertPrefix
  ) where

import           GHC.TypeNats
import           Unsafe.Coerce -- for mulMono axiom

import           Control.Monad.Except
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.ST ( RealWorld, stToIO )

import qualified Data.HashTable.ST.Basic as H
import qualified Data.Text as T
import           Data.Word (Word64)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List ( foldl' )

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Symbol as W4

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
     bindVar :: W4.BoundVar sym tp
   , bindVal :: W4.SymExpr sym tp
   }

rebindExpr ::
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (VarBinding sym) ctx ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
rebindExpr sym binds expr = do
  let vars = TFC.fmapFC bindVar binds
  let vals = TFC.fmapFC bindVal binds
  fn <- W4.definedFn sym W4.emptySymbol vars expr W4.AlwaysUnfold
  W4.applySymFn sym fn vals


mapExprPtr ::
  forall sym w.
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
  CLM.LLVMPtr sym w ->
  IO (CLM.LLVMPtr sym w)  
mapExprPtr _sym f (CLM.LLVMPointer reg off) = do
  reg' <- f reg
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
  reg <- W4.freshConstant sym W4.emptySymbol W4.BaseNatRepr
  return $ CLM.LLVMPointer reg off

freshPtrVar ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  W4.NatRepr w ->
  W4.SolverSymbol ->
  IO (CLM.LLVMPtr sym w, W4.BoundVar sym W4.BaseNatType, W4.BoundVar sym (W4.BaseBVType w))
freshPtrVar sym w nm = do
  offVar <- W4.freshBoundVar sym nm (W4.BaseBVRepr w)
  regVar <- W4.freshBoundVar sym nm W4.BaseNatRepr
  let ptr = CLM.LLVMPointer (W4.varExpr sym regVar) (W4.varExpr sym offVar)
  return $ (ptr, regVar, offVar)

mulMono :: forall p q x w. (1 <= x, 1 <= w) => p x -> q w -> W4.LeqProof 1 (x W4.* w)
mulMono _x w = unsafeCoerce (W4.leqRefl w)


-- Clagged from What4.Builder
type BoundVarMap t = H.HashTable RealWorld Word64 (Set (Some (W4B.ExprBoundVar t)))

boundVars :: W4B.Expr t tp -> IO (BoundVarMap t)
boundVars e0 = do
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
boundVars' visited (W4B.BoundVarExpr v)
  | W4B.QuantifierVarKind <- W4B.bvarKind v = do
      let idx = N.indexValue (W4B.bvarId v)
      cacheExec visited idx $
        return (S.singleton (Some v))
boundVars' _ (W4B.BoundVarExpr{}) = return S.empty
boundVars' _ (W4B.SemiRingLiteral{}) = return S.empty
boundVars' _ (W4B.BoolExpr{}) = return S.empty
boundVars' _ (W4B.StringExpr{}) = return S.empty
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
  bvs <- liftIO $ boundVars expr
  return $ ExprFilter $ \bv -> do
    case bv of
      W4B.BoundVarExpr bv' -> do
        let idx = N.indexValue (W4B.bvarId bv')
        stToIO $ H.lookup bvs idx >>= \case
          Just bvs' -> return $ S.member (Some bv') bvs'
          _ -> return False
      _ -> return False

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
    go e = W4B.idxCacheEval cache e $ case e of
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
