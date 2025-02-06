{-|
Module           : Pate.Proof.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Presenting counter-examples to failed equivalence checks
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Proof.CounterExample 
  ( getInequivalenceResult
  ) where

import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import           Data.Maybe (fromMaybe)


import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Ground as PG
import           What4.ExprHelpers as WEH

-- | Generate a structured counterexample for an equivalence
-- check from an SMT model.
-- Takes a symbolic 'PF.BlockSliceTransition' and grounds it according
-- to the model. Additionally, the given pre-domain and post-domains are
-- similarly grounded, so the counter-example contains which concrete locations
-- were assumed equivalent, and any concrete locations that are not equivalent
-- after the block slice transition.
getInequivalenceResult ::
  forall sym arch.
  PEE.InequivalenceReason ->
  -- | pre-domain
  PED.EquivalenceDomain sym arch ->
  -- | post-domain
  PED.EquivalenceDomain sym arch ->
  -- | the transition that was attempted to be proven equivalent
  -- in the given domains
  PF.BlockSliceTransition sym arch ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (PF.InequivalenceResult arch)
getInequivalenceResult defaultReason pre post slice fn = do
  result <- ground fn $ PF.InequivalenceResultSym slice pre post defaultReason
  PG.traverseWithGroundSym result $ \groundResult -> do
    let
      groundPost = PF.ineqPost groundResult
      groundSlice = PF.ineqSlice groundResult
      reason = fromMaybe defaultReason (getInequivalenceReason groundPost (PF.slBlockPostState groundSlice))
    return $ groundResult { PF.ineqReason = reason }

ground ::
  forall sym arch a.
  PEM.ExprFoldableIO sym (a sym) =>
  SymGroundEvalFn sym ->
  a sym ->
  EquivM sym arch (PG.Grounded a)
ground fn a =  withSym $ \sym -> do
  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  IO.withRunInIO $ \f ->
    PG.ground sym stackRegion (\e -> f (mkGroundInfo fn e)) a

mkGroundInfo ::
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  EquivM sym arch (PG.GroundInfo tp)
mkGroundInfo fn e = do
  ptrOpTags <- getPointerTags fn e
  val <- execGroundFn fn e
  return $ PG.GroundInfo ptrOpTags val

data Bindings sym tp where
  Bindings :: MapF.MapF (W4.SymExpr sym) W4G.GroundValueWrapper -> Bindings sym tp

instance OrdF (W4.SymExpr sym) => Semigroup (Bindings sym tp) where
  (Bindings m1) <> (Bindings m2) = Bindings $ MapF.mergeWithKey (\_ left _ -> Just left) id id m1 m2

instance OrdF (W4.SymExpr sym) => Monoid (Bindings sym tp) where
  mempty = Bindings MapF.empty

isMemOpValid ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  MapF.Pair (PMC.MemCell grnd arch) (PF.BlockSliceMemOp grnd) -> Bool
isMemOpValid dom (MapF.Pair cell mop) =
  (not (PFI.cellInGroundDomain dom cell)) || (not (PG.groundValue $ PF.slMemOpCond mop)) || (PG.groundValue $ PF.slMemOpEquiv mop)

isRegValid ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  MapF.Pair (MM.ArchReg arch) (PF.BlockSliceRegOp grnd) -> Bool
isRegValid dom (MapF.Pair r rop) =
  (not (PFI.regInGroundDomain (PED.eqDomainRegisters dom) r)) || (PG.groundValue $ PF.slRegOpEquiv rop)

getInequivalenceReason ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  PF.BlockSliceState grnd arch ->
  Maybe PEE.InequivalenceReason
getInequivalenceReason dom st =
  if | not $ all (isMemOpValid dom) (MapF.toList $ PF.slMemState st) -> Just PEE.InequivalentMemory
     | not $ all (isRegValid dom) (MapF.toList $ MM.regStateMap $ PF.slRegState st) -> Just PEE.InequivalentRegisters
     | otherwise -> Nothing


-- | Classify whether or not the given expression depends
-- on undefined pointers in the given model
getPointerTags ::
  forall sym arch tp.
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  EquivM sym arch MT.UndefPtrOpTags
getPointerTags fn e_outer = withValid $ withSym $ \sym -> do
  classify <- CMR.asks (MT.undefPtrClassify . envUndefPointerOps)
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> EquivM sym arch MT.UndefPtrOpTags
    go e = fmap getConst $ W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> Const <$> (liftIO $ MT.classifyExpr classify e)
      W4B.AppExpr a0 -> case W4B.appExprApp a0 of
        W4B.BaseIte _ _ cond eT eF -> fmap Const $ do
          cond_tags <- go cond
          branch_tags <- execGroundFn fn cond >>= \case
            True -> go eT
            False -> go eF
          return $ cond_tags <> branch_tags
        app -> TFC.foldrMFC (\e' tags -> acc e' tags) mempty app
      W4B.NonceAppExpr a0 -> TFC.foldrMFC (\e' tags -> acc e' tags) mempty (W4B.nonceExprApp a0)
      _ -> return mempty

    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Const (MT.UndefPtrOpTags) tp2 -> EquivM sym arch (Const (MT.UndefPtrOpTags) tp2)
    acc e (Const tags) = do
      tags' <- go e
      return $ Const $ tags <> tags'

  e_outer' <- resolveConcreteLookups sym (\p -> Just <$> execGroundFn fn p) e_outer
  go e_outer'
