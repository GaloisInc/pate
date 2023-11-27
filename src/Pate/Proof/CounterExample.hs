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
{-# LANGUAGE UndecidableSuperClasses #-}

module Pate.Proof.CounterExample 
  ( getInequivalenceResult
  , getCondEquivalenceBindings
  , getPathCondition
  ) where

import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import           Data.Maybe (fromMaybe)


import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.SatResult as W4R

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PB
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Condition as PEC
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
import qualified Pate.SimState as PS
import           What4.ExprHelpers as WEH
import qualified What4.PathCondition as WPC
import qualified Pate.Config as PC
import Data.Coerce (coerce, Coercible)
import Unsafe.Coerce (unsafeCoerce)

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
  SymGroundEvalFn sym MT.GroundInfo ->
  EquivM sym arch (PF.InequivalenceResult arch)
getInequivalenceResult defaultReason pre post slice fn = withSym $ \sym -> 
  PG.ground sym fn (PF.InequivalenceResultSym slice pre post defaultReason) PF.InequivalenceResult



  {-
  result <- 
  PG.traverseWithGroundSym result $ \groundResult -> do
    let
      groundPost = PF.ineqPost groundResult
      groundSlice = PF.ineqSlice groundResult
      reason = fromMaybe defaultReason (getInequivalenceReason groundPost (PF.slBlockPostState groundSlice))
    return $ groundResult { PF.ineqReason = reason }
  -}

{-
ground ::
  PEM.ExprMappable sym (a sym) =>
  SymGroundEvalFn sym ->
  a sym ->
  EquivM sym arch (PG.Grounded a)
ground fn a =  withSym $ \sym -> do
  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  stackRegionC <- execGroundFn fn (W4.natToIntegerPure stackRegion)
  PG.ground sym fn (mkGroundInfo fn stackRegionC) a

mkGroundInfo ::
  forall sym arch tp.
  SymGroundEvalFn sym ->
  Integer ->
  W4.SymExpr sym tp ->
  W4G.GroundValue tp ->
  EquivM sym arch (Maybe (PG.GroundInfo tp))
mkGroundInfo fn stackRegion e gv = do
  ptrOpTags <- getPointerTags fn e
  let (mstackRegionRepr :: Maybe (tp :~: W4.BaseIntegerType)) = case W4.exprType e of
        W4.BaseIntegerRepr | stackRegion == gv -> Just Refl
        _ -> Nothing
  case (ptrOpTags == mempty, mstackRegionRepr) of
    (True, Nothing) -> return Nothing
    _ -> return $ Just $ PG.GroundInfo ptrOpTags mstackRegionRepr
-}

data Bindings sym tp where
  Bindings :: MapF.MapF (W4.SymExpr sym) W4G.GroundValueWrapper -> Bindings sym tp

instance OrdF (W4.SymExpr sym) => Semigroup (Bindings sym tp) where
  (Bindings m1) <> (Bindings m2) = Bindings $ MapF.mergeWithKey (\_ left _ -> Just left) id id m1 m2

instance OrdF (W4.SymExpr sym) => Monoid (Bindings sym tp) where
  mempty = Bindings MapF.empty

singleBinding ::
  W4.SymExpr sym tp ->
  SymGroundEvalFn sym k ->
  EquivM sym arch (Bindings sym tp)
singleBinding e fn = do
  grnd <- execGroundFn fn e
  return $ Bindings $ MapF.singleton e (W4G.GVW grnd)

getCondEquivalenceBindings ::
  forall sym arch k.
  W4.Pred sym ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym k ->
  EquivM sym arch (MapF.MapF (W4.SymExpr sym) W4G.GroundValueWrapper)
getCondEquivalenceBindings eqCond fn = withValid $ do
  cache <- W4B.newIdxCache
  let
    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Bindings sym tp2 -> EquivM sym arch (Bindings sym tp2)
    acc e binds = do
      Bindings binds' <- go e
      return $ binds <> (Bindings binds')

    go :: W4.SymExpr sym tp -> EquivM sym arch (Bindings sym tp)
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> case W4.exprType e of
        W4.BaseArrayRepr _ _ -> return mempty
        _ -> singleBinding e fn
      W4B.AppExpr a0 -> case W4B.appExprApp a0 of
        W4B.SelectArray _ _ idx -> do
          binds' <- singleBinding e fn
          binds'' <- TFC.foldrMFC (\x a -> acc x a) mempty idx
          return $ binds' <> binds''
        app -> TFC.foldrMFC (\x a -> acc x a) mempty app
      W4B.NonceAppExpr a0 -> TFC.foldrMFC (\x a -> acc x a) mempty (W4B.nonceExprApp a0)
      _ -> return mempty
  Bindings binds <- go eqCond
  return binds

getGenPathCondition ::
  forall sym arch k f.
  PEM.ExprMappable sym f =>
  SymGroundEvalFn sym k ->
  f ->
  EquivM sym arch (W4.Pred sym)
getGenPathCondition fn f = withSym $ \sym -> do
  isSatIO <- getSatIO
  withGroundEvalFn fn $ \fn' -> do
    let
      simplifyExpr :: W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp')
      simplifyExpr e =
        -- simplifying the bitvector operations removes redundant
        -- muxes introduced by the ARM semantics specifically, which obfuscate
        -- the control flow of block slices.
        WEH.simplifyBVOps sym e

    f' <- PEM.mapExpr sym simplifyExpr f
    getGenPathConditionIO sym fn' isSatIO f'

getGenPathConditionIO ::
  forall sym  t st fs f.
  sym ~ W4B.ExprBuilder t st fs =>
  PEM.ExprMappable sym f =>
  sym ->
  W4G.GroundEvalFn t ->
  (W4.Pred sym -> IO (Maybe Bool)) ->
  f ->
  IO (W4.Pred sym)
getGenPathConditionIO sym fn isSat e = do
  let
    f :: forall tp'. W4.SymExpr sym tp' -> W4.Pred sym -> IO (W4.Pred sym)
    f e' cond = do
      cond' <- WPC.getPathCondition sym fn isSat e'
      W4.andPred sym cond cond'
  
  PEM.foldExpr sym f e (W4.truePred sym)


-- | Compute a predicate that represents the path condition for
-- registera which disagree in the given counter-example (i.e. the model
-- represented by a 'SymGroundEvalFn').
-- If all registers agree, then the resulting predicate is True.
getRegPathCondition ::
  forall sym arch k v.
  -- | The target condition
  PEC.RegisterCondition sym arch v ->
  SymGroundEvalFn sym k ->
  EquivM sym arch (W4.Pred sym)
getRegPathCondition regCond fn = withSym $ \sym ->
  TF.foldrMF (\x y -> getRegPath x y) (W4.truePred sym) (PEC.regCondPreds regCond)
  where
    getRegPath ::
      Const (PAS.AssumptionSet sym) tp ->
      W4.Pred sym ->
      EquivM_ sym arch (W4.Pred sym)
    getRegPath (Const regCondAsm) pathCond = withSym $ \sym -> do
      regCond_pred <- liftIO $ PAS.toPred sym regCondAsm
      execGroundFn fn regCond_pred >>= \case
        -- if the post-equivalence is satisfied for this entry, then we don't need
        -- to look at the path condition for these values
        True -> return pathCond
        -- for an entry that disagrees in the model, we extract the problematic path condition
        False -> do
          regPath' <- getGenPathCondition fn regCond_pred
          liftIO $ W4.andPred sym pathCond regPath'

-- | Return a function for deciding predicate satisfiability based on the current
-- assumption state. The function caches the result on each predicate, and therefore is
-- only valid under the current set of assumptions (i.e. the 'envCurrentFrame').
getSatIO ::
  forall sym arch.
  EquivM sym arch (W4.Pred sym -> IO (Maybe Bool))
getSatIO = withValid $ do
  cache <- W4B.newIdxCache
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  let
    isSat :: W4.Pred sym -> EquivM sym arch (Maybe Bool)
    isSat p' = case W4.asConstantPred p' of
      Just b -> return $ Just b
      Nothing -> fmap getConst $ W4B.idxCacheEval cache p' $ fmap Const $ do
        r <- checkSatisfiableWithModel heuristicTimeout "getPathCondition" p' $ \res -> case res of
          W4R.Unsat _ -> return $ Just False
          W4R.Sat _ -> return $ Just True
          W4R.Unknown -> return Nothing
        case r of
          Left _ -> return Nothing
          Right a -> return a

  IO.withRunInIO $ \runInIO -> return (\p -> runInIO (isSat p))

-- | Compute a predicate that represents the path condition for
-- values which disagree in the given counter-example (i.e. the model represented by
-- the 'SymGroundEvalFn).
-- This procedure attempts to produce a "minimal" predicate with respect
-- to the current set of assumptions (i.e. excluding paths which are infeasible, and
-- excluding conditions which are necessarily true).
getPathCondition ::
  forall sym arch k v.
  PE.StatePostCondition sym arch v ->
  PS.SimOutput sym arch v PB.Original ->
  PS.SimOutput sym arch v PB.Patched ->
  SymGroundEvalFn sym k ->
  EquivM sym arch (W4.Pred sym)
getPathCondition stCond outO outP fn = withSym $ \sym -> do
  regCond <- getRegPathCondition (PE.stRegPostCond stCond) fn
  withAssumption regCond $ do
    memOCond <- getGenPathCondition fn (PS.simOutMem outO)
    withAssumption memOCond $ do
      memPCond <- getGenPathCondition fn (PS.simOutMem outP)
      liftIO $ W4.andPred sym regCond memOCond >>= W4.andPred sym memPCond

isMemOpValid ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd MT.GroundInfo =>
  PED.EquivalenceDomain grnd arch ->
  MapF.Pair (PMC.MemCell grnd arch) (PF.BlockSliceMemOp grnd) -> Bool
isMemOpValid dom (MapF.Pair cell mop) =
  (not (PFI.cellInGroundDomain dom cell)) || (not (PG.groundValue $ PF.slMemOpCond mop)) || (PG.groundValue $ PF.slMemOpEquiv mop)

isRegValid ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd MT.GroundInfo =>
  PED.EquivalenceDomain grnd arch ->
  MapF.Pair (MM.ArchReg arch) (PF.BlockSliceRegOp grnd) -> Bool
isRegValid dom (MapF.Pair r rop) =
  (not (PFI.regInGroundDomain (PED.eqDomainRegisters dom) r)) || (PG.groundValue $ PF.slRegOpEquiv rop)

getInequivalenceReason ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd MT.GroundInfo =>
  PED.EquivalenceDomain grnd arch ->
  PF.BlockSliceState grnd arch ->
  Maybe PEE.InequivalenceReason
getInequivalenceReason dom st =
  if | not $ all (isMemOpValid dom) (MapF.toList $ PF.slMemState st) -> Just PEE.InequivalentMemory
     | not $ all (isRegValid dom) (MapF.toList $ MM.regStateMap $ PF.slRegState st) -> Just PEE.InequivalentRegisters
     | otherwise -> Nothing
