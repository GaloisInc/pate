{-|
Module           : What4.PredMap
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Map with What4 predicates in the range, indexed by the default predicate merge operation
(conjunction or disjuction) to use in the case of key clashes.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module What4.PredMap (
    type PredOpK
  , type PredDisjT
  , type PredConjT
  , PredMap
  , PredOpRepr(..)
  , predOpRepr
  , applyPredOp
  , mulPredOp
  , empty
  , singleton
  , merge
  , intersect
  , dropUnit
  , traverse
  , alter
  , alter'
  , lookup
  , toList
  , fromList
  , mux
  , collapse
  , predOpUnit
  , isPredOpUnit
  ) where

import           Prelude hiding ( lookup, traverse )

import qualified Control.Monad.IO.Class as IO
import           Control.Monad ( foldM )

import           Data.Proxy (Proxy(..))
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as MapM

import           Data.Parameterized.Classes
import           Data.Parameterized.HasRepr
import           Data.Parameterized.WithRepr

import qualified What4.Interface as W4

data PredOpK =
    PredConjT
  | PredDisjT

type PredConjT = 'PredConjT
type PredDisjT = 'PredDisjT

data PredMap sym f (k :: PredOpK) where
  PredMap :: { predOpRepr :: PredOpRepr k
             , predMap :: Map.Map f (W4.Pred sym)
             } -> PredMap sym f k

data PredOpRepr k where
  PredConjRepr :: PredOpRepr PredConjT
  PredDisjRepr :: PredOpRepr PredDisjT

instance HasRepr (PredMap sym f) PredOpRepr where
  typeRepr pm = predOpRepr pm

instance KnownRepr PredOpRepr 'PredConjT where
  knownRepr = PredConjRepr

instance KnownRepr PredOpRepr 'PredDisjT where
  knownRepr = PredDisjRepr

instance IsRepr PredOpRepr

empty ::
  PredOpRepr k -> PredMap sym f k
empty r = PredMap r Map.empty

singleton ::
  Ord f =>
  PredOpRepr k ->
  f ->
  W4.Pred sym ->
  PredMap sym f k
singleton r f p = PredMap r (Map.singleton f p)

-- | Operation where 'predOpUnit' is the unit element (i.e. a + unit = a, a + dualUnit = dualUnit)
applyPredOp ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  sym ->
  PredOpRepr k ->
  W4.Pred sym ->
  W4.Pred sym ->
  m (W4.Pred sym)
applyPredOp sym PredConjRepr p1 p2 = IO.liftIO $ W4.andPred sym p1 p2
applyPredOp sym PredDisjRepr p1 p2 = IO.liftIO $ W4.orPred sym p1 p2

-- | Dual of 'applyPredOp' (i.e. a * unit = unit, a * dualUnit = a)
mulPredOp ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  sym ->
  PredOpRepr k ->
  W4.Pred sym ->
  W4.Pred sym ->
  m (W4.Pred sym)
mulPredOp sym PredConjRepr p1 p2 = IO.liftIO $ W4.orPred sym p1 p2
mulPredOp sym PredDisjRepr p1 p2 = IO.liftIO $ W4.andPred sym p1 p2

predOpUnit ::
  W4.IsExprBuilder sym =>
  sym ->
  PredOpRepr k ->
  W4.Pred sym
predOpUnit sym PredConjRepr = W4.truePred sym
predOpUnit sym PredDisjRepr = W4.falsePred sym

isPredOpUnit ::
  W4.IsExprBuilder sym =>
  f sym ->
  PredOpRepr k ->
  W4.Pred sym ->
  Bool
isPredOpUnit _ r p = case (W4.asConstantPred p, r) of
  (Just True, PredConjRepr) -> True
  (Just False, PredDisjRepr) -> True
  _ -> False

-- | Union (elements are joined with (+)), missing elements are preserved
merge ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  Ord f =>
  sym ->
  PredMap sym f k ->
  PredMap sym f k ->
  m (PredMap sym f k)
merge sym pm1 pm2 = PredMap <$> pure (typeRepr pm1) <*>
    MapM.mergeA
      MapM.preserveMissing
      MapM.preserveMissing
      (MapM.zipWithAMatched (\_ p1' p2' -> applyPredOp sym (typeRepr pm1) p1' p2'))
      (predMap pm1)
      (predMap pm2)

-- | Union (elements are joined with (+))
intersect ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  Ord f =>
  sym ->
  PredMap sym f k ->
  PredMap sym f k ->
  m (PredMap sym f k)
intersect sym pm1 pm2 = PredMap <$> pure (typeRepr pm1) <*>
    MapM.mergeA
       MapM.dropMissing
       MapM.dropMissing
      (MapM.zipWithAMatched (\_ p1' p2' -> mulPredOp sym (typeRepr pm1) p1' p2'))
      (predMap pm1)
      (predMap pm2)

mux ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  Ord f =>
  sym ->
  W4.Pred sym ->
  PredMap sym f k ->
  PredMap sym f k ->
  m (PredMap sym f k)
mux sym p pmT pmF = case W4.asConstantPred p of
  Just True -> return pmT
  Just False -> return pmF
  _ -> PredMap <$> pure (typeRepr pmT) <*>
    (IO.liftIO $ MapM.mergeA
      (MapM.traverseMissing (\_ pT -> W4.baseTypeIte sym p pT (predOpUnit sym (typeRepr pmT))))
      (MapM.traverseMissing (\_ pF -> W4.baseTypeIte sym p (predOpUnit sym (typeRepr pmT)) pF))
      (MapM.zipWithAMatched (\_ pT pF -> W4.baseTypeIte sym p pT pF))
      (predMap pmT)
      (predMap pmF))

-- | Remove entries from the map that point to the unit element of the
-- underlying predicate operation.
-- This preserves the invariant that 'lookup k m' == 'lookup k (dropUnit m)' for
-- any key 'k'.
dropUnit ::
  forall sym f k.
  W4.IsExprBuilder sym =>
  PredMap sym f k ->
  PredMap sym f k
dropUnit pm  = PredMap (typeRepr pm) $
  Map.mapMaybe (\p -> case isPredOpUnit (Proxy @sym) (typeRepr pm) p of
                        True -> Nothing
                        _ -> Just p) (predMap pm)

-- | Traverse and modify the predicate associated with each key.
traverse ::
  Applicative m =>
  PredMap sym f k ->
  (f -> W4.Pred sym -> m (W4.Pred sym)) ->
  m (PredMap sym f k)
traverse pm f = PredMap <$> pure (typeRepr pm) <*> Map.traverseWithKey f (predMap pm)

-- | Alter the key-predicate pairs in a 'PredMap'.
-- When any keys are modified, the map is safely rebuilt according
-- to the underlying predicate operation in the case of duplicate entries
-- in the resulting map.
alter ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  Ord f =>
  sym ->
  PredMap sym f k ->
  (f -> W4.Pred sym -> m (f, W4.Pred sym)) ->
  m (PredMap sym f k)
alter sym pm f = do
  let (ks, vs) = unzip $ Map.toAscList (predMap pm)
  (ks', vs') <- unzip <$> mapM (\(k, p) -> f k p) (zip ks vs)
  case ks == ks' of
    -- if the keys are unmodified, we can just treat this like a normal traversal
    True -> return $ PredMap (typeRepr pm) (Map.fromAscList (zip ks' vs'))
    -- otherwise we have to use the 'fromList' defined here which accounts
    -- for possible duplicate entries
    False -> fromList sym (typeRepr pm) (zip ks' vs')

-- | Alter the key-predicate pairs in a 'PredMap', rebuilding
-- the map safely according to the underlying predicate operation
-- in the case of duplicate entries in the resulting map.
alter' ::
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  Ord g =>
  sym ->
  PredMap sym f k ->
  (f -> W4.Pred sym -> m (g, W4.Pred sym)) ->
  m (PredMap sym g k)
alter' sym pm f = do
  pm' <- mapM (\(k, p) -> f k p) (Map.toList (predMap pm))
  fromList sym (typeRepr pm) pm'

-- | Lookup an entry in the underlying map, returning the unit entry of
-- the predicate operation for the map if the entry is not present
lookup ::
  forall sym f k.
  W4.IsExprBuilder sym =>
  Ord f =>
  sym ->
  f ->
  PredMap sym f k ->
  W4.Pred sym
lookup sym f pm = case Map.lookup f (predMap pm) of
  Just p -> p
  Nothing -> predOpUnit sym (typeRepr pm)

toList ::
  PredMap sym f k ->
  [(f, W4.Pred sym)]
toList pm = Map.toList (predMap pm)

-- | Fold the entries of the map together using (+) and the given operation
collapse :: 
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  sym ->
  (f -> f -> m f) ->
  f ->
  PredMap sym f k -> 
  m (f, W4.Pred sym)
collapse sym f v_init pm = do
  let repr = predOpRepr pm
  foldM (\(v1, p1) (v2, p2) -> (,) <$> f v1 v2 <*> applyPredOp sym repr p1 p2) (v_init, predOpUnit sym repr) (toList pm)

-- | Convert a list of key-predicate pairs into a 'PredMap', merging duplicate
-- entries according to the corresponding predicate operation indicated by
-- the given 'PredOpRepr'
fromList ::
  forall f m k sym.
  Ord f =>
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  sym ->
  PredOpRepr k ->
  [(f, W4.Pred sym)] ->
  m (PredMap sym f k)
fromList sym r l = foldM (\ms (f,p) -> merge sym (singleton r f p) ms) (empty r) l
