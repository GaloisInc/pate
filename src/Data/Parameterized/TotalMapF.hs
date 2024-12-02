{-|
Module           : Data.Parameterized.TotalMapF
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Reified total functions (maps) with testable equality and ordering.
Implemented as a wrapped Data.Parameterized.Map with a constrained interface. 

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Data.Parameterized.TotalMapF
  ( 
      TotalMapF
    , HasTotalMapF(..)
    , totalMapRepr
    , apply
    , compose
    , zip
    , mapWithKey
    , traverseWithKey
  ) where

import           Prelude hiding ( zip )
import qualified Data.List as List

import           Data.Kind (Type)
import           Data.Functor.Const

import           Data.Parameterized.TraversableF
import           Data.Parameterized.PairF
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( MapF )

-- | A wrapped 'MapF' from 'a' to 'b' that covers all possible values of 'a' for all instances.
--   All values of 'a' is defined by 'allValues' from 'HasTotalMapF', which is trusted.
--   If 'allValues' is incomplete then the behavior of this datatype is undefined and
--   may raise runtime errors.
newtype TotalMapF (a :: k -> Type) (b :: k -> Type) = TotalMapF (MapF a b)
  deriving (FoldableF, FunctorF, Show)

instance TraversableF (TotalMapF a) where
  traverseF f (TotalMapF tm) = TotalMapF <$> traverseF f tm

mapWithKey :: (forall x. a x -> b x -> c x) -> TotalMapF a b -> TotalMapF a c
mapWithKey f (TotalMapF m) = TotalMapF $ MapF.mapWithKey f m

traverseWithKey :: Applicative m => (forall x. a x -> b x -> m (c x)) -> TotalMapF a b -> m (TotalMapF a c)
traverseWithKey f (TotalMapF m) = TotalMapF <$> MapF.traverseWithKey f m

instance (TestEquality a, (forall x. (Eq (b x)))) => Eq (TotalMapF a b) where
  m1 == m2 = all (\(MapF.Pair _ (PairF b1 b2)) -> b1 == b2) (zipToList m1 m2)

instance (OrdF a, (forall x. (Ord (b x)))) => Ord (TotalMapF a b) where
  compare m1 m2 = compareZipped (map (\(MapF.Pair _ v) -> Some v) $ zipToList m1 m2)

compareZipped :: (forall x. (Ord (a x))) => [Some (PairF a a)] -> Ordering
compareZipped (Some (PairF x1 x2):xs) = case compare x1 x2 of
  EQ -> compareZipped xs
  LT -> LT
  GT -> GT
compareZipped [] = EQ

class HasTotalMapF a where
  -- | A list of all possible values for this type (for all possible instances).
  --   TODO: Unclear how this will behave if defined for infinite types via a lazy list
  allValues :: [Some a]

-- | Canonical total map for a given type. Use FunctorF instance to create maps to other types.
totalMapRepr :: forall a. (OrdF a, HasTotalMapF a) => TotalMapF a (Const ())
totalMapRepr = TotalMapF $ MapF.fromList (map (\(Some x) -> MapF.Pair x (Const ())) $ allValues @a)

apply :: OrdF a => TotalMapF (a :: k -> Type) b -> (forall x. a x -> b x)
apply (TotalMapF m) k = case MapF.lookup k m of
  Just v -> v
  Nothing -> error "TotalMapF apply: internal failure. Likely 'HasTotalMapF' instance is incomplete."

compose :: (OrdF a, OrdF b) => TotalMapF a b -> TotalMapF b c -> TotalMapF a c
compose atoB btoC = fmapF (apply btoC) atoB

-- | Same as 'zip' but skips re-building the map
zipToList :: TestEquality a => TotalMapF a b -> TotalMapF a c -> [MapF.Pair a (PairF b c)]
zipToList m1 m2 = 
  let 
    m1' = toList m1
    m2' = toList m2
    err = error "TotalMapF zip: internal failure. Likely 'HasTotalMapF' instance is incomplete."
  in case length m1' == length m2' of
    True -> map (\(MapF.Pair a1 b, MapF.Pair a2 c) -> case testEquality a1 a2 of Just Refl -> MapF.Pair a1 (PairF b c); Nothing -> err) (List.zip m1' m2')
    False -> err

zip :: OrdF a => TotalMapF a b -> TotalMapF a c -> TotalMapF a (PairF b c)
zip m1 m2 = TotalMapF (MapF.fromList $ zipToList m1 m2)

toList :: TotalMapF a b -> [MapF.Pair a b]
toList (TotalMapF m) = MapF.toList m
