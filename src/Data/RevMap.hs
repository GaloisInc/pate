{-# LANGUAGE LambdaCase #-}
{-|
Module           : Data.RevMap
Copyright        : (c) Galois, Inc 2023
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Map with reverse lookup
-}

module Data.RevMap
  ( RevMap
  , empty
  , singleton
  , lookup
  , reverseLookup
  , minView
  , minView_value
  , delete
  , alter
  , insertWith
  ) where

import Prelude hiding (lookup)

import qualified Data.Set as Set
import           Data.Set (Set)

import qualified Data.Map as Map
import           Data.Map (Map)
import Data.Maybe (fromMaybe)

data RevMap a b =
  RevMap (Map a b) (Map b (Set a))

empty :: RevMap a b
empty = RevMap Map.empty Map.empty

lookup :: (Ord a) => a -> RevMap a b -> Maybe b
lookup a (RevMap a_to_b _) = Map.lookup a a_to_b

minView :: (Ord a, Ord b) => RevMap a b -> Maybe (a, RevMap a b)
minView m@(RevMap a_to_b _) = case Set.minView (Map.keysSet a_to_b) of
  Just (a,_) -> Just (a, delete a m)
  Nothing -> Nothing

-- | Return a pair such that 'b' is the smallest value in the map codomain,
--   and 'a' is the smallest value that maps to 'b'
minView_value :: (Ord a, Ord b) => RevMap a b -> Maybe (a, b, RevMap a b)
minView_value m@(RevMap a_to_b b_to_as) = case Set.minView (Map.keysSet b_to_as) of
  Just (b, _) -> case Set.minView (reverseLookup b m) of
    Just (a, _) -> Just (a, b, delete a m)
    Nothing -> minView_value (RevMap a_to_b (Map.delete b b_to_as))
  Nothing -> Nothing


singleton :: a -> b -> RevMap a b
singleton a b = RevMap (Map.singleton a b) (Map.singleton b (Set.singleton a))

reverseLookup :: Ord b => b -> RevMap a b -> Set a
reverseLookup b (RevMap _ b_to_as) = case Map.lookup b b_to_as of
  Just as -> as
  Nothing -> Set.empty

reverseAdjust :: Ord b => b -> (Set a -> Set a) -> RevMap a b -> RevMap a b
reverseAdjust b f (RevMap a_to_b b_to_as) = 
  RevMap a_to_b (Map.alter (\mas -> Just (f (fromMaybe Set.empty mas))) b b_to_as)

delete :: (Ord a, Ord b) => a -> RevMap a b -> RevMap a b
delete a m@(RevMap a_to_b b_to_a) = case Map.lookup a a_to_b of
  Just b -> reverseAdjust b (Set.delete a) (RevMap (Map.delete a a_to_b) b_to_a)
  Nothing -> m


alter :: (Ord a, Ord b) => (Maybe b -> Maybe b) -> a -> RevMap a b -> RevMap a b
alter f a m@(RevMap a_to_b b_to_as) = case Map.lookup a a_to_b of
  Just b -> case f (Just b) of
    Just b' -> reverseAdjust b' (Set.insert a) $ 
      reverseAdjust b (Set.delete a) (RevMap (Map.insert a b' a_to_b) b_to_as)
    Nothing -> delete a m
  Nothing -> case f Nothing of
    Just b -> 
      RevMap (Map.insert a b a_to_b)
             (Map.insertWith Set.union b (Set.singleton a) b_to_as)
    Nothing -> m


insertWith :: (Ord a, Ord b) => (b -> b -> b) -> a -> b -> RevMap a b -> RevMap a b
insertWith f a b m = alter (\case {Just b' -> Just (f b b'); Nothing -> Just b}) a m