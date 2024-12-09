{-|
Module           : Data.Parameterized.SetF
Copyright        : (c) Galois, Inc 2021
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Sets over a types with a parameteric type parameter
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
{-# LANGUAGE OverloadedStrings #-}

module Data.Parameterized.SetF
  ( SetF
  , AsOrd(..)
  , empty
  , singleton
  , insert
  , toList
  , fromList
  , member
  , size
  , filter
  , lookupMin
  , union
  , unions
  , null
  , toSet
  , fromSet
  , map
  , ppSetF
  , asSet
  ) where

import Prelude hiding (filter, null, map)
import qualified Data.List as List
import           Data.Parameterized.Classes
import qualified Data.Foldable as Foldable
import qualified Control.Lens as L

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import           Data.Set (Set)
import qualified Data.Set as S
import Unsafe.Coerce (unsafeCoerce)

newtype AsOrd f tp where
  AsOrd :: { unAsOrd :: f tp } -> AsOrd f tp

newtype SetF f tp = SetF (Set (AsOrd f tp))

instance TestEquality f => Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) | Just Refl <- testEquality a b = True
  _ == _ = False

instance OrdF f => Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

deriving instance OrdF f => Semigroup (SetF f tp)
deriving instance OrdF f => Monoid (SetF f tp)


empty :: SetF f tp
empty = SetF S.empty

singleton ::
  OrdF f =>
  f tp ->
  SetF f tp
singleton e = SetF (S.singleton (AsOrd e))

insert ::
  OrdF f =>
  f tp ->
  SetF f tp ->
  SetF f tp
insert e (SetF es) = SetF (S.insert (AsOrd e) es)

toList ::
  SetF f tp ->
  [f tp]
toList (SetF es) = List.map unAsOrd $ S.toList es

fromList ::
  OrdF f =>
  [f tp] ->
  SetF f tp
fromList es = SetF $ S.fromList (List.map AsOrd es)

member ::
  OrdF f =>
  f tp ->
  SetF f tp ->
  Bool
member e (SetF es) = S.member (AsOrd e) es

size ::
  SetF f tp -> Int
size (SetF es) = S.size es

union :: OrdF f =>
  SetF f tp -> SetF f tp -> SetF f tp
union (SetF a) (SetF b) = SetF (S.union a b)

unions ::
  (Foldable t, OrdF f) => t (SetF f tp) -> SetF f tp
unions = Foldable.foldl' union empty

filter ::
  (f tp -> Bool) -> SetF f tp -> SetF f tp
filter f (SetF es) = SetF $ S.filter (f . unAsOrd) es

lookupMin ::
  SetF f tp -> Maybe (f tp)
lookupMin (SetF es) = fmap unAsOrd $ S.lookupMin es

null ::
  SetF f tp -> Bool
null (SetF es) = S.null es

-- | Convert a 'SetF' to a 'Set', under the assumption
--   that the 'OrdF' and 'Ord' instances are consistent.
--   This uses coercion rather than re-building the set,
--   which is sound given the above assumption.
toSet ::
  (OrdF f, Ord (f tp)) => SetF f tp -> Set (f tp)
toSet (SetF s) = unsafeCoerce s

-- | Convert a 'Set' to a 'SetF', under the assumption
--   that the 'OrdF' and 'Ord' instances are consistent.
--   This uses coercion rather than re-building the set,
--   which is sound given the above assumption.
fromSet :: (OrdF f, Ord (f tp)) => Set (f tp) -> SetF f tp
fromSet s = SetF (unsafeCoerce s)

asSet ::
  (OrdF f, Ord (f tp)) =>
  L.Lens' (SetF f tp) (Set (f tp))
asSet f sf = fmap fromSet (f (toSet sf))

map ::
  (OrdF g) => (f tp -> g tp) -> SetF f tp -> SetF g tp
map f (SetF s) = SetF (S.map (\(AsOrd v) -> AsOrd (f v)) s)  

ppSetF ::
  (f tp -> PP.Doc a) ->
  SetF f tp ->
  PP.Doc a
ppSetF ppElem es =
  let ps = [ ppElem p | p <- toList es ]
  in PP.sep (zipWith (<+>) ("{" : repeat ",") ps) <+> "}"

instance PP.Pretty (a tp) => PP.Pretty (SetF a tp) where
  pretty s = ppSetF PP.pretty s
