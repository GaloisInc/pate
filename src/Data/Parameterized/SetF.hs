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
  , ppSetF
  ) where

import Prelude hiding (filter, null)
import           Data.Parameterized.Classes
import qualified Data.Foldable as Foldable

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import           Data.Set (Set)
import qualified Data.Set as S

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
toList (SetF es) = map unAsOrd $ S.toList es

fromList ::
  OrdF f =>
  [f tp] ->
  SetF f tp
fromList es = SetF $ S.fromList (map AsOrd es)

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

ppSetF ::
  (f tp -> PP.Doc a) ->
  SetF f tp ->
  PP.Doc a
ppSetF ppElem es =
  let ps = [ ppElem p | p <- toList es ]
  in PP.sep (zipWith (<+>) ("{" : repeat ",") ps) <+> "}"

instance PP.Pretty (a tp) => PP.Pretty (SetF a tp) where
  pretty s = ppSetF PP.pretty s
