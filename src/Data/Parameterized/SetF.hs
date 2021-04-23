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

module Data.Parameterized.SetF
  ( SetF
  , singleton
  , toList
  , fromList
  , member
  , size
  ) where

import           Data.Parameterized.Classes

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


singleton ::
  OrdF f =>
  f tp ->
  SetF f tp
singleton e = SetF (S.singleton (AsOrd e))

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
