{-|
Module           : Data.Quant
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

A container that is used to conveniently define datatypes that
are generalized over concrete, existential and universal quantification.

-}


{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures #-}

module Data.Quant
  ( 
     Quant(..)
    , pattern QuantSome
    , toQuantExists
  ) where

import Data.Kind (Type)
import Data.Functor.Const
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import Data.Parameterized.Some
import qualified Data.Parameterized.TotalMapF as TMF
import           Data.Parameterized.TotalMapF ( TotalMapF, HasTotalMapF )

-- | Wraps the kind 'k' with additional cases for existential and
--   universal quantification
data QuantK k = OneK k | ExistsK | AllK


-- | Similar to 'KnownRepr' and 'IsRepr' but defines a specific type 'ReprOf' that serves as the runtime representation of
--   the type parameter for values of type 'f k'
class (HasTotalMapF (ReprOf :: k -> Type), TestEquality (ReprOf :: k -> Type), OrdF (ReprOf :: k -> Type)) => HasReprK k where
    type ReprOf :: k -> Type
    
-- we need this so that quantification is necessarily bounded in order to meaningfully compare universally quantified values
allReprs :: forall k. HasReprK k => TotalMapF (ReprOf :: k -> Type)  (Const ())
allReprs = TMF.totalMapRepr @(ReprOf :: k -> Type) 

-- | Wraps a kind 'k -> Type' to represent the following possible cases:
--     * a single value of type 'f k' (i.e. f x ~ Quant f (OneK x))
--     * all possible values of type 'f k' (i.e. (forall k. f k) ~ Quant f AllK)
--     * existentially quantified over the above two cases (i.e. Some f ~ Quant f ExistsK ~ Some (Quant f))
--   By universally quantifying types and functions over 'Quant k' we can implicitly handle all 3 of the
--   above cases, rather than requiring individual implementations for each.
data Quant (f :: k0 -> Type) (tp :: QuantK k0) where
    QuantOne :: ReprOf k -> f k -> Quant f (OneK k)
    -- ^ a single value of type 'f k'
    QuantAll :: TotalMapF ReprOf f -> Quant f AllK

    -- the above two cases, but existentially wrapped
    QuantExists :: Quant f (OneK k) -> Quant f ExistsK
    QuantAny :: Quant f AllK -> Quant f ExistsK

-- Drop the type information from a 'Quant' by making it existential instead.
toQuantExists :: Quant f tp1 -> Quant f ExistsK
toQuantExists x = case x of
    QuantOne{} -> QuantExists x
    QuantAll{} -> QuantAny x
    QuantExists y -> toQuantExists y
    QuantAny y -> toQuantExists y


fromQuantSome :: Quant f tp -> Maybe (tp :~: ExistsK, Some (Quant f))
fromQuantSome x = case x of
    QuantExists y -> Just (Refl,Some y)
    QuantAny y -> Just (Refl,Some y)
    _ -> Nothing

-- in most cases we don't care about which 'Quant' was used to form an existential,
-- so this pattern lets us treat them uniformly
pattern QuantSome :: () => (tp2 ~ ExistsK) => Quant f tp1 -> Quant f tp2
pattern QuantSome x <- (fromQuantSome -> Just (Refl, Some x))
    where
        QuantSome x = toQuantExists x

{-# COMPLETE QuantOne, QuantAll, QuantSome #-}

instance FunctorFC Quant where
    fmapFC f = \case
        QuantOne repr x -> QuantOne repr (f x)
        QuantAll g -> QuantAll (fmapF f g)
        QuantSome x -> QuantSome (fmapFC f x)

instance forall k. HasReprK k => FoldableFC (Quant :: (k -> Type) -> QuantK k -> Type) where
    foldrFC f b = \case
        QuantOne _ x -> f x b
        QuantAll g -> foldrF f b g
        QuantSome x -> foldrFC f b x

instance forall k. HasReprK k => TraversableFC (Quant :: (k -> Type) -> QuantK k -> Type) where
    traverseFC f = \case
        QuantOne repr x -> QuantOne <$> pure repr <*> f x
        QuantAll g -> QuantAll <$> traverseF f g
        QuantSome x -> QuantSome <$> traverseFC f x

quantToRepr :: Quant f tp -> QuantRepr tp
quantToRepr = \case
    QuantOne baserepr _ -> QuantOne baserepr (Const ())
    QuantAll tm -> QuantAll (fmapF (\_ -> Const()) tm)
    QuantSome x -> QuantSome (quantToRepr x)

type QuantRepr = Quant (Const ())

instance forall k f. (HasReprK k, (forall x. Ord (f x))) => TestEquality (Quant (f :: k -> Type)) where
    testEquality repr1 repr2 = case (repr1, repr2) of
        (QuantOne baserepr1 x1, QuantOne baserepr2 x2) -> case testEquality baserepr1 baserepr2 of
            Just Refl | x1 == x2 -> Just Refl
            _ -> Nothing
        (QuantAll g1, QuantAll g2) -> case g1 == g2 of
            True -> Just Refl
            False -> Nothing
        (QuantExists x1, QuantExists x2) -> case testEquality x1 x2 of
            Just Refl -> Just Refl
            Nothing -> Nothing
        (QuantAny x1, QuantAny x2) ->  case testEquality x1 x2 of
            Just Refl -> Just Refl
            Nothing -> Nothing
        _ -> Nothing


instance forall k f. (HasReprK k, (forall x. Ord (f x))) => OrdF (Quant (f :: k -> Type)) where
    compareF repr1 repr2 = case (repr1, repr2) of
        (QuantOne baserepr1 x1, QuantOne baserepr2 x2) -> lexCompareF baserepr1 baserepr2 $ fromOrdering (compare x1 x2)
        (QuantAll g1, QuantAll g2) -> fromOrdering (compare g1 g2)
        (QuantExists x1, QuantExists x2) -> case compareF x1 x2 of
            LTF -> LTF
            GTF -> GTF
            EQF -> EQF
        (QuantAny x1, QuantAny x2) -> case compareF x1 x2 of
            LTF -> LTF
            GTF -> GTF
            EQF -> EQF

        -- based on constructor ordering
        (QuantOne{}, QuantAll{}) -> LTF
        (QuantOne{}, QuantExists{}) -> LTF
        (QuantOne{}, QuantAny{}) -> LTF

        (QuantAll{}, QuantOne{}) -> GTF
        (QuantAll{}, QuantExists{}) -> LTF
        (QuantAll{}, QuantAny{}) -> LTF

        (QuantExists{}, QuantOne{}) -> GTF
        (QuantExists{}, QuantAll{}) -> GTF
        (QuantExists{}, QuantAny{}) -> LTF

        (QuantAny{}, QuantOne{}) -> GTF
        (QuantAny{}, QuantAll{}) -> GTF
        (QuantAny{}, QuantExists{}) -> GTF

-- Defining which conversions are always possible
class ToQuant f (t1 :: QuantK k) (t2 :: QuantK k) where
    toQuant :: f t1 -> QuantRepr t2 -> f t2

-- Can take a universally quantified variant to any variant
instance HasReprK k => ToQuant (Quant f) AllK (tp :: QuantK k) where
    toQuant z@(QuantAll f) repr = case repr of
        QuantOne baserepr _ -> QuantOne baserepr (TMF.apply f baserepr)
        QuantAll _ -> QuantAll f
        QuantSome{} -> QuantSome z

-- Can take any variant to an existentially quantified variant
instance ToQuant (Quant f) (tp :: QuantK k) ExistsK where
    toQuant z _ = case z of
        QuantSome{} -> z
        _ -> QuantSome z

-- Can always take a variant to the same kind
instance ToQuant f (OneK k1) (OneK k1) where 
    toQuant x _ = x


class ToMaybeQuant f (t1 :: QuantK k) (t2 :: QuantK k) where
    toMaybeQuant :: f t1 -> QuantRepr t2 -> Maybe (f t2)

instance HasReprK k => ToMaybeQuant (Quant f) (tp1 :: QuantK k) (tp2 :: QuantK k) where
    toMaybeQuant x repr = case (x, repr) of
        (QuantAll{}, _) -> Just (toQuant x repr)
        (_, QuantSome{}) -> Just (toQuant x repr)
        (QuantOne baseX x', QuantOne baseY _) -> case testEquality baseX baseY of
            Just Refl -> Just $ QuantOne baseX x'
            -- by definition we can't convert between base types
            Nothing -> Nothing
        (QuantSome x', _) -> toMaybeQuant x' repr
        -- by definition a base type cannot be turned into a universal quantifier
        (QuantOne{}, QuantAll{}) -> Nothing