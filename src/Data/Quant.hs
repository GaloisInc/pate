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
    , type QuantK
    , type OneK
    , type ExistsK
    , type AllK
    , map
    , traverse
    , mapWithRepr
    , traverseWithRepr
    , pattern QuantSome
    , toQuantExists
    , quantToRepr
    , QuantRepr(..)
    , QuantConversion(..)
    , QuantConvertible(..)
    , QuantCoercion(..)
    , QuantCoercible(..)
    , HasReprK(..)
    , pattern QuantToOne
    , generateAll
    , generateAllM
    , pattern All
    , pattern Single
    , quantEach
    , QuantEach
    , pattern QuantEach
    , AsSingle(..)
  ) where

import           Prelude hiding (map, traverse)

import           Data.Kind (Type)
import           Data.Constraint

import Data.Functor.Const
import Data.Proxy
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import Data.Parameterized.Some
import qualified Data.Parameterized.TotalMapF as TMF
import           Data.Parameterized.TotalMapF ( TotalMapF, HasTotalMapF )
import           Data.Parameterized.WithRepr

-- | Wraps the kind 'k' with additional cases for existential and
--   universal quantification
data QuantK k = OneK k | ExistsK | AllK

type OneK = 'OneK
type ExistsK = 'ExistsK
type AllK = 'AllK

type KnownHasRepr (k0 :: k) = KnownRepr (ReprOf :: k -> Type) k0

-- | Similar to 'KnownRepr' and 'IsRepr' but defines a specific type 'ReprOf' that serves as the runtime representation of
--   the type parameter for values of type 'f k'
class (HasTotalMapF (ReprOf :: k -> Type), TestEquality (ReprOf :: k -> Type), OrdF (ReprOf :: k -> Type), IsRepr (ReprOf :: k -> Type)) => HasReprK k where
    type ReprOf :: k -> Type

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

generateAll :: HasReprK k => (forall (x :: k). ReprOf x -> f x) -> Quant f AllK
generateAll f = QuantAll $ TMF.mapWithKey (\k _ -> f k) allReprs

generateAllM :: (HasReprK k, Applicative m) => (forall (x :: k). ReprOf x -> m (f x)) -> m (Quant f AllK)
generateAllM f = QuantAll <$> TMF.traverseWithKey (\k _ -> f k) allReprs

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

-- | A more convenient interface for handling existential cases, which
--   doesn't distinguish between universal or concrete for the wrapped
--   Quant.
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

map :: (forall x. f x -> g x) -> Quant f tp -> Quant g tp
map = fmapFC

mapWithRepr :: (forall (x :: k). ReprOf x -> f x -> g x) -> Quant f tp -> Quant g tp
mapWithRepr f = \case
    QuantOne repr x -> QuantOne repr $ f repr x
    QuantAll tm -> QuantAll $ TMF.mapWithKey f tm
    QuantSome x -> QuantSome $ mapWithRepr f x

traverse :: (HasReprK k, Applicative m) => (forall (x :: k). f x -> m (g x)) -> Quant f tp -> m (Quant g tp)
traverse = traverseFC

traverseWithRepr :: (HasReprK k, Applicative m) => (forall (x :: k). ReprOf x -> f x -> m (g x)) -> Quant f tp -> m (Quant g tp)
traverseWithRepr f = \case
    QuantOne repr x -> QuantOne <$> pure repr <*> f repr x
    QuantAll tm -> QuantAll <$> TMF.traverseWithKey f tm
    QuantSome x -> QuantSome <$> traverseWithRepr f x

quantToRepr :: Quant f tp -> QuantRepr tp
quantToRepr = \case
    QuantOne baserepr _ -> QuantOneRepr baserepr
    QuantAll{} -> QuantAllRepr
    QuantSome{} -> QuantSomeRepr

data QuantRepr (tp :: QuantK k0) where
    QuantOneRepr :: ReprOf k -> QuantRepr (OneK k)
    QuantAllRepr :: QuantRepr AllK
    QuantSomeRepr :: QuantRepr ExistsK

instance KnownHasRepr x => KnownRepr (QuantRepr :: QuantK k0 -> Type) (OneK (x :: k0)) where
    knownRepr = QuantOneRepr knownRepr

instance KnownRepr QuantRepr AllK where
    knownRepr = QuantAllRepr

instance KnownRepr QuantRepr ExistsK where
    knownRepr = QuantSomeRepr

instance IsRepr (ReprOf :: k -> Type) => IsRepr (QuantRepr :: QuantK k -> Type)

instance forall k. (HasReprK k) => TestEquality (QuantRepr :: QuantK k -> Type) where
    testEquality (QuantOneRepr r1) (QuantOneRepr r2) = case testEquality r1 r2 of
        Just Refl -> Just Refl
        Nothing -> Nothing
    testEquality QuantAllRepr QuantAllRepr = Just Refl
    testEquality QuantSomeRepr QuantSomeRepr = Just Refl
    testEquality _ _ = Nothing

instance forall k. (HasReprK k) => OrdF (QuantRepr :: QuantK k -> Type) where
    compareF (QuantOneRepr r1) (QuantOneRepr r2) = case compareF r1 r2 of
        EQF -> EQF
        LTF -> LTF
        GTF -> GTF
    compareF QuantAllRepr QuantAllRepr = EQF
    compareF QuantSomeRepr QuantSomeRepr = EQF

    compareF (QuantOneRepr{}) QuantAllRepr = LTF
    compareF (QuantOneRepr{}) QuantSomeRepr = LTF

    compareF QuantAllRepr (QuantOneRepr{}) = GTF
    compareF QuantAllRepr QuantSomeRepr = LTF

    compareF QuantSomeRepr (QuantOneRepr{}) = GTF
    compareF QuantSomeRepr QuantAllRepr = GTF

instance forall k f. (HasReprK k, (forall x. Eq (f x))) => TestEquality (Quant (f :: k -> Type)) where
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

instance (HasReprK k, forall x. Eq (f x)) => Eq (Quant (f :: k -> Type) tp) where
    q1 == q2 = case testEquality q1 q2 of
        Just Refl -> True
        Nothing -> False

instance (HasReprK k, forall x. Ord (f x)) => Ord (Quant (f :: k -> Type) tp) where
    compare q1 q2 = toOrdering $ compareF q1 q2

data QuantCoercion (t1 :: QuantK k) (t2 :: QuantK k) where
    CoerceAllToOne :: ReprOf x -> QuantCoercion AllK (OneK x)
    CoerceAllToExists :: QuantCoercion AllK ExistsK
    CoerceOneToExists :: QuantCoercion (OneK x) ExistsK
    CoerceRefl :: QuantCoercion x x

class QuantCoercible (f :: QuantK k -> Type)  where
    applyQuantCoercion :: forall t1 t2. HasReprK k => QuantCoercion t1 t2 -> f t1 -> f t2
    applyQuantCoercion qc f1 = withRepr qc $ coerceQuant f1

    coerceQuant :: forall t1 t2. (HasReprK k, KnownCoercion t1 t2) => f t1 -> f t2
    coerceQuant = applyQuantCoercion knownRepr

instance HasReprK k => IsRepr (QuantCoercion (t1 :: QuantK k)) where
    withRepr x f = case x of
        CoerceAllToOne repr -> withRepr repr $ f
        CoerceAllToExists -> f
        CoerceOneToExists -> f
        CoerceRefl -> f

instance QuantCoercible (Quant (f :: k -> Type)) where
    applyQuantCoercion qc q = case (qc, q) of
        (CoerceAllToOne repr, QuantAll f) -> QuantOne repr (TMF.apply f repr)
        (CoerceAllToExists, QuantAll{}) -> QuantAny q
        (CoerceOneToExists, QuantOne{}) -> QuantExists q
        (CoerceRefl, _) -> q

type KnownCoercion (tp1 :: QuantK k) (tp2 :: QuantK k) = KnownRepr (QuantCoercion tp1) tp2


instance (KnownRepr (ReprOf :: k -> Type) (x :: k)) => KnownRepr (QuantCoercion AllK) (OneK x) where
    knownRepr = CoerceAllToOne knownRepr

instance KnownRepr (QuantCoercion AllK) ExistsK where
    knownRepr = CoerceAllToExists

instance KnownRepr (QuantCoercion (OneK x)) ExistsK where
    knownRepr = CoerceOneToExists

instance KnownRepr (QuantCoercion x) x where
    knownRepr = CoerceRefl


data QuantConversion (t1 :: QuantK k) (t2 :: QuantK k) where
    ConvertWithCoerce :: QuantCoercion t1 t2 -> QuantConversion t1 t2
    ConvertExistsToAll :: QuantConversion ExistsK AllK
    ConvertExistsToOne :: ReprOf x -> QuantConversion ExistsK (OneK x)

instance HasReprK k => IsRepr (QuantConversion (t1 :: QuantK k)) where
    withRepr x f = case x of
        ConvertWithCoerce y -> case y of
            CoerceAllToOne repr -> withRepr repr $ f
            CoerceAllToExists -> f
            CoerceOneToExists -> f
            CoerceRefl -> f
        ConvertExistsToAll -> f
        ConvertExistsToOne repr -> withRepr repr $ f

class QuantConvertible (f :: QuantK k -> Type)  where
    applyQuantConversion :: forall t1 t2. HasReprK k => QuantConversion t1 t2 -> f t1 -> Maybe (f t2)
    applyQuantConversion qc f1 = withRepr qc $ convertQuant f1

    convertQuant :: forall t1 t2. (HasReprK k, KnownConversion t1 t2) => f t1 -> Maybe (f t2)
    convertQuant = applyQuantConversion knownRepr

type KnownConversion (tp1 :: QuantK k) (tp2 :: QuantK k) = KnownRepr (QuantConversion tp1) tp2

instance (KnownRepr (ReprOf :: k -> Type) (x :: k)) => KnownRepr (QuantConversion AllK) (OneK x) where
    knownRepr = ConvertWithCoerce knownRepr

instance KnownRepr (QuantConversion AllK) ExistsK where
    knownRepr = ConvertWithCoerce knownRepr

instance KnownRepr (QuantConversion (OneK x)) ExistsK where
    knownRepr = ConvertWithCoerce knownRepr

instance KnownRepr (QuantConversion x) x where
    knownRepr = ConvertWithCoerce knownRepr

instance KnownRepr (QuantConversion ExistsK) AllK where
    knownRepr = ConvertExistsToAll

instance (KnownRepr (ReprOf :: k -> Type) (x :: k)) => KnownRepr (QuantConversion ExistsK) (OneK x) where
    knownRepr = ConvertExistsToOne knownRepr


instance QuantConvertible (Quant (f :: k -> Type)) where
    applyQuantConversion qc q = case (qc, q) of
        (ConvertWithCoerce qc', _) -> Just (applyQuantCoercion qc' q)
        (ConvertExistsToAll, QuantAny q') -> Just q'
        (ConvertExistsToAll, QuantExists{}) -> Nothing
        (ConvertExistsToOne repr, QuantAny q') -> Just (applyQuantCoercion (CoerceAllToOne repr) q')
        (ConvertExistsToOne repr, QuantExists q'@(QuantOne repr' _)) -> case testEquality repr repr' of
            Just Refl -> Just q'
            Nothing -> Nothing

type family TheOneK (tp :: QuantK k) :: k where
    TheOneK (OneK k) = k

type family IfIsOneK (tp :: QuantK k) (c :: Constraint) :: Constraint where
    IfIsOneK (OneK k) c = c
    IfIsOneK AllK c = ()
    IfIsOneK ExistsK c = ()

asQuantOne :: forall k (x :: k) f tp. HasReprK k => ReprOf x -> Quant (f :: k -> Type) (tp :: QuantK k) -> Maybe (Dict (KnownRepr QuantRepr tp), Dict (IfIsOneK tp (x ~ TheOneK tp)), ReprOf x, f x)
asQuantOne repr = \case
    QuantOne repr' f | Just Refl <- testEquality repr' repr -> Just (withRepr (QuantOneRepr repr') $ Dict, Dict, repr, f)
    QuantOne{} -> Nothing
    QuantAll tm -> Just (Dict, Dict, repr, TMF.apply tm repr)
    QuantExists x -> case asQuantOne repr x of
        Just (Dict, _, _, x') -> Just (Dict, Dict, repr, x')
        Nothing -> Nothing
    QuantAny (QuantAll f) -> Just (Dict, Dict, repr, TMF.apply f repr)

-- | Cast a 'Quant' to a specific instance of 'x' if it contains it. Pattern match failure otherwise.
pattern QuantToOne :: forall {k} x f tp. (KnownHasRepr (x :: k), HasReprK k) => ( KnownRepr QuantRepr tp, IfIsOneK tp (x ~ TheOneK tp)) => f x -> Quant f tp
pattern QuantToOne fx <- (asQuantOne (knownRepr :: ReprOf x) -> Just (Dict, Dict, _, fx))


data ExistsOrCases (tp1 :: QuantK k) (tp2 :: QuantK k) where
    ExistsOrRefl :: ExistsOrCases tp tp
    ExistsOrExists :: ExistsOrCases ExistsK tp

type family IsExistsOrConstraint (tp1 :: QuantK k) (tp2 :: QuantK k) :: Constraint

class IsExistsOrConstraint tp1 tp2 => IsExistsOr (tp1 :: QuantK k) (tp2 :: QuantK k) where
    isExistsOr :: ExistsOrCases tp1 tp2
    
type instance IsExistsOrConstraint (OneK x) tp = ((OneK x) ~ tp)
type instance IsExistsOrConstraint (AllK :: QuantK k) tp = ((AllK :: QuantK k) ~ tp)

instance IsExistsOr (OneK x) (OneK x) where
    isExistsOr = ExistsOrRefl

instance IsExistsOr AllK AllK where
    isExistsOr = ExistsOrRefl

instance IsExistsOr ExistsK ExistsK where
    isExistsOr = ExistsOrRefl

type instance IsExistsOrConstraint ExistsK x = ()

instance IsExistsOr ExistsK (OneK k) where
    isExistsOr = ExistsOrExists

instance IsExistsOr ExistsK AllK where
    isExistsOr = ExistsOrExists

data QuantAsAllProof (f :: k -> Type) (tp :: QuantK k) where
    QuantAsAllProof :: (IsExistsOr tp AllK) => (forall x. ReprOf x -> f x) -> QuantAsAllProof f tp

quantAsAll :: HasReprK k => Quant (f :: k -> Type) tp -> Maybe (QuantAsAllProof f tp)
quantAsAll q = case q of
    QuantOne{} -> Nothing
    QuantAll f -> Just (QuantAsAllProof (TMF.apply f))
    QuantSome q' -> case quantAsAll q' of
        Just (QuantAsAllProof f) -> Just $ QuantAsAllProof f
        Nothing -> Nothing

-- | Pattern for creating or matching a universally quantified 'Quant', generalized over the existential cases
pattern All :: forall {k} f tp. (HasReprK k) => (IsExistsOr tp AllK) => (forall x. ReprOf x -> f x) -> Quant (f :: k -> Type) tp
pattern All f <- (quantAsAll -> Just (QuantAsAllProof f))
    where
        All f = case (isExistsOr :: ExistsOrCases tp AllK) of
            ExistsOrExists -> QuantAny (All f)
            ExistsOrRefl -> QuantAll (TMF.mapWithKey (\repr _ -> f repr) (allReprs @k))

data QuantAsOneProof (f :: k -> Type) (tp :: QuantK k) where
    QuantAsOneProof :: (IsExistsOr tp (OneK x), IfIsOneK tp (x ~ TheOneK tp)) => ReprOf x -> f x -> QuantAsOneProof f tp

quantAsOne :: forall k f tp. HasReprK k => Quant (f :: k -> Type) (tp :: QuantK k) -> Maybe (QuantAsOneProof f tp)
quantAsOne q = case q of
    QuantOne repr x-> withRepr repr $ Just (QuantAsOneProof repr x)
    QuantExists q' -> case quantAsOne q' of
        Just (QuantAsOneProof repr x) -> Just $ QuantAsOneProof repr x
        Nothing -> Nothing
    _ -> Nothing

existsOrCases :: forall tp tp' a. IsExistsOr tp tp' => (tp ~ ExistsK => a) ->  (tp ~ tp' => a) ->  a
existsOrCases f g = case (isExistsOr :: ExistsOrCases tp tp') of
    ExistsOrExists -> f
    ExistsOrRefl -> g

-- | Pattern for creating or matching a singleton 'Quant', generalized over the existential cases
pattern Single :: forall {k} f tp. (HasReprK k) => forall x. (IsExistsOr tp (OneK x), IfIsOneK tp (x ~ TheOneK tp)) => ReprOf x -> f x -> Quant (f :: k -> Type) tp
pattern Single repr x <- (quantAsOne -> Just (QuantAsOneProof repr x))
    where
        Single (repr :: ReprOf x) x = existsOrCases @tp @(OneK x) (QuantExists (Single repr x)) (QuantOne repr x)


{-# COMPLETE Single, All #-}
{-# COMPLETE Single, QuantAll, QuantAny #-}
{-# COMPLETE Single, QuantAll, QuantSome #-}

{-# COMPLETE All, QuantOne, QuantExists #-}
{-# COMPLETE All, QuantOne, QuantSome #-}

newtype AsSingle (f :: QuantK k -> Type) (y :: k) where
    AsSingle :: f (OneK y) -> AsSingle f y

deriving instance Eq (f (OneK x)) => Eq ((AsSingle f) x)
deriving instance Ord (f (OneK x)) => Ord ((AsSingle f) x)
deriving instance Show (f (OneK x)) => Show ((AsSingle f) x)

instance TestEquality f => TestEquality (AsSingle f) where
    testEquality (AsSingle x) (AsSingle y) = case testEquality x y of
        Just Refl -> Just Refl
        Nothing -> Nothing

instance OrdF f => OrdF (AsSingle f) where
    compareF (AsSingle x) (AsSingle y) = case compareF x y of
        EQF -> EQF
        LTF -> LTF
        GTF -> GTF

instance forall f. ShowF f => ShowF (AsSingle f) where
    showF (AsSingle x) = showF x
    withShow _ (_ :: q tp) f = withShow (Proxy :: Proxy f) (Proxy :: Proxy (OneK tp)) f

type QuantEach (f :: QuantK k -> Type) = Quant (AsSingle f) AllK

quantEach :: HasReprK k => QuantEach f -> (forall (x :: k). ReprOf x -> f (OneK x))
quantEach (QuantAll f) = \r -> case TMF.apply f r of AsSingle x -> x

viewQuantEach' :: HasReprK k => Quant (AsSingle f) tp -> Maybe (Dict (IsExistsOr tp AllK), forall (x :: k). ReprOf x -> f (OneK x))
viewQuantEach' q = case q of
    QuantOne{} -> Nothing
    QuantAll f -> Just (Dict, \r -> case TMF.apply f r of AsSingle x -> x)
    QuantSome q' -> case viewQuantEach' q' of
        Just (Dict, g) -> Just (Dict, g)
        Nothing -> Nothing

pattern QuantEach :: forall {k} f tp. (HasReprK k) => (IsExistsOr tp AllK) => (forall (x :: k). ReprOf x -> f (OneK x)) -> Quant (AsSingle f) tp
pattern QuantEach f <- (viewQuantEach' -> Just (Dict, f))
    where
        QuantEach f = existsOrCases @tp @AllK (QuantAny (QuantEach f)) (QuantAll (TMF.mapWithKey (\r _ -> AsSingle (f r)) (allReprs @k)))

{-# COMPLETE QuantEach, Single #-}

_testQuantEach :: forall {k} f tp. HasReprK k => Quant (AsSingle (f :: QuantK k -> Type)) tp -> ()
_testQuantEach = \case
    QuantEach (_f :: forall (x :: k). ReprOf x -> f (OneK x)) -> ()
    Single (_repr :: ReprOf (x :: k)) (AsSingle (_x :: f (OneK x))) -> ()

_testQuantEach1 :: HasReprK k => Quant (AsSingle (f :: QuantK k -> Type)) AllK -> ()
_testQuantEach1 = \case
    QuantEach (_f :: forall (x :: k). ReprOf x -> f (OneK x)) -> ()
    -- complete match, since Single has an unsolvable constraint