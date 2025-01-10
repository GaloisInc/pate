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
{-# LANGUAGE TypeFamilyDependencies #-}

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
    , toSingleQuant
    , pattern SomeSingle
    , coerceToExists
    , KnownConversion
    , KnownCoercion
    , pattern CoerceToExists
    , Exists
    , pattern Exists
    , pattern ExistsOne
    , pattern ExistsAll
    , IsExistsOr(..)
    , ExistsOrCases(..)
    , TheOneK
    , IfIsOneK
    , IfIsOneKElse
    , NotAllK
    , coerceExists
  ) where

import           Prelude hiding (map, traverse)
import           GHC.TypeLits (TypeError, ErrorMessage(..))

import           Data.Kind (Type)
import           Data.Constraint
import qualified Data.List as List

import Data.Functor.Const
import Data.Proxy
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import Data.Parameterized.Some
import qualified Data.Parameterized.TotalMapF as TMF
import           Data.Parameterized.TotalMapF ( TotalMapF, HasTotalMapF )
import           Data.Parameterized.WithRepr
import qualified Data.Parameterized.Map as MapF

-- | Wraps the kind 'k' with additional cases for existential and
--   universal quantification
data QuantK k = OneK k | ExistsK | AllK

type OneK = 'OneK
type ExistsK = 'ExistsK
type AllK = 'AllK

type family QuantKCases (tp :: QuantK k) (caseOne :: l) (caseExists :: l) (caseAll :: l) :: l where
    QuantKCases (OneK _) k _ _ = k
    QuantKCases AllK _ _ k = k
    QuantKCases ExistsK _ k _ = k


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
    CoerceOneToExists :: ReprOf x -> QuantCoercion (OneK x) ExistsK
    CoerceRefl :: QuantRepr x -> QuantCoercion x x


pattern CoerceToExists :: forall t1 t2. () => (t2 ~ ExistsK) => QuantRepr t1 -> QuantCoercion t1 t2
pattern CoerceToExists repr <- 
  ((\l -> case l of 
    CoerceAllToExists -> Just (QuantAllRepr, Refl)
    CoerceOneToExists repr -> Just (QuantOneRepr repr, Refl)
    CoerceRefl QuantSomeRepr -> Just (QuantSomeRepr, Refl)
    _ -> Nothing) 
      -> Just (repr :: QuantRepr t1, Refl :: t2 :~: ExistsK))

{-# COMPLETE CoerceAllToOne, CoerceAllToExists, CoerceOneToExists, CoerceRefl #-}
{-# COMPLETE CoerceAllToOne, CoerceToExists, CoerceRefl #-}

class QuantCoercible (f :: QuantK k -> Type)  where
    applyQuantCoercion :: forall t1 t2. HasReprK k => QuantCoercion t1 t2 -> f t1 -> f t2
    applyQuantCoercion qc f1 = withRepr qc $ coerceQuant f1

    coerceQuant :: forall t1 t2. (HasReprK k, KnownCoercion t1 t2) => f t1 -> f t2
    coerceQuant = applyQuantCoercion knownRepr

coerceToExists :: forall {k} f (tp :: QuantK k). (HasReprK k, QuantCoercible f, KnownRepr QuantRepr tp) => f tp -> f ExistsK
coerceToExists x = case knownRepr :: QuantRepr tp of
  QuantOneRepr repr -> applyQuantCoercion (CoerceOneToExists repr) x
  QuantAllRepr -> applyQuantCoercion CoerceAllToExists x
  QuantSomeRepr -> x

instance HasReprK k => IsRepr (QuantCoercion (t1 :: QuantK k)) where
    withRepr x f = case x of
        CoerceAllToOne repr -> withRepr repr $ f
        CoerceAllToExists -> f
        CoerceOneToExists repr -> withRepr repr $ f
        CoerceRefl qrepr -> withRepr qrepr $ f

instance QuantCoercible (Quant (f :: k -> Type)) where
    applyQuantCoercion qc q = case (qc, q) of
        (CoerceAllToOne repr, QuantAll f) -> QuantOne repr (TMF.apply f repr)
        (CoerceAllToExists, QuantAll{}) -> QuantAny q
        (CoerceOneToExists{}, QuantOne{}) -> QuantExists q
        (CoerceRefl{}, _) -> q

type KnownCoercion (tp1 :: QuantK k) (tp2 :: QuantK k) = KnownRepr (QuantCoercion tp1) tp2


instance (KnownRepr (ReprOf :: k -> Type) (x :: k)) => KnownRepr (QuantCoercion AllK) (OneK x) where
    knownRepr = CoerceAllToOne knownRepr

instance KnownRepr (QuantCoercion AllK) ExistsK where
    knownRepr = CoerceAllToExists

instance KnownRepr ReprOf x => KnownRepr (QuantCoercion (OneK x)) ExistsK where
    knownRepr = CoerceOneToExists knownRepr

instance KnownRepr QuantRepr tp => KnownRepr (QuantCoercion tp) tp where
    knownRepr = CoerceRefl knownRepr

data QuantConversion (t1 :: QuantK k) (t2 :: QuantK k) where
    ConvertRefl :: ReprOf x -> QuantConversion x x
    ConvertNone :: ReprOf x -> ReprOf y -> QuantConversion x y
    ConvertExistsToAll :: QuantConversion ExistsK AllK
    ConvertExistsToOne :: ReprOf x -> QuantConversion ExistsK (OneK x)

instance HasReprK k => IsRepr (QuantConversion (t1 :: QuantK k)) where
    withRepr x f = case x of
        ConvertRefl repr -> withRepr repr $ f
        ConvertNone repr1 repr2 -> withRepr repr1 $ withRepr repr2 $ f
        ConvertExistsToAll -> f
        ConvertExistsToOne repr -> withRepr repr $ f

class QuantConvertible (f :: QuantK k -> Type)  where
    applyQuantConversion :: forall t1 t2. HasReprK k => QuantConversion t1 t2 -> f t1 -> Maybe (f t2)
    applyQuantConversion qc f1 = withRepr qc $ convertQuant f1

    convertQuant :: forall t1 t2. (HasReprK k, KnownConversion t1 t2) => f t1 -> Maybe (f t2)
    convertQuant = applyQuantConversion knownRepr

findFirst :: (a -> Maybe b) -> [a] -> Maybe b
findFirst _ [] = Nothing
findFirst f (x:xs) = case f x of
    Just y -> Just y
    Nothing -> findFirst f xs

data MaybeF f tp = JustF (f tp) | NothingF

-- | Project out a 'Quant' of singletons from a given 'f' parameterized by 'QuantK k'.
--   Uses the 'QuantCoercible' and 'QuantConvertible' instances to attempt to coerce/convert
--   'f' into each possible single value.
toSingleQuant :: 
    forall {k} f (tp :: QuantK k). 
    ( HasReprK k
    , QuantCoercible f
    , QuantConvertible f
    , KnownRepr QuantRepr tp) => 
    f tp -> 
    Maybe (Quant (AsSingle f) tp)
toSingleQuant f = case knownRepr :: QuantRepr tp of
  QuantOneRepr repr -> Just $ Single repr (AsSingle f)
  QuantAllRepr -> Just $ All (\r -> AsSingle $ applyQuantCoercion (CoerceAllToOne r) f)
  QuantSomeRepr -> case applyQuantConversion ConvertExistsToAll f of
    Just f' -> QuantAny <$> toSingleQuant f'
    Nothing -> 
      let y = TMF.mapWithKey 
                (\r _ -> case applyQuantConversion (ConvertExistsToOne r) f of 
                  Just x -> JustF (AsSingle x)
                  Nothing -> NothingF)  
                (allReprs :: TMF.TotalMapF (ReprOf :: k -> Type) (Const ()))
      in case TMF.traverseWithKey (\_ -> \case JustF x -> Just x; NothingF -> Nothing) y of
        -- if we can convert to each individual singleton, then we can take all of the results and turn this into a QuantAll
        -- (i.e. likely all of the inner Quants are QuantAny, and so can be converted to any single value)
        Just z -> Just (QuantAny $ QuantAll z)
        -- otherwise we just take the first successful conversion
        Nothing -> findFirst 
          (\(MapF.Pair repr x) -> case x of 
              JustF (AsSingle z) -> Just (QuantExists $ QuantOne repr (AsSingle z))
              NothingF -> Nothing) 
          (TMF.toList y)

data SomeSingle f tp where
  SomeSingleCtor :: (IsExistsOr tp (OneK (TheOneK tp)), IfIsOneK tp (x ~ TheOneK tp)) => ReprOf x -> f (OneK x) -> SomeSingle f tp

toSomeSingle :: HasReprK k => Quant (AsSingle f) (tp :: QuantK k) -> Maybe (SomeSingle f tp)
toSomeSingle = \case
  QuantExists (QuantOne repr (AsSingle x)) -> Just $ SomeSingleCtor repr x 
  QuantOne repr (AsSingle x) -> Just $ SomeSingleCtor repr x
  _ -> Nothing

pattern SomeSingle :: 
    forall {k} (f :: QuantK k -> Type) (tp :: QuantK k).
    ( HasReprK k
    , QuantCoercible f
    , QuantConvertible f
    , KnownRepr QuantRepr tp) => 
    forall (x :: k). (IsExistsOr tp (OneK (TheOneK tp)), IfIsOneK tp (x ~ TheOneK tp)) => 
    ReprOf x ->
    f (OneK x) -> 
    f tp
pattern SomeSingle repr x <- ((\l -> toSingleQuant l >>= toSomeSingle) -> (Just (SomeSingleCtor repr x)))
  where
    SomeSingle repr x = case (isExistsOr :: ExistsOrCases tp (OneK (TheOneK tp))) of
      ExistsOrExists -> withRepr repr $ coerceQuant x
      ExistsOrRefl -> x


type KnownConversion (tp1 :: QuantK k) (tp2 :: QuantK k) = KnownRepr (QuantConversion tp1) tp2

{-
instance KnownRepr (QuantConversion ExistsK) AllK where
    knownRepr = ConvertExistsToAll

instance (KnownRepr (ReprOf :: k -> Type) (x :: k)) => KnownRepr (QuantConversion ExistsK) (OneK x) where
    knownRepr = ConvertExistsToOne knownRepr
-}

instance forall k x1 x2. (HasReprK k, KnownRepr QuantRepr (x1 :: QuantK k), KnownRepr QuantRepr x2) => KnownRepr (QuantConversion x1) x2 where
  knownRepr = case (knownRepr :: QuantRepr x1, knownRepr :: QuantRepr x2) of
    (QuantSomeRepr, QuantAllRepr) -> ConvertExistsToAll
    (QuantSomeRepr, QuantOneRepr repr) -> ConvertExistsToOne repr
    (x, y) | Just Refl <- testEquality x y -> ConvertRefl x
    _ -> ConvertNone knownRepr knownRepr



instance QuantConvertible (Quant (f :: k -> Type)) where
    applyQuantConversion qc q = case (qc, q) of
        (ConvertRefl{}, _) -> Just q
        (ConvertNone{}, _) -> Nothing
        (ConvertExistsToAll, QuantAny q') -> Just q'
        (ConvertExistsToAll, QuantExists{}) -> Nothing
        (ConvertExistsToOne repr, QuantAny q') -> Just (applyQuantCoercion (CoerceAllToOne repr) q')
        (ConvertExistsToOne repr, QuantExists q'@(QuantOne repr' _)) -> case testEquality repr repr' of
            Just Refl -> Just q'
            Nothing -> Nothing

type family TheOneK (tp :: QuantK k) :: k where
    TheOneK (OneK k) = k

type family IfIsOneKElse (tp :: QuantK k) (cT :: Constraint) (cF :: Constraint) :: Constraint where
    IfIsOneKElse (OneK k) cT _ = cT
    IfIsOneKElse AllK _ cF = cF
    IfIsOneKElse ExistsK _ cF = cF

type IfIsOneK tp (c :: Constraint) = QuantKCases tp c (() :: Constraint) (() :: Constraint) 

type NotAllK tp = QuantKCases tp (() :: Constraint) (() :: Constraint) (TypeError ('Text "NotAllK: Cannot match with AllK"))

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

type IsExistsOrConstraint (tp1 :: QuantK k) (tp2 :: QuantK k) = QuantKCases tp1 (tp1 ~ tp2)  (() :: Constraint) (tp1 ~ tp2)

class (IsExistsOr tp1 tp1, IsExistsOr tp2 tp2, IsExistsOrConstraint tp1 tp2) => IsExistsOr (tp1 :: QuantK k) (tp2 :: QuantK k) where
    isExistsOr :: ExistsOrCases tp1 tp2

instance IsExistsOr (OneK x) (OneK x) where
    isExistsOr = ExistsOrRefl

instance IsExistsOr AllK AllK where
    isExistsOr = ExistsOrRefl

instance IsExistsOr ExistsK ExistsK where
    isExistsOr = ExistsOrRefl

instance IsExistsOr ExistsK (OneK k) where
    isExistsOr = ExistsOrExists

instance IsExistsOr ExistsK AllK where
    isExistsOr = ExistsOrExists

data QuantAsAllProof (f :: k -> Type) (tp :: QuantK k) where
    QuantAsAllProof :: (IsExistsOr tp AllK, KnownRepr QuantRepr tp) => (forall x. ReprOf x -> f x) -> QuantAsAllProof f tp

quantAsAll :: HasReprK k => Quant (f :: k -> Type) tp -> Maybe (QuantAsAllProof f tp)
quantAsAll q = case q of
    QuantOne{} -> Nothing
    QuantAll f -> Just (QuantAsAllProof (TMF.apply f))
    QuantSome q' -> case quantAsAll q' of
        Just (QuantAsAllProof f) -> Just $ QuantAsAllProof f
        Nothing -> Nothing

-- | Pattern for creating or matching a universally quantified 'Quant', generalized over the existential cases
pattern All :: forall {k} f tp. (HasReprK k) => (IsExistsOr tp AllK, KnownRepr QuantRepr tp) => (forall x. ReprOf x -> f x) -> Quant (f :: k -> Type) tp
pattern All f <- (quantAsAll -> Just (QuantAsAllProof f))
    where
        All f = case (isExistsOr :: ExistsOrCases tp AllK) of
            ExistsOrExists -> QuantAny (All f)
            ExistsOrRefl -> QuantAll (TMF.mapWithKey (\repr _ -> f repr) (allReprs @k))

data QuantAsOneProof (f :: k -> Type) (tp :: QuantK k) where
    QuantAsOneProof :: (IsExistsOr tp (OneK x), IfIsOneK tp (x ~ TheOneK tp), KnownRepr QuantRepr tp) => ReprOf x -> f x -> QuantAsOneProof f tp

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
pattern Single :: forall {k} f tp. (HasReprK k) => forall x. (KnownRepr QuantRepr tp, IsExistsOr tp (OneK x), IfIsOneK tp (x ~ TheOneK tp)) => ReprOf x -> f x -> Quant (f :: k -> Type) tp
pattern Single repr x <- (quantAsOne -> Just (QuantAsOneProof repr x))
    where
        Single (repr :: ReprOf x) x = existsOrCases @tp @(OneK x) (withRepr repr $ QuantExists (Single repr x)) (QuantOne repr x)


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

instance HasTotalMapF (ReprOf :: k -> Type) => HasTotalMapF (QuantRepr :: QuantK k -> Type) where
  allValues = (Some QuantAllRepr:Some QuantSomeRepr:List.map (\(Some r) -> Some (QuantOneRepr r)) TMF.allValues)

instance HasReprK k => HasReprK (QuantK k) where
  type ReprOf = QuantRepr


-- | Augment a type with an existential case
data Exists f (tp :: QuantK k) where
  TheOne :: ReprOf x -> f (OneK x) -> Exists f (OneK x)
  TheAll :: f AllK -> Exists f AllK
  ExistsOneCtor :: ReprOf x -> f (OneK x) -> Exists f ExistsK
  ExistsAllCtor :: f AllK -> Exists f ExistsK

instance (HasReprK k, forall (x :: QuantK k). Eq (f x)) => Eq (Exists f tp) where
  a == b = case (a, b) of
    (TheOne _ a', TheOne _ b') -> a' == b' 
    (ExistsOneCtor repra a', ExistsOneCtor reprb b') -> case testEquality repra reprb of
      Just Refl -> a' == b'
      Nothing -> False
    (TheAll a', TheAll b') -> a' == b'
    (ExistsAllCtor a', ExistsAllCtor b') -> a' == b'
    _ -> False
  
instance (HasReprK k, forall (x :: QuantK k). Ord (f x)) => Ord (Exists f tp) where
  compare a b = case (a, b) of
    (ExistsOneCtor repra a', ExistsOneCtor reprb b') -> case compareF repra reprb of
      EQF -> compare a' b'
      LTF -> LT
      GTF -> GT
    (ExistsAllCtor a', ExistsAllCtor b') -> compare a' b'
    (TheOne _ a', TheOne _ b') -> compare a' b'
    (TheAll a', TheAll b') -> compare a' b'

    (ExistsOneCtor{}, ExistsAllCtor{}) -> LT
    (ExistsAllCtor{}, ExistsOneCtor{}) -> GT

data ExistsOneProof f tp where
  ExistsOneProof :: (IsExistsOr tp (OneK (TheOneK tp)), IfIsOneK tp (x ~ (TheOneK tp))) => ReprOf x -> f (OneK x) -> ExistsOneProof f tp

existsOne :: HasReprK k => Exists f (tp :: QuantK k) -> Maybe (ExistsOneProof f tp)
existsOne = \case
  TheOne repr x -> Just $ ExistsOneProof repr x
  ExistsOneCtor repr x -> Just $ ExistsOneProof repr x
  _ -> Nothing

pattern ExistsOne :: 
  forall {k} f (tp :: QuantK k). 
    (HasReprK k) => 
    forall x. (IsExistsOr tp (OneK (TheOneK tp)), IfIsOneK tp (x ~ TheOneK tp)) => 
    ReprOf x -> 
    f (OneK x) -> 
    Exists f tp
pattern ExistsOne repr x <- (existsOne -> Just (ExistsOneProof repr x))
  where
    ExistsOne repr x = existsOrCases @tp @(OneK (TheOneK tp)) (ExistsOneCtor repr x) (TheOne repr x) 

data ExistsAllProof f tp where
  ExistsAllProof :: (KnownRepr QuantRepr tp, IsExistsOr tp AllK) => f AllK -> ExistsAllProof f tp

existsAll :: Exists f tp -> Maybe (ExistsAllProof f tp)
existsAll = \case
  TheAll x -> Just $ ExistsAllProof x
  ExistsAllCtor x -> Just $ ExistsAllProof x
  _ -> Nothing

pattern ExistsAll :: forall f tp. () => (KnownRepr QuantRepr tp, IsExistsOr tp AllK) => f AllK -> Exists f tp
pattern ExistsAll x <- (existsAll -> Just (ExistsAllProof x))
  where
    ExistsAll x = existsOrCases @tp @AllK (ExistsAllCtor x) (TheAll x) 

{-# COMPLETE ExistsOne, ExistsAll #-}


data ExistsProof f tp where
  ExistsProof :: (IsExistsOr tp tp', NotExists tp') => QuantRepr tp' -> f tp' -> ExistsProof f tp

existsProof :: Exists f tp -> ExistsProof f tp
existsProof = \case
  TheOne repr x -> ExistsProof (QuantOneRepr repr) x
  TheAll x -> ExistsProof QuantAllRepr x
  ExistsAllCtor x -> ExistsProof QuantAllRepr x
  ExistsOneCtor repr x -> ExistsProof (QuantOneRepr repr) x

type family NotExists (tp :: QuantK k) :: Constraint where
  NotExists ExistsK = True ~ False
  NotExists _ = ()

pattern Exists :: forall f tp. () => forall tp'. (IsExistsOr tp tp', NotExists tp') => QuantRepr tp' -> f tp' -> Exists f tp
pattern Exists repr x <- (existsProof -> ExistsProof repr x)
  where
    Exists (repr :: QuantRepr tp') x = case repr of
      QuantOneRepr repr' -> existsOrCases @tp @tp' (ExistsOneCtor repr' x) (TheOne repr' x) 
      QuantAllRepr -> existsOrCases @tp @tp' (ExistsAllCtor x) (TheAll x)

coerceExists :: Exists f tp -> Exists f ExistsK
coerceExists e = case e of
  TheOne repr x -> ExistsOneCtor repr x
  TheAll x -> ExistsAllCtor x
  ExistsAllCtor{} -> e
  ExistsOneCtor{} -> e

{-# COMPLETE Exists #-}

instance QuantCoercible f => QuantCoercible (Exists f) where
  applyQuantCoercion qc e = case (qc, e) of
    (CoerceAllToExists, TheAll x) -> ExistsAllCtor x
    (CoerceOneToExists{}, TheOne repr x) -> ExistsOneCtor repr x
    (CoerceAllToOne repr, TheAll x) -> TheOne repr (applyQuantCoercion qc x)
    (CoerceRefl{}, _) -> e

instance QuantCoercible f => QuantConvertible (Exists f) where
  applyQuantConversion qc e = case (qc, e) of
    (ConvertRefl{}, _) -> Just e
    (ConvertNone{}, _) -> Nothing
    (ConvertExistsToAll, ExistsAllCtor x) -> Just $ TheAll x
    (ConvertExistsToOne repr, ExistsOneCtor repr' x) -> case testEquality repr repr' of
      Just Refl -> Just $ TheOne repr x
      Nothing -> Nothing
    (ConvertExistsToAll, ExistsOneCtor{}) -> Nothing
    (ConvertExistsToOne repr, ExistsAllCtor x) -> Just $ TheOne repr (applyQuantCoercion (CoerceAllToOne repr) x)


instance FunctorFC Exists where
  fmapFC f = \case
    TheOne repr x -> TheOne repr (f x)
    TheAll x -> TheAll (f x)
    ExistsOneCtor repr x -> ExistsOneCtor repr (f x)
    ExistsAllCtor x -> ExistsAllCtor (f x)

instance FoldableFC Exists where
  foldrFC f b = \case
      TheOne _ x -> f x b
      TheAll x -> f x b
      ExistsOneCtor _ x -> f x b
      ExistsAllCtor x -> f x b

instance TraversableFC Exists where
  traverseFC f = \case
    TheOne repr x -> TheOne <$> pure repr <*> f x
    TheAll x -> TheAll <$> f x
    ExistsOneCtor repr x -> ExistsOneCtor <$> pure repr <*> f x
    ExistsAllCtor x -> ExistsAllCtor <$> f x
