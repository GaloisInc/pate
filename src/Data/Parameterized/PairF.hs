{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Parameterized.PairF 
  (
    PairF(..)
  , TupleF
  , pattern TupleF2
  , pattern TupleF3
  , pattern TupleF4
  ) where

import           Data.Kind (Type)
import Data.Parameterized.Classes

data PairF tp1 tp2 k = PairF (tp1 k) (tp2 k)

type family TupleF (t :: l) :: (k -> Type)
type instance TupleF '(a,b) = PairF a b
type instance TupleF '(a,b,c) = PairF a (PairF b c)
type instance TupleF '(a,b,c,d) = PairF a (PairF b (PairF c d))

pattern TupleF2 :: a k -> b k -> TupleF '(a,b) k
pattern TupleF2 a b = PairF a b

instance (TestEquality a, TestEquality b) => TestEquality (PairF a b) where
  testEquality (PairF a1 b1) (PairF a2 b2) = 
    case (testEquality a1 a2, testEquality b1 b2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing

instance (OrdF a, OrdF b) => OrdF (PairF a b) where
  compareF (PairF a1 b1) (PairF a2 b2) = 
    lexCompareF a1 a2 $ compareF b1 b2

{-# COMPLETE TupleF2 #-}

pattern TupleF3 :: a k -> b k -> c k -> TupleF '(a,b,c) k
pattern TupleF3 a b c = PairF a (PairF b c)

{-# COMPLETE TupleF3 #-}

pattern TupleF4 :: a k -> b k -> c k -> d k -> TupleF '(a,b,c,d) k
pattern TupleF4 a b c d = PairF a (PairF b (PairF c d))

{-# COMPLETE TupleF4 #-}

