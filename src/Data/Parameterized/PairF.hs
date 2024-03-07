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

data PairF tp1 tp2 k = PairF (tp1 k) (tp2 k)

type family TupleF (t :: l) :: (k -> Type)
type instance TupleF '(a,b) = PairF a b
type instance TupleF '(a,b,c) = PairF a (PairF b c)
type instance TupleF '(a,b,c,d) = PairF a (PairF b (PairF c d))

pattern TupleF2 :: a k -> b k -> TupleF '(a,b) k
pattern TupleF2 a b = PairF a b

{-# COMPLETE TupleF2 #-}

pattern TupleF3 :: a k -> b k -> c k -> TupleF '(a,b,c) k
pattern TupleF3 a b c = PairF a (PairF b c)

{-# COMPLETE TupleF3 #-}

pattern TupleF4 :: a k -> b k -> c k -> d k -> TupleF '(a,b,c,d) k
pattern TupleF4 a b c d = PairF a (PairF b (PairF c d))

{-# COMPLETE TupleF4 #-}

