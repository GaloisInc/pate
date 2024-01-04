{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}


-- Deriving 'Ord' from 'OrdF'
module Data.Parameterized.WithOrd 
  ( withOrd ) 
  where
    
  
import           Data.Parameterized.Classes
import Data.Constraint
import Unsafe.Coerce (unsafeCoerce)

newtype AsOrd f tp = AsOrd (f tp)

instance TestEquality f => Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) | Just Refl <- testEquality a b = True
  _ == _ = False

instance OrdF f => Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

withOrd :: forall f tp a. OrdF f => (Ord (f tp) => a) -> a
withOrd f = case coerced_witness of
    Dict -> f
    where
        coerced_witness :: Dict (Ord (f tp))
        coerced_witness = unsafeCoerce ord_witness

        ord_witness :: Dict (Ord (AsOrd f tp))
        ord_witness = Dict