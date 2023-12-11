{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.UnwrapType ( UnwrapType, unwrapClass ) where

import Data.Constraint(Dict(..))
import Data.Kind (Type)
import Data.Parameterized
import Data.Coerce
import Data.Proxy
import Unsafe.Coerce (unsafeCoerce)

type family UnwrapType (tp :: Type) :: Type

withInstance' :: forall c tp a. (Coercible tp (UnwrapType tp), c tp) => Proxy c -> Proxy tp -> (c (UnwrapType tp) => a) -> a
withInstance' _ _ f = case coerced_witness of
    Dict -> f
    where
        coerced_witness :: Dict (c (UnwrapType tp))
        coerced_witness = unsafeCoerce witness

        witness :: Dict (c tp)
        witness = Dict


unwrapClass :: forall c wrapped_tp a. (Coercible wrapped_tp (UnwrapType wrapped_tp), (c wrapped_tp)) => (c (UnwrapType wrapped_tp) => a) -> a
unwrapClass f = withInstance' (Proxy @c) (Proxy @wrapped_tp) f

class TestClass tp where

type family Foo k :: Symbol -> Type
newtype WrappedFoo k s = WrappedFoo (Foo k s)
type instance UnwrapType (WrappedFoo k s) = Foo k s

instance TestClass (WrappedFoo k s) where

_test :: forall k s a. ((TestClass (Foo k s)) => a) -> a
_test x = unwrapClass @TestClass @(WrappedFoo k s) $ x