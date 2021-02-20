{-|
Module           : Pate.Parallel
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Primitives for parallelism
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Pate.Parallel
    ( ParMonad(..)
    , NonParMonad(..)
    )

    where

import       Control.Monad.Trans.Class

import       Data.Parameterized.TraversableF as TF


--data SimpleFuture m a  =
--    Future !(m a)
--  | Present !a

--instance Functor m => Functor (Future m) where
--  fmap f (Future m) = Future (f <$> m)
--  fmap f (Present v) = Present (f v)

data ConstF f a tp where
  ConstF :: { getConstF :: f (a tp) } -> ConstF f a tp

newtype NonParMonad m a where
  NonParMonad :: { runNpm :: m a } -> NonParMonad m a
  deriving ( Functor, Applicative, Monad )

instance MonadTrans NonParMonad where
  lift m = NonParMonad m

newtype NoFuture a where
  NoFuture :: a -> NoFuture a
  deriving Functor

instance Monad m => ParMonad (NonParMonad m) where
  type Future (NonParMonad m) = NoFuture
  joinFuture (NoFuture v) = pure v
  promise m = do
    a <- m
    return $ NoFuture a
  present = promise

class Monad m => ParMonad m where
  type Future m :: * -> *
  
  traverseFPar :: forall t f e.
    TF.TraversableF t => (forall s. e s -> m (Future m (f s))) -> t e -> m (Future m (t f))
  traverseFPar f t = do
    let
      f' :: forall s . e s -> m (ConstF (Future m) f s)
      f' e = ConstF <$> f e
    promises <- TF.traverseF f' t
    present $ TF.traverseF (joinFuture . getConstF) promises

  traversePar :: Traversable t => (e -> m (Future m f)) -> t e -> m (Future m (t f))
  traversePar f t = do
    promises <- traverse f t
    present $ traverse joinFuture promises

  forFuture :: Future m a -> (a -> m b) -> m (Future m b)
  forFuture m f = present $ do
    v <- joinFuture m
    f v
  
  joinFuture :: Future m a -> m a
  promise :: m a -> m (Future m a)
  present :: m a -> m (Future m a)
  

