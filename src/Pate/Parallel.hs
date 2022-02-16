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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Parallel
    ( IsFuture(..)
    , Future
    , ConstF(..)
    )
    where

import qualified Control.Concurrent.Async as A
import qualified Control.Concurrent as IO

import           Control.Monad.Trans
import qualified Data.Kind as DK
import           Data.Parameterized.TraversableF as TF

data ConstF f a tp where
  ConstF :: { getConstF :: f (a tp) } -> ConstF f a tp

class Monad m => IsFuture m (future :: DK.Type -> DK.Type) where
  
  traverseFPar :: forall t f e.
    TF.TraversableF t => (forall s. e s -> m (future (f s))) -> t e -> m (future (t f))
  traverseFPar f t = do
    let
      f' :: forall s . e s -> m (ConstF future f s)
      f' e = ConstF <$> f e
    promises <- TF.traverseF f' t
    present $ TF.traverseF (joinFuture . getConstF) promises

  traversePar :: Traversable t => (e -> m (future f)) -> t e -> m (future (t f))
  traversePar f t = do
    promises <- traverse f t
    present $ traverse joinFuture promises

  forMPar :: Traversable t => t e -> (e -> m (future f)) -> m (future (t f))
  forMPar t f = traversePar f t
  
  forFuture :: future a -> (a -> m b) -> m (future b)
  forFuture m f = present $ do
    v <- joinFuture m
    f v

  joinFuture :: future a -> m a

  -- | A long-running forked result
  promise :: m a -> m (future a)

  -- | An explicitly lazy result, but evaluated on the current thread
  present :: m a -> m (future a)

  immediate :: a -> m (future a)

-- | Any monad trivially produces its own future results
instance Monad m => IsFuture m m where
  joinFuture f = f
  forFuture f g = return $ f >>= g
  present f = return f
  promise = present
  immediate = return . return

data Future a where
  -- | A "future" value is a handle on a forked thread, with a
  -- finalization action
  Future :: A.Async a -> (a -> IO b) -> Future b
  -- | A "present" value is evaluated lazily when the future is joined, but on the
  -- joining thread
  Present :: IO a -> Future a
  -- | An "immediate" value has already been evaluated.
  Immediate :: a -> Future a

-- | Cached evaluation that assumes the same value for 'b' will always be given.
cachedEval :: (b -> IO a) -> IO (b -> IO a)
cachedEval f = do
  var <- IO.newMVar Nothing
  let f' b = IO.modifyMVar var $ \case
        Just a -> return (Just a, a)
        Nothing -> do
          a <- f b
          return (Just a, a)
  return f'

instance IsFuture IO Future where
  joinFuture (Future a_var fin) = fin =<< A.wait a_var
  joinFuture (Present f) = f
  joinFuture (Immediate a) = return a

  forFuture (Future a_var g) f = do
    f' <- liftIO $ cachedEval f
    return $ Future a_var (\a -> g a >>= f')
  forFuture (Present g) f = do
    f' <- liftIO $ cachedEval f
    return $ Present (g >>= f')
  forFuture (Immediate a) f = present (f a)

  present m = do
    f' <- liftIO $ cachedEval (\() -> m)
    return $ Present (f' ())

  promise m = do
    a_var <- A.async m
    return $ Future a_var return

  immediate = return . Immediate
