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

module Pate.Parallel
    ( IsFuture(..)
    , Future(..)
    , InFutureIO(..)
    , FutureF
    , ConstF(..)
    )
    where

import           Data.Parameterized.TraversableF as TF
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Trans
import qualified UnliftIO.Concurrent as IO

data ConstF f a tp where
  ConstF :: { getConstF :: f (a tp) } -> ConstF f a tp

class Monad m => IsFuture m (future :: * -> *) where
  
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

  forFuture :: future a -> (a -> m b) -> m (future b)
  forFuture m f = present $ do
    v <- joinFuture m
    f v

  joinFuture :: future a -> m a

  -- | A long-running forked result
  promise :: m a -> m (future a)

  -- | An explicitly lazy result, but evaluated on the current thread
  present :: m a -> m (future a)

-- | Any monad trivially produces its own future results
instance Monad m => IsFuture m m where
  joinFuture f = f
  forFuture f g = return $ f >>= g
  present f = return f
  promise = present

data Future a where
  Future :: IO.ThreadId -> IO.MVar a -> (a -> IO b) -> Future b
  Present :: IO a -> Future a

type FutureF = ConstF Future

-- | A trivial wrapper to differentiate which Future operations to use
newtype InFutureIO m a = InFutureIO { runInFutureIO :: m a }
  deriving (Functor, Applicative, Monad, IO.MonadIO, IO.MonadUnliftIO)

instance MonadTrans InFutureIO where
  lift f = InFutureIO f

instance IO.MonadUnliftIO m => IsFuture (InFutureIO m) Future where
  joinFuture (Future _ a f) = IO.liftIO $ IO.readMVar a >>= f
  joinFuture (Present v) = IO.liftIO $ v

  forFuture (Present a) f = do
    runInIO <- IO.askRunInIO
    return $ Present $ (a >>= runInIO . f)
  forFuture (Future tid a g) f = do
    runInIO <- IO.askRunInIO
    return $ Future tid a (\v -> g v >>= runInIO . f)

  present m = do
    runInIO <- IO.askRunInIO
    return $ Present $ runInIO m    

  promise m = do
    var <- IO.newEmptyMVar
    let runM = do
          a <- m
          IO.putMVar var $! a
    tid <- IO.forkIO runM
    return $ Future tid var return

instance IsFuture IO Future where
  present m = runInFutureIO $ present (lift m)
  promise m = runInFutureIO $ promise (lift m)
  joinFuture future = runInFutureIO $ joinFuture future
  forFuture future f = runInFutureIO $ forFuture future (lift . f)
