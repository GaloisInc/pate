{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE QuantifiedConstraints  #-}
module Pate.Location (
    Location(..)
  , LocationWitherable(..)
  , LocationTraversable(..)
  , LocationPredPair(..)
  ) where

import           GHC.TypeLits
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.Trans.Except ( throwE, runExceptT )
import           Control.Monad.Trans.State ( StateT, get, put, execStateT )
import           Control.Monad.Trans ( lift )

import           Data.Parameterized.Classes
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFG as MM

import qualified Pate.PatchPair as PPa
import qualified Pate.MemCell as PMC
import qualified Pate.ExprMappable as PEM
import qualified What4.Interface as W4

-- | Generalized location-based traversals

data LocK =
    RegK MT.Type
  | CellK Nat
  | NoLocK


data Location sym arch l where
  Register :: MM.ArchReg arch tp -> Location sym arch ('RegK tp)
  Cell :: 1 <= w => PMC.MemCell sym arch w -> Location sym arch ('CellK w)
  -- | A location that does not correspond to any specific state element
  -- FIXME: currently this is convenient for including additional predicates
  -- during a location-based traversal, but it shouldn't be necessary once
  -- all the necessary types are defined to be 'LocationTraversable'
  NoLoc :: Location sym arch 'NoLocK

instance PEM.ExprMappable sym (Location sym arch l) where
  mapExpr sym f loc = case loc of
    Register r -> return $ Register r
    Cell cell -> Cell <$> PEM.mapExpr sym f cell
    NoLoc -> return NoLoc


-- TODO: this can be abstracted over 'W4.Pred'

-- | Defines 'f' to be viewed as a witherable (traversable but
-- optionally dropping elements instead of updating them) collection of
-- 'Location' elements paired with 'W4.Pred' elements.
class LocationWitherable sym arch f where
  -- | Traverse 'f' and map each element pair, optionally dropping
  -- it by returning 'Nothing'
  witherLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall l. Location sym arch l -> W4.Pred sym -> m (Maybe (Location sym arch l, W4.Pred sym))) ->
    m f

-- | Defines 'f' to be viewed as a traversable collection of
-- 'Location' elements paired with 'W4.Pred' elements.
class LocationTraversable sym arch f where
  traverseLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall l. Location sym arch l -> W4.Pred sym -> m (Location sym arch l, W4.Pred sym)) ->
    m f

  -- | Return the first location (according to the traversal order
  -- defined by 'traverseLocation') where the given function returns
  -- a 'Just' result
  firstLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall l. Location sym arch l -> W4.Pred sym -> m (Maybe a)) ->
    m (Maybe a)
  firstLocation sym body f = do
    r <- runExceptT $ do
      _ <- traverseLocation sym body $ \loc v' -> do
        lift (f loc v') >>= \case
          Just a -> throwE a
          Nothing -> return (loc, v')
      return ()
    case r of
      Left a -> return $ Just a
      Right () -> return Nothing

  -- | Fold over 'f' (according to its traversal order
  -- defined by 'traverseLocation')
  foldLocation ::
    forall m a.
    IO.MonadIO m =>
    sym ->
    f ->
    a ->
    (forall l. a -> Location sym arch l -> W4.Pred sym -> m a) ->
    m a
  foldLocation sym body init_ f = execStateT g init_
    where
      g :: StateT a m ()
      g = do
        _ <- traverseLocation sym body $ \loc v' -> do
          a <- get
          a' <- lift (f a loc v')
          put a'
          return (loc, v')
        return ()

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) =>
  LocationWitherable sym arch (PMC.MemCellPred sym arch) where
  witherLocation sym mp f = PMC.witherCell sym mp $ \c p -> do
    f (Cell c) p >>= \case
      Just (Cell c', p') -> return $ Just (c', p')
      Nothing -> return Nothing

-- | Wrapped location-predicate pair to make trivial 'LocationTraversable' values.
data LocationPredPair sym arch = forall l.
  LocationPredPair (Location sym arch l) (W4.Pred sym)

instance LocationTraversable sym arch (LocationPredPair sym arch) where
  traverseLocation _sym (LocationPredPair l p) f =
    f l p >>= \(l', p') -> return $ LocationPredPair l' p'

instance (LocationTraversable sym arch a, LocationTraversable sym arch b) =>
  LocationTraversable sym arch (a, b) where
  traverseLocation sym (a, b) f = (,) <$> traverseLocation sym a f <*> traverseLocation sym b f

instance (forall bin. (LocationWitherable sym arch (f bin))) =>
  LocationWitherable sym arch (PPa.PatchPair f) where
  witherLocation sym (PPa.PatchPair a b) f = PPa.PatchPair <$> witherLocation sym a f <*> witherLocation sym b f
