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

import qualified Prettyprinter as PP

import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Classes
import           Data.Parameterized.HasRepr ( typeRepr )
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFG as MM


import qualified Pate.PatchPair as PPa
import qualified Pate.MemCell as PMC
import qualified Pate.ExprMappable as PEM
import qualified What4.Interface as W4
import qualified What4.PredMap as WPM

-- | Generalized location-based traversals

data LocK =
    RegK MT.Type
  | CellK Nat


data Location sym arch l where
  Register :: MM.ArchReg arch tp -> Location sym arch ('RegK tp)
  Cell :: 1 <= w => PMC.MemCell sym arch w -> Location sym arch ('CellK w)

instance PEM.ExprMappable sym (Location sym arch l) where
  mapExpr sym f loc = case loc of
    Register r -> return $ Register r
    Cell cell -> Cell <$> PEM.mapExpr sym f cell

instance (W4.IsSymExprBuilder sym, MM.RegisterInfo (MM.ArchReg arch)) => PP.Pretty (Location sym arch l) where
  pretty loc = case loc of
    Register r -> PP.pretty (showF r)
    Cell c -> PMC.ppCell c

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
  LocationWitherable sym arch (PMC.MemCellPred sym arch k) where
  witherLocation sym mp f = fmap WPM.dropUnit $ WPM.alter sym mp $ \sc p -> PMC.viewCell sc $ \c ->
    f (Cell c) p >>= \case
      Just (Cell c', p') -> return $ (Some c', p')
      Nothing -> return $ (Some c, WPM.predOpUnit sym (typeRepr mp))

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) =>
  LocationTraversable sym arch (PMC.MemCellPred sym arch k) where
  traverseLocation sym mp f = witherLocation sym mp (\l p -> Just <$> f l p)

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
