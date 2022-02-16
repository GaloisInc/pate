{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Equivalence.MemPred (
    MemPred(..)
  , mapMemPred
  , mapMemPredPar
  , memPredTrue
  , memPredFalse
  , memPredToList
  , memPredCells
  , footPrintsToPred
  , addFootPrintsToPred
  , memPredAt
  , muxMemPred
  ) where

import           Control.Monad ( forM, foldM, join )
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.TypeNats
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM

import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Parallel as PP

---------------------------------------------
-- Memory predicate

-- | This is a collection of 'PMC.MemCells', which describe ranges of memory
-- covered by this predicate.  Each 'PMC.MemCells' (which covers a set of
-- 'PMC.MemCell') contains the predicate determining whether or not it is "in".
--
-- The interpretation of those predicates is subject to the 'memPredPolarity'.
data MemPred sym arch =
    MemPred
      { memPredLocs :: MapF.MapF W4.NatRepr (PMC.MemCells sym arch)
      -- ^ The locations covered by this 'MemPred' (whether they are "in" or not
      -- is subject to the polarity)
      --
      -- The 'W4.NatRepr' index describes the number of bytes covered by each
      -- 'PMC.MemCell'
      , memPredPolarity :: W4.Pred sym
      -- ^ If true, then the predicate is true at exactly the locations
      -- specified by 'memPredLocs'.  If false, then the predicate is true
      -- everywhere but these locations.
      --
      -- Currently this is always concrete, but alternate strategies
      -- for computing pre-domains may decide to use symbolic polarities,
      -- and there is no fundamental reason to exclude this case.
      }

-- | Map the internal 'PMC.MemCells' representing the locations of a 'MemPred', preserving
-- its polarity.
mapMemPredPar ::
  forall sym arch m future.
  PP.IsFuture m future =>
  W4.IsExprBuilder sym =>
  MemPred sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (future (W4.Pred sym))) ->
  m (future (MemPred sym arch))
mapMemPredPar memPred f = do
  let
    dropFalse :: PMC.MemCell sym arch w -> W4.Pred sym -> Maybe (W4.Pred sym)
    dropFalse _ p = case W4.asConstantPred p of
      Just False -> Nothing
      _ -> Just p

    f' :: PMC.MemCell sym arch w -> W4.Pred sym -> m (future (W4.Pred sym))
    f' (cell@PMC.MemCell{}) p = f cell p

    cellsF :: PMC.MemCells sym arch w -> m (future (PMC.MemCells sym arch w))
    cellsF (PMC.MemCells cells) = do
      future_cells <- M.traverseWithKey f' cells
      PP.present $ PMC.MemCells <$> mapM PP.joinFuture future_cells

  future_locs <- PP.traverseFPar cellsF (memPredLocs memPred)
  PP.forFuture future_locs $ \locs -> do
    let locs' = TF.fmapF (\(PMC.MemCells cells) -> PMC.MemCells $ M.mapMaybeWithKey dropFalse cells) locs
    return $ memPred { memPredLocs = locs' }

mapMemPred ::
  forall sym arch m.
  Monad m =>
  W4.IsExprBuilder sym =>
  MemPred sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (W4.Pred sym)) -> m (MemPred sym arch)
mapMemPred memPred f = join $ mapMemPredPar memPred (\cell p -> return $ f cell p)


memPredToList ::
  MemPred sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
memPredToList memPred =
  concat $
  map (\(MapF.Pair _ (PMC.MemCells cells)) -> map (\(cell, p) -> (Some cell, p)) $ M.toList cells) $
  MapF.toList (memPredLocs memPred)

memPredCells ::
  OrdF (W4.SymExpr sym) => MemPred sym arch -> Set (Some (PMC.MemCell sym arch))
memPredCells memPred = S.fromList $ map fst (memPredToList memPred)

listToMemPred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)] ->
  W4.Pred sym ->
  IO (MemPred sym arch)
listToMemPred sym cells pol = do
  let
    maps = map (\(Some cell, p) -> MapF.singleton (PMC.cellWidth cell) (PMC.MemCells (M.singleton cell p))) cells
  locs <- foldM (PMC.mergeMemCellsMap sym) MapF.empty maps
  return $ MemPred locs pol

muxMemPred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemPred sym arch ->
  MemPred sym arch ->
  IO (MemPred sym arch)
muxMemPred sym p predT predF = case W4.asConstantPred p of
  Just True -> return predT
  Just False -> return predF
  _ -> do
    pol <- W4.baseTypeIte sym p (memPredPolarity predT) (memPredPolarity predF)
    locs <- PMC.muxMemCellsMap sym p (memPredLocs predT) (memPredLocs predF)
    return $ MemPred locs pol


memPredAt ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemPred sym arch ->
  PMC.MemCell sym arch w ->
  IO (W4.Pred sym)
memPredAt sym mempred stamp = do
  isInLocs <- case MapF.lookup (PMC.cellWidth stamp) (memPredLocs mempred) of
    Just stamps -> PMC.inMemCells sym stamp stamps
    Nothing -> return $ W4.falsePred sym
  W4.isEq sym isInLocs (memPredPolarity mempred)


-- | Trivial predicate that is true on all of memory
memPredTrue :: W4.IsExprBuilder sym => sym -> MemPred sym arch
memPredTrue sym = MemPred MapF.empty (W4.falsePred sym)

-- | Predicate that is false on all of memory
memPredFalse :: W4.IsExprBuilder sym => sym -> MemPred sym arch
memPredFalse sym = MemPred MapF.empty (W4.truePred sym)


footPrintsToPred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  W4.Pred sym ->
  IO (MemPred sym arch)
footPrintsToPred sym foots polarity = do
  locs <- fmap catMaybes $ forM (S.toList foots) $ \(MT.MemFootprint ptr w dir cond end) -> do
    dirPolarity <- case dir of
      MT.Read -> return $ W4.truePred sym
      MT.Write -> return $ W4.falsePred sym
    polarityMatches <- W4.isEq sym polarity dirPolarity
    cond' <- W4.andPred sym polarityMatches (MT.getCond sym cond)
    case W4.asConstantPred cond' of
      Just False -> return Nothing
      _ -> return $ Just (Some (PMC.MemCell ptr w end), cond')
  listToMemPred sym locs polarity

addFootPrintsToPred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  MemPred sym arch ->
  IO (MemPred sym arch)
addFootPrintsToPred sym foots memPred = do
  memPred' <- footPrintsToPred sym foots (memPredPolarity memPred)
  memLocs' <- PMC.mergeMemCellsMap sym (memPredLocs memPred) (memPredLocs memPred')
  return $ memPred { memPredLocs = memLocs' }

instance PEM.ExprMappable sym (MemPred sym arch) where
  mapExpr sym f memPred = do
    locs <- MapF.traverseWithKey (\_ -> PEM.mapExpr sym f) (memPredLocs memPred)
    pol <- f (memPredPolarity memPred)
    return $ MemPred locs pol
