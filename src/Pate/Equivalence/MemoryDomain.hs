{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

module Pate.Equivalence.MemoryDomain (
    MemoryDomain(..)
  , traverseWithCellPar
  , traverseWithCell
  , universal
  , empty
  , toList
  , toAscList
  , fromList
  , fromAscList
  , cells
  , fromFootPrints
  , addFootPrints
  , containsCell
  , mux
  ) where

import           Control.Monad ( forM, join, foldM )
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
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
-- Memory domain

-- | This wrapper around a 'PMC.MemCellPred', which describe ranges of memory
-- covered by this predicate.  Each entry in 'PMC.MemCellPred'
-- contains the predicate determining whether or not it is "in".
--
-- The interpretation of those predicates is subject to the 'memDomainPolarity'.
data MemoryDomain sym arch =
    MemoryDomain
      { memDomainPred :: PMC.MemCellPred sym arch
      -- ^ The locations covered by this 'MemoryDomain' (whether they are "in" or not
      -- is subject to the polarity)
      , memDomainPolarity :: W4.Pred sym
      -- ^ If true, then the predicate is true at exactly the locations
      -- specified by 'memDomainLocs'.  If false, then the predicate is true
      -- everywhere but these locations.
      --
      -- Currently this is always concrete, but alternate strategies
      -- for computing pre-domains may decide to use symbolic polarities,
      -- and there is no fundamental reason to exclude this case.
      }

-- | Map the internal 'PMC.MemCell' entries representing the locations of a 'MemoryDomain', preserving its polarity.
traverseWithCellPar ::
  forall sym arch m future.
  PP.IsFuture m future =>
  W4.IsExprBuilder sym =>
  MemoryDomain sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (future (W4.Pred sym))) ->
  m (future (MemoryDomain sym arch))
traverseWithCellPar memDom f = do
  let
    f' :: Some (PMC.MemCell sym arch) -> W4.Pred sym -> m (future (W4.Pred sym))
    f' (Some cell@(PMC.MemCell{})) p = f cell p

  future_preds <- M.traverseWithKey f' (memDomainPred memDom)
  PP.present $ do
    preds <- traverse PP.joinFuture future_preds
    return $ MemoryDomain (PMC.dropTrivialCells preds) (memDomainPolarity memDom)

      
traverseWithCell ::
  forall sym arch m.
  Monad m =>
  W4.IsExprBuilder sym =>
  MemoryDomain sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (W4.Pred sym)) -> m (MemoryDomain sym arch)
traverseWithCell memDom f = join $ traverseWithCellPar memDom (\cell p -> return $ f cell p)


toList ::
  MemoryDomain sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
toList memDom = M.toList (memDomainPred memDom)

toAscList ::
  MemoryDomain sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
toAscList memDom = M.toAscList (memDomainPred memDom)

cells ::
  OrdF (W4.SymExpr sym) =>
  MemoryDomain sym arch ->
  Set (Some (PMC.MemCell sym arch))
cells memDom = S.fromList $ map fst (toList memDom)

-- | Build a 'MemoryDomain' from a list of 'PMC.MemCell' entries, with a corresponding
-- predicate indicating whether or not they are in or out of the domain (subject to the
-- given polarity).
-- Duplicate entries are allowed, where the resulting predicate will be the disjunction
-- of the overlapping predicates.
fromList ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)] ->
  W4.Pred sym ->
  IO (MemoryDomain sym arch)
fromList sym l pol = do
  -- NOTE: We can't just use Data.Map.fromList here because it will discard duplicate
  -- entries
  let maps = map (\(cell, p) -> M.singleton cell p) l
  merged <- foldM (PMC.mergeMemCellPred sym) M.empty maps
  return $ MemoryDomain merged pol

-- | Similar to 'fromList' but assumes the cells are in order and disjoint
fromAscList ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  [(Some (PMC.MemCell sym arch), W4.Pred sym)] ->
  W4.Pred sym ->
  MemoryDomain sym arch
fromAscList l pol = MemoryDomain (M.fromAscList l) pol

mux ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemoryDomain sym arch ->
  MemoryDomain sym arch ->
  IO (MemoryDomain sym arch)
mux sym p predT predF = case W4.asConstantPred p of
  Just True -> return predT
  Just False -> return predF
  _ -> do
    pol <- W4.baseTypeIte sym p (memDomainPolarity predT) (memDomainPolarity predF)
    locs <- PMC.muxMemCellPred sym p (memDomainPred predT) (memDomainPred predF)
    return $ MemoryDomain locs pol

-- | True if the given 'PMC.MemCell' is in the given 'MemoryDomain', according to
-- its polarity.
containsCell ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemoryDomain sym arch ->
  PMC.MemCell sym arch w ->
  IO (W4.Pred sym)
containsCell sym memDom cell = do
  isInLocs <- PMC.inMemCellPred sym cell (memDomainPred memDom)
  W4.isEq sym isInLocs (memDomainPolarity memDom)


-- | Trivial domain that covers all of memory
universal :: W4.IsExprBuilder sym => sym -> MemoryDomain sym arch
universal sym = MemoryDomain M.empty (W4.falsePred sym)

-- | Trivial domain that covers no memory (the empty domain)
empty :: W4.IsExprBuilder sym => sym -> MemoryDomain sym arch
empty sym = MemoryDomain M.empty (W4.truePred sym)


fromFootPrints ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  W4.Pred sym ->
  IO (MemoryDomain sym arch)
fromFootPrints sym foots polarity = do
  locs <- fmap catMaybes $ forM (S.toList foots) $ \(MT.MemFootprint ptr w dir cond end) -> do
    dirPolarity <- case dir of
      MT.Read -> return $ W4.truePred sym
      MT.Write -> return $ W4.falsePred sym
    polarityMatches <- W4.isEq sym polarity dirPolarity
    cond' <- W4.andPred sym polarityMatches (MT.getCond sym cond)
    case W4.asConstantPred cond' of
      Just False -> return Nothing
      _ -> return $ Just (Some (PMC.MemCell ptr w end), cond')
  fromList sym locs polarity

addFootPrints ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  MemoryDomain sym arch ->
  IO (MemoryDomain sym arch)
addFootPrints sym foots memDom = do
  memDom' <- fromFootPrints sym foots (memDomainPolarity memDom)
  memLocs' <- PMC.mergeMemCellPred sym (memDomainPred memDom) (memDomainPred memDom')
  return $ memDom { memDomainPred = memLocs' }

instance PEM.ExprMappable sym (MemoryDomain sym arch) where
  foldMapExpr sym f memDom b = do
    let (ks, vs) = unzip $ M.toAscList (memDomainPred memDom)
    (ks', b') <- PEM.foldMapExpr sym f ks b
    (vs', b'') <- PEM.foldMapExpr sym f (map (PEM.ToExprMappable @sym) vs) b'
    let vs'' = map PEM.unEM vs'
    (pol', b''') <- f (memDomainPolarity memDom) b''
    memDom' <- case ks == ks' of
      True -> return $ fromAscList (zip ks vs'') pol'
      False -> fromList sym (zip ks' vs'') pol'
    return $ (memDom', b''')

  foldExpr sym f memDom b = do
    b' <- PEM.foldExpr sym f (M.toList $ fmap (PEM.ToExprMappable @sym) (memDomainPred memDom)) b
    f (memDomainPolarity memDom) b'
