{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Equivalence.MemoryDomain (
    MemoryDomain
  , traverseWithCell
  , universal
  , toList
  , fromList
  , cells
  , fromFootPrints
  , excludeFootPrints
  , mayContainCell
  , mux
  , intersect
  , ppMemoryDomainEntries
  , dropFalseCells
  ) where

import           Control.Monad ( forM )
import           Data.Maybe (catMaybes)
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.TypeNats
import qualified What4.Interface as W4

import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MM

import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Location as PL
import qualified What4.PredMap as WPM

---------------------------------------------
-- Memory domain

-- | This wrapper around a 'PMC.MemCellPred' describes ranges of memory
-- covered by this domain. A memory domain is defined exclusively -
-- all addresses are considered to be "in" the domain unless they are
-- covered by the given 'PMC.MemCellPred'.
data MemoryDomain sym arch =
    MemoryDomain
      { memDomainPred :: PMC.MemCellPred sym arch WPM.PredDisjT
      -- ^ The locations excluded by this 'MemoryDomain' 
      }

-- | Map the internal 'PMC.MemCell' entries representing the locations of a 'MemoryDomain'. Predicates which are concretely false are dropped from in resulting internal 'PMC.MemCellPred' (this has no effect on the interpretation of the domain). Supports parallel traversal if the 'future' parameter is instantiated to 'Par.Future'.
traverseWithCell ::
  forall sym arch m.
  Monad m =>
  W4.IsExprBuilder sym =>
  MemoryDomain sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (W4.Pred sym)) ->
  m (MemoryDomain sym arch)
traverseWithCell (MemoryDomain mp) f = MemoryDomain <$> WPM.traverse mp (\(Some c) p -> PMC.viewCell c $ f c p)

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) => PL.LocationWitherable sym arch (MemoryDomain sym arch) where
  witherLocation sym (MemoryDomain mp) f = MemoryDomain <$> PL.witherLocation sym mp f

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) => PL.LocationTraversable sym arch (MemoryDomain sym arch) where
  traverseLocation sym d f = PL.witherLocation sym d (\loc v -> Just <$> f loc v)


-- | Drop cells in the inner 'PMC.MemCellPred' that are concretely false
dropFalseCells ::
  W4.IsExprBuilder sym =>
  MemoryDomain sym arch ->
  MemoryDomain sym arch
dropFalseCells dom = dom { memDomainPred = WPM.dropUnit (memDomainPred dom) }

toList ::
  MemoryDomain sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
toList memDom = WPM.toList (memDomainPred memDom)


cells ::
  OrdF (W4.SymExpr sym) =>
  MemoryDomain sym arch ->
  Set (Some (PMC.MemCell sym arch))
cells memDom = S.fromList $ map fst (toList memDom)

-- | Build a 'MemoryDomain' from a list of 'PMC.MemCell' entries, with a corresponding
-- predicate indicating that is true if the cell is excluded from the domain.
-- Duplicate entries are allowed, where the resulting predicate will be the disjunction
-- of the clashing entries.
fromList ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)] ->
  IO (MemoryDomain sym arch)
fromList sym l = MemoryDomain <$> (WPM.fromList sym WPM.PredDisjRepr l)

mux ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemoryDomain sym arch ->
  MemoryDomain sym arch ->
  IO (MemoryDomain sym arch)
mux sym p predT predF =
  MemoryDomain <$> WPM.mux sym p (memDomainPred predT) (memDomainPred predF)

-- | Intersect two domains, where a cell is excluded in the resulting domain if it
-- is excluded in either of the source domains
intersect ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemoryDomain sym arch ->
  MemoryDomain sym arch ->
  IO (MemoryDomain sym arch)
intersect sym predT predF =
  MemoryDomain <$> WPM.merge sym (memDomainPred predT) (memDomainPred predF)


-- | True if the given 'PMC.MemCell' is not excluded by the given 'MemoryDomain'.
-- Notably this does not consider the memory region covered by the given cell.
-- A cell must be exactly excluded (i.e. present in the underlying 'PMC.MemCellPred')
-- for this predicate to be true - it is not sufficient for a cell to be subsumed by an entry.
--
-- A more precise model could instead consider the memory region
-- covered by the excluded cells. This would correctly identify
-- edge cases where a cell can be considered excluded by the domain
-- if it subsumed by one or more entries. This reasoning would be
-- very expensive and likely not useful in most cases.
--
-- The tradeoff is that this may conservatively
-- decide a cell is included when it could be proven to be excluded
-- with more precise semantics.
-- This is therefore sound to use when proving equality on a domain,
-- but unsound if used to assume initial equality.
mayContainCell ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemoryDomain sym arch ->
  PMC.MemCell sym arch w ->
  IO (W4.Pred sym)
mayContainCell sym memDom cell = do
  isInLocs <- PMC.inMemCellPred sym cell (memDomainPred memDom)
  W4.notPred sym isInLocs


-- | Domain that covers all of memory (i.e. no cells are excluded)
universal :: W4.IsExprBuilder sym => sym -> MemoryDomain sym arch
universal _sym = MemoryDomain (WPM.empty WPM.PredDisjRepr)

-- | Derive a 'MemoryDomain' from a set of 'MT.MemFootprint'.
-- The resulting domain includes all of memory, except for the given footprints.
fromFootPrints ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  IO (MemoryDomain sym arch)
fromFootPrints sym foots = do
  locs <- fmap catMaybes $ forM (S.toList foots) $ \(MT.MemFootprint ptr w _dir cond end) -> do
    let cond' = MT.getCond sym cond
    case W4.asConstantPred cond' of
      Just False -> return Nothing
      _ -> return $ Just (Some (PMC.MemCell ptr w end), cond')
  fromList sym locs

-- | Exclude footprints from an existing 'MemoryDomain'.
excludeFootPrints ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)) ->
  MemoryDomain sym arch ->
  IO (MemoryDomain sym arch)
excludeFootPrints sym foots memDom = do
  memDom' <- fromFootPrints sym foots
  memLocs' <- WPM.asHasPredOps sym $ WPM.merge sym (memDomainPred memDom) (memDomainPred memDom')
  return $ memDom { memDomainPred = memLocs' }

instance PEM.ExprMappable2 sym1 sym2 (MemoryDomain sym1 arch) (MemoryDomain sym2 arch) where
  mapExpr2 sym1 sym2 f memDom = MemoryDomain <$> PEM.mapExpr2 sym1 sym2 f (memDomainPred memDom)

ppMemoryDomainEntries ::
  forall sym arch a.
  W4.IsSymExprBuilder sym =>
  -- | Called when a cell is in the domain conditionally, with
  -- a non-trivial condition
  (W4.Pred sym -> PP.Doc a) ->
  MemoryDomain sym arch ->
  PP.Doc a
ppMemoryDomainEntries showCond dom = PP.vsep (map ppMem $ toList dom)
  where
    ppMem :: (Some (PMC.MemCell sym arch), W4.Pred sym) -> PP.Doc a
    ppMem (Some cell, p) = case W4.asConstantPred p of
      Just True -> PMC.ppCell cell
      _ -> PMC.ppCell cell <> PP.line <> (showCond p)

instance W4.IsSymExprBuilder sym => PP.Pretty (MemoryDomain sym arch) where
  pretty = ppMemoryDomainEntries W4.printSymExpr
