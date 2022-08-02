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

module Pate.MemCell (
    MemCell(..)
  , ppCell
  , setMemCellRegion
  , MemCellPred(..)
  , traverseWithCell
  , witherCell
  , mergeMemCellPred
  , muxMemCellPred
  , inMemCellPred
  , dropFalseCells
  , readMemCell
  , writeMemCell
  , predFromList
  , predToList
  ) where

import           Control.Monad ( foldM, forM )
import qualified Control.Monad.IO.Class as IO

import           Data.Maybe (catMaybes)
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as MapM
import           Data.Parameterized.Some
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PNR
import           GHC.TypeLits ( type (<=) )
import qualified Lang.Crucible.LLVM.MemModel as CLM
import           Lang.Crucible.Backend (IsSymInterface)
import qualified What4.Interface as WI

import qualified Prettyprinter as PP

import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as PMT
import qualified What4.ExprHelpers as WEH

-- | A pointer with an attached width, representing the size of the "cell" in bytes.
-- It represents a discrete read or write, used as the key when forming a 'Pate.Equivalence.MemPred'
--
-- Note these are indirectly contained in the 'Pate.Equivalence.MemPred', which
-- has its own 'PNR.NatRepr'; this is the same 'PNR.NatRepr' as is contained
-- here.  The duplication allows the width of the cell to be determined in isolation.
data MemCell sym arch w where
  MemCell ::
    1 <= w =>
    { cellPtr :: CLM.LLVMPtr sym (MC.ArchAddrWidth arch)
    , cellWidth :: PNR.NatRepr w
    , cellEndian :: MM.Endianness
    } -> MemCell sym arch w

instance PC.TestEquality (WI.SymExpr sym) => PC.TestEquality (MemCell sym arch) where
  testEquality (MemCell (CLM.LLVMPointer reg1 off1) sz1 end1) (MemCell (CLM.LLVMPointer reg2 off2) sz2 end2)
   | reg1 == reg2
   , Just PC.Refl <- PC.testEquality off1 off2
   , Just PC.Refl <- PC.testEquality sz1 sz2
   , end1 == end2
   = Just PC.Refl
  testEquality _ _ = Nothing

instance PC.OrdF (WI.SymExpr sym) => PC.OrdF (MemCell sym arch) where
  compareF (MemCell (CLM.LLVMPointer reg1 off1) sz1 end1) (MemCell (CLM.LLVMPointer reg2 off2) sz2 end2) =
    PC.lexCompareF off1 off2 $
    PC.lexCompareF sz1 sz2 $
    PC.fromOrdering (compare reg1 reg2 <> compare end1 end2)

instance PC.TestEquality (WI.SymExpr sym) => Eq (MemCell sym arch w) where
  stamp1 == stamp2 | Just PC.Refl <- PC.testEquality stamp1 stamp2 = True
  _ == _ = False

instance PC.OrdF (WI.SymExpr sym) => Ord (MemCell sym arch w) where
  compare stamp1 stamp2  = PC.toOrdering $ PC.compareF stamp1 stamp2

-- | Each 'MemCell' is associated with the predicate that says whether or not the
-- described memory is contained in the 'Pate.Equivalence.MemoryDomain'.
newtype MemCellPred sym arch = MemCellPred (Map.Map (Some (MemCell sym arch)) (WI.Pred sym))

traverseWithCell ::
  forall sym arch m.
  Monad m =>
  WI.IsExprBuilder sym =>
  MemCellPred sym arch ->
  (forall w. 1 <= w => MemCell sym arch w -> WI.Pred sym -> m (WI.Pred sym)) ->
  m (MemCellPred sym arch)
traverseWithCell (MemCellPred memPred) f =
  MemCellPred <$> Map.traverseWithKey (\(Some cell@MemCell{}) p -> f cell p) memPred


-- | Traverse a 'MemCellPred', optionally dropping elements instead of updating them.
witherCell ::
  forall sym arch m.
  IO.MonadIO m =>
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCellPred sym arch ->
  (forall w. 1 <= w => MemCell sym arch w -> WI.Pred sym -> m (Maybe (MemCell sym arch w, WI.Pred sym))) ->
  m (MemCellPred sym arch)
witherCell sym (MemCellPred memPred)  f = do
  es <- fmap catMaybes $ forM (Map.toList memPred) $ \(Some (cell@MemCell{}), p) -> do
    f cell p >>= \case
      Just (cell', p') -> return $ Just (Some cell', p')
      Nothing -> return Nothing
  IO.liftIO $ predFromList sym es

predFromList ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  [(Some (MemCell sym arch), WI.Pred sym)] ->
  IO (MemCellPred sym arch)
predFromList sym l = do
  -- NOTE: We can't just use Data.Map.fromList here because it will discard duplicate
  -- entries
  let maps = map (\(cell, p) -> MemCellPred $ Map.singleton cell p) l
  foldM (mergeMemCellPred sym) (MemCellPred Map.empty) maps

predToList ::
  MemCellPred sym arch ->
  [(Some (MemCell sym arch), WI.Pred sym)]
predToList (MemCellPred cells) = Map.toList cells

-- | Drop entries from the map which are concretely false.
dropFalseCells ::
  forall sym arch.
  WI.IsExprBuilder sym =>
  MemCellPred sym arch ->
  MemCellPred sym arch
dropFalseCells (MemCellPred cells) = MemCellPred $ Map.mapMaybe dropFalse cells
  where
    dropFalse ::
      WI.Pred sym ->
      Maybe (WI.Pred sym)
    dropFalse p = case WI.asConstantPred p of
      Just False -> Nothing
      _ -> Just p

mergeMemCellPred ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCellPred sym arch ->
  MemCellPred sym arch ->
  IO (MemCellPred sym arch)
mergeMemCellPred sym (MemCellPred cells1) (MemCellPred cells2) = fmap MemCellPred $ do
  MapM.mergeA
    MapM.preserveMissing
    MapM.preserveMissing
    (MapM.zipWithAMatched (\_ p1 p2 -> WI.orPred sym p1 p2))
    cells1
    cells2

muxMemCellPred ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  WI.Pred sym ->
  MemCellPred sym arch ->
  MemCellPred sym arch ->
  IO (MemCellPred sym arch)
muxMemCellPred sym p (MemCellPred cellsT) (MemCellPred cellsF) = case WI.asConstantPred p of
  Just True -> return $ MemCellPred cellsT
  Just False -> return $ MemCellPred cellsF
  _ -> fmap MemCellPred $ do
    notp <- WI.notPred sym p
    MapM.mergeA
      (MapM.traverseMissing (\_ pT -> WI.andPred sym pT p))
      (MapM.traverseMissing (\_ pF -> WI.andPred sym pF notp))
      (MapM.zipWithAMatched (\_ p1 p2 -> WI.baseTypeIte sym p p1 p2))
      cellsT
      cellsF

-- | Check if a 'MemCell' is in the given 'MemCellPred'. This is true
-- if and only if:
-- 1) The given cell is semantically equivalent to a cell in the 'MemCellPred'
-- 2) The predicate associated with that cell in the 'MemCellPred' is true
-- Notably, this does not consider all of the addresses covered by a 'MemCell'
-- (i.e. the 'w' bytes starting from the base address). The exact cell must be
-- present in the 'MemCellPred' for the result of this function to be true.
inMemCellPred ::
  forall sym arch w.
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCell sym arch w ->
  MemCellPred sym arch ->
  IO (WI.Pred sym)
inMemCellPred sym cell (MemCellPred cells) =
  case Map.lookup (Some cell) cells of
    Just cond | Just True <- WI.asConstantPred cond -> return $ WI.truePred sym
    _ -> go (WI.falsePred sym) (Map.toList cells)
  where
    go :: WI.Pred sym -> [(Some (MemCell sym arch), WI.Pred sym)] -> IO (WI.Pred sym)
    go p ((Some cell', cond) : cells') = case WI.testEquality (cellWidth cell) (cellWidth cell') of
      Just WI.Refl -> do
        eqPtrs <- PMT.llvmPtrEq sym (cellPtr cell) (cellPtr cell')
        case WI.asConstantPred eqPtrs of
          Just True | Just True <- WI.asConstantPred cond -> return $ WI.truePred sym
          Just False -> go p cells'
          _ -> do
            matches <- WI.andPred sym eqPtrs cond
            p' <- WI.orPred sym p matches
            go p' cells'
      Nothing -> go p cells'
    go p [] = return p

setMemCellRegion ::
  WI.SymNat sym ->
  MemCell sym arch w ->
  MemCell sym arch w
setMemCellRegion n cell@(MemCell{}) =
  let CLM.LLVMPointer _ off = cellPtr cell
  in cell { cellPtr = CLM.LLVMPointer n off }

readMemCell ::
  WI.IsSymExprBuilder sym =>
  MC.RegisterInfo (MC.ArchReg arch) =>
  sym ->
  PMT.MemTraceImpl sym (MC.ArchAddrWidth arch) ->
  MemCell sym arch w ->
  IO (CLM.LLVMPtr sym (8 WI.* w))
readMemCell sym mem cell@(MemCell{}) = do
  let repr = MC.BVMemRepr (cellWidth cell) (cellEndian cell)
  PMT.readMemState sym (PMT.memState mem) (PMT.memBaseMemory mem) (cellPtr cell) repr

-- FIXME: this currently drops the region due to weaknesses in the memory model
writeMemCell ::
  IsSymInterface sym =>
  MC.RegisterInfo (MC.ArchReg arch) =>
  sym ->
  -- | write condition
  WI.Pred sym ->
  PMT.MemTraceState sym (MC.ArchAddrWidth arch) ->
  MemCell sym arch w ->
  CLM.LLVMPtr sym (8 WI.* w) ->
  IO (PMT.MemTraceState sym (MC.ArchAddrWidth arch))
writeMemCell sym cond mem cell@(MemCell{}) valPtr = do
  let repr = MC.BVMemRepr (cellWidth cell) (cellEndian cell)
  PMT.writeMemState sym cond mem (cellPtr cell) repr valPtr

instance PEM.ExprMappable sym (MemCell sym arch w) where
  mapExpr sym f (MemCell ptr w end) = do
    ptr' <- WEH.mapExprPtr sym f ptr
    return $ MemCell ptr' w end

instance PEM.ExprMappable sym (MemCellPred sym arch) where
  mapExpr sym f (MemCellPred memPred) = do
    let (ks, vs) = unzip $ Map.toAscList memPred
    ks' <- PEM.mapExpr sym f ks
    vs' <- PEM.mapExpr sym f (map (PEM.ToExprMappable @sym) vs)
    let vs'' = map PEM.unEM vs'
    case ks == ks' of
      True -> return $ MemCellPred (Map.fromAscList (zip ks vs''))
      False -> IO.liftIO $ predFromList sym (zip ks' vs'')

ppCell :: (WI.IsSymExprBuilder sym) => MemCell sym arch w -> PP.Doc a
ppCell cell =
  let CLM.LLVMPointer reg off = cellPtr cell
  in WI.printSymNat reg <> "+" <> WI.printSymExpr off
