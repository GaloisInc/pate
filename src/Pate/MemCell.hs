{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Pate.MemCell (
    MemCell(..)
  , MemCells(..)
  , mapCellPreds
  , mergeMemCells
  , mergeMemCellsMap
  , muxMemCells
  , muxMemCellsMap
  , inMemCells
  , readMemCell
  , writeMemCell
  ) where

import           Control.Monad ( foldM, forM )
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as MapM
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PNR
import qualified Data.Parameterized.TraversableF as TF
import           GHC.TypeLits ( type (<=) )
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified What4.Interface as WI

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
   | Just PC.Refl <- PC.testEquality reg1 reg2
   , Just PC.Refl <- PC.testEquality off1 off2
   , Just PC.Refl <- PC.testEquality sz1 sz2
   , end1 == end2
   = Just PC.Refl
  testEquality _ _ = Nothing

instance PC.OrdF (WI.SymExpr sym) => PC.OrdF (MemCell sym arch) where
  compareF (MemCell (CLM.LLVMPointer reg1 off1) sz1 end1) (MemCell (CLM.LLVMPointer reg2 off2) sz2 end2) =
    PC.lexCompareF reg1 reg2 $
    PC.lexCompareF off1 off2 $
    PC.lexCompareF sz1 sz2 $
    PC.fromOrdering $ compare end1 end2

instance PC.TestEquality (WI.SymExpr sym) => Eq (MemCell sym arch w) where
  stamp1 == stamp2 | Just PC.Refl <- PC.testEquality stamp1 stamp2 = True
  _ == _ = False

instance PC.OrdF (WI.SymExpr sym) => Ord (MemCell sym arch w) where
  compare stamp1 stamp2  = PC.toOrdering $ PC.compareF stamp1 stamp2

-- | This is a collection of 'MemCell' that all represent memory regions of the same size.
--
-- Each 'MemCell' is associated with the predicate that says whether or not the
-- described memory is contained in the 'Pate.Equivalence.MemPred'.
newtype MemCells sym arch w = MemCells (Map.Map (MemCell sym arch w) (WI.Pred sym))

mapCellPreds ::
  (WI.Pred sym -> IO (WI.Pred sym)) ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)
mapCellPreds f (MemCells stamps) = MemCells <$> mapM f stamps

mergeMemCells ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)
mergeMemCells sym (MemCells cells1) (MemCells cells2) = do
  MemCells <$>
    MapM.mergeA
      MapM.preserveMissing
      MapM.preserveMissing
      (MapM.zipWithAMatched (\_ p1 p2 -> WI.orPred sym p1 p2))
      cells1
      cells2

muxMemCells ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  WI.Pred sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)
muxMemCells sym p (MemCells cellsT) (MemCells cellsF) = case WI.asConstantPred p of
  Just True -> return $ MemCells cellsT
  Just False -> return $ MemCells cellsF
  _ -> do
    notp <- WI.notPred sym p
    MemCells <$>
      MapM.mergeA
        (MapM.traverseMissing (\_ pT -> WI.andPred sym pT p))
        (MapM.traverseMissing (\_ pF -> WI.andPred sym pF notp))
        (MapM.zipWithAMatched (\_ p1 p2 -> WI.baseTypeIte sym p p1 p2))
        cellsT
        cellsF

-- | Mux two 'MemCells' maps, where entries that appear in only one map
-- are made conditional on the given predicate.
muxMemCellsMap ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  PC.OrdF f =>
  sym ->
  WI.Pred sym ->
  MapF.MapF f (MemCells sym arch) ->
  MapF.MapF f (MemCells sym arch) ->
  IO (MapF.MapF f (MemCells sym arch))
muxMemCellsMap sym p cellsMapT cellsMapF = case WI.asConstantPred p of
  Just True -> return cellsMapT
  Just False -> return cellsMapF
  _ -> do
    notp <- WI.notPred sym p
    MapF.mergeWithKeyM
         (\_ cellsT cellsF -> Just <$> muxMemCells sym p cellsT cellsF)
         (TF.traverseF (mapCellPreds (WI.andPred sym p)))
         (TF.traverseF (mapCellPreds (WI.andPred sym notp)))
         cellsMapT
         cellsMapF

-- | Unconditionally merge two 'MemCells' maps.
mergeMemCellsMap ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  PC.OrdF f =>
  sym ->
  MapF.MapF f (MemCells sym arch) ->
  MapF.MapF f (MemCells sym arch) ->
  IO (MapF.MapF f (MemCells sym arch))
mergeMemCellsMap sym cellsMap1 cellsMap2 = do
  MapF.mergeWithKeyM
       (\_ cells1 cells2 -> Just <$> mergeMemCells sym cells1 cells2)
       return
       return
       cellsMap1
       cellsMap2

-- | True if this cell is logically equivalent to any cell in the given
-- collection. Note that this is still false if the given cell overlaps
-- two different entries.
inMemCells ::
  forall sym arch w.
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCell sym arch w ->
  MemCells sym arch w ->
  IO (WI.Pred sym)
inMemCells sym cell (MemCells cells) =
  case Map.lookup cell cells of
    Just cond | Just True <- WI.asConstantPred cond -> return $ WI.truePred sym
    _ -> go (WI.falsePred sym) (Map.toList cells)
  where
    go :: WI.Pred sym -> [(MemCell sym arch w, WI.Pred sym)] -> IO (WI.Pred sym)
    go p ((cell', cond) : cells') = do
      eqPtrs <- PMT.llvmPtrEq sym (cellPtr cell) (cellPtr cell')
      case WI.asConstantPred eqPtrs of
        Just True | Just True <- WI.asConstantPred cond -> return $ WI.truePred sym
        Just False -> go p cells'
        _ -> do
          matches <- WI.andPred sym eqPtrs cond
          p' <- WI.orPred sym p matches
          go p' cells'
    go p [] = return p


readMemCell ::
  WI.IsSymExprBuilder sym =>
  MC.RegisterInfo (MC.ArchReg arch) =>
  sym ->
  PMT.MemTraceImpl sym (MC.ArchAddrWidth arch) ->
  MemCell sym arch w ->
  IO (CLM.LLVMPtr sym (8 WI.* w))
readMemCell sym mem cell@(MemCell{}) = do
  let repr = MC.BVMemRepr (cellWidth cell) (cellEndian cell)
  PMT.readMemArr sym mem (cellPtr cell) repr

-- FIXME: this currently drops the region due to weaknesses in the memory model
writeMemCell ::
  WI.IsSymExprBuilder sym =>
  MC.RegisterInfo (MC.ArchReg arch) =>
  sym ->
  PMT.MemTraceImpl sym (MC.ArchAddrWidth arch) ->
  MemCell sym arch w ->
  CLM.LLVMPtr sym (8 WI.* w) ->
  IO (PMT.MemTraceImpl sym (MC.ArchAddrWidth arch))
writeMemCell sym mem cell@(MemCell{}) valPtr = do
  let
    repr = MC.BVMemRepr (cellWidth cell) (cellEndian cell)
    CLM.LLVMPointer _ val = valPtr
  PMT.writeMemArr sym mem (cellPtr cell) repr val

instance PEM.ExprMappable sym (MemCell sym arch w) where
  mapExpr sym f (MemCell ptr w end) = do
    ptr' <- WEH.mapExprPtr sym f ptr
    return $ MemCell ptr' w end

instance PC.OrdF (WI.SymExpr sym) => PEM.ExprMappable sym (MemCells sym arch w) where
  mapExpr sym f (MemCells cells) = do
    maps <- forM (Map.toList cells) $ \(cell, p) -> do
      cell' <- PEM.mapExpr sym f cell
      p' <- f p
      case WI.asConstantPred p' of
        Just False -> return $ MemCells $ Map.empty
        _ -> return $ MemCells $ Map.singleton cell' p'
    foldM (mergeMemCells sym) (MemCells Map.empty) maps
