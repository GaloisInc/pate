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
  , setMemCellRegion
  , MemCellPred
  , mergeMemCellPred
  , muxMemCellPred
  , inMemCellPred
  , readMemCell
  , writeMemCell
  ) where


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
-- described memory is contained in the 'Pate.Equivalence.MemPred'.
type MemCellPred sym arch = Map.Map (Some (MemCell sym arch)) (WI.Pred sym)

mergeMemCellPred ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCellPred sym arch ->
  MemCellPred sym arch ->
  IO (MemCellPred sym arch)
mergeMemCellPred sym cells1 cells2 = do
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
muxMemCellPred sym p cellsT cellsF = case WI.asConstantPred p of
  Just True -> return cellsT
  Just False -> return cellsF
  _ -> do
    notp <- WI.notPred sym p
    MapM.mergeA
      (MapM.traverseMissing (\_ pT -> WI.andPred sym pT p))
      (MapM.traverseMissing (\_ pF -> WI.andPred sym pF notp))
      (MapM.zipWithAMatched (\_ p1 p2 -> WI.baseTypeIte sym p p1 p2))
      cellsT
      cellsF

-- | True if this cell is logically equivalent to any cell in the given
-- collection. Note that this is still false if the given cell overlaps
-- two different entries.
inMemCellPred ::
  forall sym arch w.
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  sym ->
  MemCell sym arch w ->
  MemCellPred sym arch ->
  IO (WI.Pred sym)
inMemCellPred sym cell cells =
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
  PMT.MemTraceState sym (MC.ArchAddrWidth arch) ->
  MemCell sym arch w ->
  IO (CLM.LLVMPtr sym (8 WI.* w))
readMemCell sym mem cell@(MemCell{}) = do
  let repr = MC.BVMemRepr (cellWidth cell) (cellEndian cell)
  PMT.readMemState sym mem (cellPtr cell) repr

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
