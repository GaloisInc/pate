{-|
Module           : Pate.SimState
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Functionality for handling the inputs and outputs of crucible.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}


module Pate.SimState
  ( -- simulator state
    SimState(..)
  , SimInput(..)
  , SimOutput(..)
  , SimSpec(..)
  , SimBundle(..)
  , simInMem
  , simInRegs
  , simOutMem
  , simOutRegs
  , simPair
  -- variable binding
  , SimVars(..)
  , MacawRegVar(..)
  , bindSpec
  , flatVars
   -- memory
  , MemCell(..)
  , MemCells(..)
  , mapCellPreds
  , mergeMemCells
  , mergeMemCellsMap
  , muxMemCells
  , muxMemCellsMap
  , inMemCells
  ) where

import           GHC.TypeNats

import           Control.Monad ( forM, foldM )

import           Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS

import qualified What4.Interface as W4

import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Types as PT
import           What4.ExprHelpers

------------------------------------
-- Crucible inputs and outputs

data SimState sym arch (bin :: PT.WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (PT.MacawRegEntry sym)
  }

data SimInput sym arch bin = SimInput
  {
    simInState :: SimState sym arch bin
  , simInBlock :: PT.ConcreteBlock arch bin
  }


simInMem ::
  SimInput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simInMem simIn = simMem $ simInState simIn

simInRegs ::
  SimInput sym arch bin -> MM.RegState (MM.ArchReg arch) (PT.MacawRegEntry sym)
simInRegs simIn = simRegs $ simInState simIn


data SimOutput sym arch bin = SimOutput
  {
    simOutState :: SimState sym arch bin
  , simOutExit :: MT.ExitClassifyImpl sym
  , simOutReturn :: CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch)))
  }

simOutMem ::
  SimOutput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simOutMem simIn = simMem $ simOutState simIn

simOutRegs ::
  SimOutput sym arch bin -> MM.RegState (MM.ArchReg arch) (PT.MacawRegEntry sym)
simOutRegs simIn = simRegs $ simOutState simIn


data SimSpec sym arch f = SimSpec
  {
    specVarsO :: SimVars sym arch PT.Original
  , specVarsP :: SimVars sym arch PT.Patched
  , specAsm :: W4.Pred sym
  , specBody :: f
  }

data SimBundle sym arch = SimBundle
  {
    simInO :: SimInput sym arch PT.Original
  , simInP :: SimInput sym arch PT.Patched
  , simOutO :: SimOutput sym arch PT.Original
  , simOutP :: SimOutput sym arch PT.Patched
  }

simPair :: SimBundle sym arch -> PT.PatchPair arch
simPair bundle = PT.PatchPair (simInBlock $ simInO bundle) (simInBlock $ simInP bundle)

-----------------------------------------
-- Memory

-- | A pointer with an attached width, representing the size of the "cell" in bytes
data MemCell sym arch w where
  MemCell ::
    1 <= w =>
    { cellPtr :: CLM.LLVMPtr sym (MM.ArchAddrWidth arch)
    , cellWidth :: W4.NatRepr w
    } -> MemCell sym arch w

instance TestEquality (W4.SymExpr sym) => TestEquality (MemCell sym arch) where
  testEquality (MemCell (CLM.LLVMPointer reg1 off1) sz1) (MemCell (CLM.LLVMPointer reg2 off2) sz2)
   | Just Refl <- testEquality reg1 reg2
   , Just Refl <- testEquality off1 off2
   , Just Refl <- testEquality sz1 sz2
   = Just Refl
  testEquality _ _ = Nothing

instance OrdF (W4.SymExpr sym) => OrdF (MemCell sym arch) where
  compareF (MemCell (CLM.LLVMPointer reg1 off1) sz1) (MemCell (CLM.LLVMPointer reg2 off2) sz2) =
    lexCompareF reg1 reg2 $
     lexCompareF off1 off2 $
     compareF sz1 sz2

instance TestEquality (W4.SymExpr sym) => Eq (MemCell sym arch w) where
  stamp1 == stamp2 | Just Refl <- testEquality stamp1 stamp2 = True
  _ == _ = False

instance OrdF (W4.SymExpr sym) => Ord (MemCell sym arch w) where
  compare stamp1 stamp2  = toOrdering $ compareF stamp1 stamp2

newtype MemCells sym arch w = MemCells (Map (MemCell sym arch w) (W4.Pred sym))

mapCellPreds ::
  (W4.Pred sym -> IO (W4.Pred sym)) ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)
mapCellPreds f (MemCells stamps) = MemCells <$> mapM f stamps

mergeMemCells ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)  
mergeMemCells sym (MemCells cells1) (MemCells cells2) = do
  MemCells <$>
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\_ p1 p2 -> W4.orPred sym p1 p2))
      cells1
      cells2

muxMemCells ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)  
muxMemCells sym p (MemCells cellsT) (MemCells cellsF) = do
  notp <- W4.notPred sym p
  MemCells <$>
    M.mergeA
      (M.traverseMissing (\_ pT -> W4.andPred sym pT p))
      (M.traverseMissing (\_ pF -> W4.andPred sym pF notp)) 
      (M.zipWithAMatched (\_ p1 p2 -> W4.baseTypeIte sym p p1 p2))
      cellsT
      cellsF

muxMemCellsMap ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF f =>
  sym ->
  W4.Pred sym ->
  MapF.MapF f (MemCells sym arch) ->
  MapF.MapF f (MemCells sym arch) ->
  IO (MapF.MapF f (MemCells sym arch))  
muxMemCellsMap sym p cellsMapT cellsMapF = do
  notp <- W4.notPred sym p
  MapF.mergeWithKeyM
       (\_ cellsT cellsF -> Just <$> muxMemCells sym p cellsT cellsF)
       (TF.traverseF (mapCellPreds (W4.andPred sym p)))
       (TF.traverseF (mapCellPreds (W4.andPred sym notp)))
       cellsMapT
       cellsMapF

mergeMemCellsMap ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF f =>
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
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemCell sym arch w ->
  MemCells sym arch w ->
  IO (W4.Pred sym) 
inMemCells sym cell (MemCells cells) =
  case M.lookup cell cells of
    Just cond | Just True <- W4.asConstantPred cond -> return $ W4.truePred sym
    _ -> go (W4.falsePred sym) (M.toList cells)
  where
    go :: W4.Pred sym -> [(MemCell sym arch w, W4.Pred sym)] -> IO (W4.Pred sym)
    go p ((cell', cond) : cells') = do
      eqPtrs <- MT.llvmPtrEq sym (cellPtr cell) (cellPtr cell')
      case W4.asConstantPred eqPtrs of
        Just True | Just True <- W4.asConstantPred cond -> return $ W4.truePred sym
        Just False -> go p cells'
        _ -> do
          matches <- W4.andPred sym eqPtrs cond
          p' <- W4.orPred sym p matches
          go p' cells'
    go p [] = return p

---------------------------------------
-- Variable binding

data SimVars sym arch bin = SimVars
  {
    simVarMem :: MT.MemTraceVar sym (MM.ArchAddrWidth arch)
  , simVarRegs :: MM.RegState (MM.ArchReg arch) (MacawRegVar sym)
  , simVarState :: SimState sym arch bin
  }

data MacawRegVar sym tp where
  MacawRegVar ::
    { macawVarEntry :: PT.MacawRegEntry sym tp
    , macawVarBVs :: Ctx.Assignment (W4.BoundVar sym) (CrucBaseTypes (MS.ToCrucibleType tp))
    } ->
    MacawRegVar sym tp

type family CrucBaseTypes (tp :: CC.CrucibleType) :: Ctx.Ctx W4.BaseType
type instance CrucBaseTypes (CLM.LLVMPointerType w) = (Ctx.EmptyCtx Ctx.::> W4.BaseNatType Ctx.::> W4.BaseBVType w)

flatVars ::
  SimVars sym arch bin -> [Some (W4.BoundVar sym)]
flatVars simVars =
  let
    regVarPairs =
      MapF.toList $
      MM.regStateMap $
      (simVarRegs simVars)
    regVars = concat $ map (\(MapF.Pair _ (MacawRegVar _ vars)) -> TFC.toListFC Some vars) regVarPairs
    MT.MemTraceVar memVar = simVarMem simVars
  in ((Some memVar):regVars)

flatVarBinds ::
  forall sym arch bin.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimVars sym arch bin ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PT.MacawRegEntry sym) ->
  IO [Some (VarBinding sym)]
flatVarBinds _sym simVars mem regs = do
  let
    regBinds =
      MapF.toList $
      MM.regStateMap $
      MM.zipWithRegState (\(MacawRegVar _ vars) val -> MacawRegVar val vars) (simVarRegs simVars) regs
  regVarBinds <- fmap concat $ forM regBinds $ \(MapF.Pair _ (MacawRegVar val vars)) -> do
    case PT.macawRegRepr val of
      CLM.LLVMPointerRepr{} -> do
        CLM.LLVMPointer region off <- return $ PT.macawRegValue val
        (Ctx.Empty Ctx.:> regVar Ctx.:> offVar) <- return $ vars
        return $ [Some (VarBinding regVar region), Some (VarBinding offVar off)]
      _ -> fail "flatVarBinds: unsupported type"

  MT.MemTraceVar memVar <- return $ simVarMem simVars
  let memBind = VarBinding memVar (MT.memArr mem)   
  return $ ((Some memBind):regVarBinds)

bindSpec ::
  PT.ExprMappable sym f =>
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym -> 
  SimState sym arch PT.Original ->
  SimState sym arch PT.Patched ->
  SimSpec sym arch f ->
  IO (W4.Pred sym, f)
bindSpec sym stO stP spec = do
  flatO <- flatVarBinds sym (specVarsO spec) (simMem stO) (simRegs stO)
  flatP <- flatVarBinds sym (specVarsP spec) (simMem stP) (simRegs stP)
  Some flatCtx <- return $ Ctx.fromList (flatO ++ flatP)
  body <- PT.mapExpr sym (rebindExpr sym flatCtx) (specBody spec)
  asm <- rebindExpr sym flatCtx (specAsm spec)
  return $ (asm, body)

------------------------------------
-- ExprMappable instances

instance PT.ExprMappable sym (SimState sym arch bin) where
  mapExpr sym f st = do
    simMem' <- PT.mapExpr sym f $ simMem st
    simRegs' <- MM.traverseRegsWith (\_ -> PT.mapExpr sym f) $ simRegs st
    return $ SimState simMem' simRegs'

instance PT.ExprMappable sym (SimInput sym arch bin) where
  mapExpr sym f simIn = do
    st <- PT.mapExpr sym f (simInState simIn)
    return $ simIn { simInState = st }

instance PT.ExprMappable sym (SimOutput sym arch bin) where
  mapExpr sym f simOut = do
    st <- PT.mapExpr sym f (simOutState simOut)
    ret <- traverse (PT.mapExprPtr sym f) $ simOutReturn simOut
    return $ simOut { simOutState = st, simOutReturn = ret }

instance PT.ExprMappable sym (SimBundle sym arch) where
  mapExpr sym f bundle = do
    simInO' <- PT.mapExpr sym f $ simInO bundle
    simInP' <- PT.mapExpr sym f $ simInP bundle
    simOutO' <- PT.mapExpr sym f $ simOutO bundle
    simOutP' <- PT.mapExpr sym f $ simOutP bundle
    return $ SimBundle simInO' simInP' simOutO' simOutP'

instance PT.ExprMappable sym (MemCell sym arch w) where
  mapExpr sym f (MemCell ptr w) = do
    ptr' <- mapExprPtr sym f ptr
    return $ MemCell ptr' w

instance OrdF (W4.SymExpr sym) => PT.ExprMappable sym (MemCells sym arch w) where
  mapExpr sym f (MemCells cells) = do
    maps <- forM (M.toList cells) $ \(cell, p) -> do
      cell' <- PT.mapExpr sym f cell
      p' <- f p
      return $ MemCells $ M.singleton cell' p'
    foldM (mergeMemCells sym) (MemCells M.empty) maps


