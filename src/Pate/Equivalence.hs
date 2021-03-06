{-|
Module           : Pate.Equivalence
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Definitions for equality over crucible input and output states.
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

module Pate.Equivalence
  ( MemPred(..)
  , StatePred(..)
  , StatePredSpec
  , EquivRelation(..)
  , MemEquivRelation(..)
  , RegEquivRelation(..)

  , muxStatePred
  , mapMemPred
  , memPredTrue
  , memPredFalse
  , weakenEquivRelation
  , getPostcondition
  , getPrecondition
  , impliesPrecondition
  , footPrintsToPred
  , addFootPrintsToPred
  , statePredFalse
  , memPredToList
  , listToMemPred
  , memPredPre
  , equalValuesIO
  , registerEquivalence
  , stateEquivalence
  , memEqAtRegion
  , memEqOutsideRegion
  ) where

import           GHC.Stack ( HasCallStack )
import           GHC.TypeNats

import           Control.Monad ( forM, foldM )
import           Control.Lens hiding ( op, pre )
import           Control.Monad.IO.Class ( liftIO )

import           Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (catMaybes)

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.Map as MapF

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT

import qualified What4.Interface as W4

import qualified Pate.Arch as PA
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT
import           What4.ExprHelpers

---------------------------------------------
-- Memory predicate

data MemPred sym arch =
    MemPred
      { memPredLocs :: MapF.MapF W4.NatRepr (PMC.MemCells sym arch)
      -- ^ predicate status at these locations according to polarity
      , memPredPolarity :: W4.Pred sym
      -- ^ if true, then predicate is true at exactly the locations
      -- if false, then predicate is true everywhere but these locations.
      -- Currently this is always concrete, but alternate strategies
      -- for computing pre-domains may decide to use symbolic polarities,
      -- and there is no fundamental reason to exclude this case.
      }

-- | Map the internal 'PMC.MemCells' representing the locations of a 'MemPred', preserving
-- its polarity.
mapMemPred ::
  forall sym arch m.
  Monad m =>
  W4.IsExprBuilder sym =>
  MemPred sym arch ->
  (forall w. 1 <= w => PMC.MemCell sym arch w -> W4.Pred sym -> m (W4.Pred sym)) ->
  m (MemPred sym arch)
mapMemPred memPred f = do
  let
    f' :: (forall w. PMC.MemCell sym arch w -> W4.Pred sym -> m (Maybe (W4.Pred sym)))
    f' cell@(PMC.MemCell{}) p = do
      p' <- f cell p
      case W4.asConstantPred p' of
        Just False -> return Nothing
        _ -> return $ Just p'
  locs <- TF.traverseF (\(PMC.MemCells cells) -> PMC.MemCells <$> M.traverseMaybeWithKey f' cells) (memPredLocs memPred)
  return $ memPred { memPredLocs = locs }


memPredToList ::
  MemPred sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
memPredToList memPred =
  concat $
  map (\(MapF.Pair _ (PMC.MemCells cells)) -> map (\(cell, p) -> (Some cell, p)) $ M.toList cells) $
  MapF.toList (memPredLocs memPred)

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

---------------------------------------------
-- State predicate

data StatePred sym arch =
  StatePred
    { predRegs :: Map (Some (MM.ArchReg arch)) (W4.Pred sym)
    -- ^ predicate is considered false on missing entries
    , predStack :: MemPred sym arch
    , predMem :: MemPred sym arch
    }

type StatePredSpec sym arch = SimSpec sym arch (StatePred sym arch)

muxStatePred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  W4.Pred sym ->
  StatePred sym arch ->
  StatePred sym arch ->
  IO (StatePred sym arch)
muxStatePred sym p predT predF = case W4.asConstantPred p of
  Just True -> return predT
  Just False -> return predF
  _ -> do
    notp <- W4.notPred sym p
    regs <- M.mergeA
      (M.traverseMissing (\_ pT -> W4.andPred sym pT p))
      (M.traverseMissing (\_ pF -> W4.andPred sym pF notp)) 
      (M.zipWithAMatched (\_ p1 p2 -> W4.baseTypeIte sym p p1 p2))
      (predRegs predT)
      (predRegs predF)  
    stack <- muxMemPred sym p (predStack predT) (predStack predF)
    mem <- muxMemPred sym p (predMem predT) (predMem predF)
    return $ StatePred regs stack mem

statePredFalse :: W4.IsExprBuilder sym => sym -> StatePred sym arch
statePredFalse sym = StatePred M.empty (memPredFalse sym) (memPredFalse sym)

---------------------------------------
-- Equivalence relations

-- The state predicates define equality, meant to be guarded by a 'StatePred' which
-- defines the domain that the equality holds over


newtype MemEquivRelation sym arch =
  MemEquivRelation { applyMemEquivRelation :: (forall w. PMC.MemCell sym arch w -> CLM.LLVMPtr sym (8 W4.* w) -> CLM.LLVMPtr sym (8 W4.* w) -> IO (W4.Pred sym)) }


newtype RegEquivRelation sym arch =
  RegEquivRelation { applyRegEquivRelation :: (forall tp. MM.ArchReg arch tp -> PSR.MacawRegEntry sym tp -> PSR.MacawRegEntry sym tp -> IO (W4.Pred sym)) }


data EquivRelation sym arch =
  EquivRelation
    { eqRelRegs :: RegEquivRelation sym arch
    , eqRelStack :: MemEquivRelation sym arch
    , eqRelMem :: MemEquivRelation sym arch
    }

equalValuesIO ::
  HasCallStack =>
  W4.IsExprBuilder sym =>
  sym ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp' ->
  IO (W4.Pred sym)
equalValuesIO sym entry1 entry2 = case (PSR.macawRegRepr entry1, PSR.macawRegRepr entry2) of
  (CLM.LLVMPointerRepr w1, CLM.LLVMPointerRepr w2) ->
    case testEquality w1 w2 of
      Just Refl -> liftIO $ MT.llvmPtrEq sym (PSR.macawRegValue entry1) (PSR.macawRegValue entry2)
      Nothing -> return $ W4.falsePred sym
  (CT.BoolRepr, CT.BoolRepr) -> liftIO $ W4.isEq sym (PSR.macawRegValue entry1) (PSR.macawRegValue entry2)
  (CT.StructRepr Ctx.Empty, CT.StructRepr Ctx.Empty) -> return (W4.truePred sym)
  (tp1, tp2) -> error ("equalValues: unsupported types: " ++ show (tp1, tp2))

-- | Base register equivalence relation. Equates all registers, except the instruction pointer.
-- Explicitly ignores the region of the stack pointer register, as this is checked elsewhere.
registerEquivalence ::
  forall sym arch.
  PA.ValidArch arch =>
  W4.IsSymExprBuilder sym =>
  sym ->
  RegEquivRelation sym arch
registerEquivalence sym = RegEquivRelation $ \r vO vP -> do
  case PT.registerCase (PSR.macawRegRepr vO) r of
    PT.RegIP -> return $ W4.truePred sym
    PT.RegSP -> do
      let
        CLM.LLVMPointer _ offO = PSR.macawRegValue vO
        CLM.LLVMPointer _ offP = PSR.macawRegValue vP
      W4.isEq sym offO offP
    _ -> equalValuesIO sym vO vP

-- | Base state equivalence relation. Requires pointer equality at all memory cells, where
-- stack equality on non-stack cells is trivially true, and memory equality on stack
-- cells is trivially true.
stateEquivalence ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  -- | stack memory region
  W4.SymExpr sym W4.BaseNatType ->
  EquivRelation sym arch
stateEquivalence sym stackRegion =
  let
    isStackCell cell = do
      let CLM.LLVMPointer region _ = PMC.cellPtr cell
      W4.isEq sym region stackRegion

    memEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell >>= W4.notPred sym) $
        MT.llvmPtrEq sym vO vP

    stackEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell) $
        MT.llvmPtrEq sym vO vP
  in EquivRelation (registerEquivalence sym) stackEq memEq

-- | Resolve a domain predicate and equivalence relation into a precondition
getPrecondition ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymExpr sym W4.BaseNatType ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
getPrecondition sym stackRegion bundle eqRel stPred = do
  statePredPre sym stackRegion (simInO bundle) (simInP bundle) eqRel stPred

-- | True if the first precondition implies the second under the given
-- equivalence relation
impliesPrecondition ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymExpr sym W4.BaseNatType ->
  SimInput sym arch PT.Original ->
  SimInput sym arch PT.Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)  
impliesPrecondition sym stackRegion inO inP eqRel stPredAsm stPredConcl = do
  asm <- statePredPre sym stackRegion inO inP eqRel stPredAsm
  concl <- statePredPre sym stackRegion inO inP eqRel stPredConcl
  W4.impliesPred sym asm concl

-- | Resolve a domain predicate and equivalence relation into a postcondition and associated
-- structured equivalence relation (for reporting counterexamples)
getPostcondition ::
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  StatePred sym arch ->  
  IO (EquivRelation sym arch, W4.Pred sym)
getPostcondition sym bundle eqRel stPred = do
  post <- statePredPost sym (simOutO bundle) (simOutP bundle) eqRel stPred
  return (weakenEquivRelation sym stPred eqRel, post)

-- | Weaken an equivalence relation to be conditional on exactly this predicate.
-- This is meant to be used for reporting only.
weakenEquivRelation ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  StatePred sym arch ->
  EquivRelation sym arch ->
  EquivRelation sym arch
weakenEquivRelation sym stPred eqRel =
  let
    regsFn = RegEquivRelation $ \r v1 v2 -> do
      case M.lookup (Some r) (predRegs stPred) of
        Just cond ->
          impM sym (return cond) $
            applyRegEquivRelation (eqRelRegs eqRel) r v1 v2
        Nothing -> return $ W4.truePred sym
    stackFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (memPredAt sym (predStack stPred) cell) $
        applyMemEquivRelation (eqRelStack eqRel) cell v1 v2
    memFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (memPredAt sym (predMem stPred) cell) $
        applyMemEquivRelation (eqRelMem eqRel) cell v1 v2
  in EquivRelation regsFn stackFn memFn

-- | Compute a predicate that is true iff the output states are equal according to
-- the given 'MemEquivRelation' at the locations defined by the given 'MemPred'
memPredPost ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch PT.Original ->
  SimOutput sym arch PT.Patched ->
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
memPredPost sym outO outP memEq memPred = do
  iteM sym (return $ (memPredPolarity memPred))
    (positiveMemPred sym stO stP memEq memPred) negativePolarity
  where
    stO = simOutState outO
    stP = simOutState outP
    
    memO = simOutMem outO
    memP = simOutMem outP

    -- | Cell equivalence that is conditional on whether or not this
    -- cell is in the domain of the given predicate
    resolveCell ::
      PMC.MemCell sym arch w ->
      W4.Pred sym ->
      IO (W4.Pred sym)
    resolveCell cell cond = do
      impM sym (memPredAt sym memPred cell) $
        resolveCellEquiv sym stO stP memEq cell cond

    -- | For the negative case, we need to consider the domain of the state itself -
    -- we assure that all writes are equivalent when they have not been excluded
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      footO <- MT.traceFootprint sym (MT.memSeq $ memO)
      footP <- MT.traceFootprint sym (MT.memSeq $ memP)
      let foot = S.union footO footP
      footCells <- memPredToList <$> footPrintsToPred sym foot (W4.falsePred sym)
      foldr (\(Some cell, cond) -> andM sym (resolveCell cell cond)) (return $ W4.truePred sym) footCells

positiveMemPred :: 
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PT.Original ->
  SimState sym arch PT.Patched ->  
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
positiveMemPred sym stO stP memEq memPred = do
  let
    memCells = memPredToList memPred
    resolveCellPos = resolveCellEquiv sym stO stP memEq
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells

resolveCellEquiv ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PT.Original ->
  SimState sym arch PT.Patched ->  
  MemEquivRelation sym arch ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquiv sym stO stP eqRel cell cond = do
  val1 <- PMC.readMemCell sym (simMem stO) cell
  val2 <- PMC.readMemCell sym (simMem stP) cell
  impM sym (return cond) $ applyMemEquivRelation eqRel cell val1 val2


-- | Compute a precondition that is sufficiently strong to imply the given
-- equivalence relation on the given domain for the given input state
-- This predicate is meant to be *assumed* true.
memPredPre ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimInput sym arch PT.Original ->
  SimInput sym arch PT.Patched ->
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
memPredPre sym memEqRegion inO inP memEq memPred  = do
  iteM sym (return $ (memPredPolarity memPred))
    (positiveMemPred sym stO stP memEq memPred) negativePolarity
  where
    stO = simInState inO
    stP = simInState inP
    
    memO = simInMem inO
    memP = simInMem inP

    -- | Conditionally write a fresh value to the given memory location
    -- FIXME: update for when memory model supports regions
    freshWrite ::
      PMC.MemCell sym arch w ->
      W4.Pred sym ->
      MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
      IO (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))
    freshWrite cell@(PMC.MemCell{}) cond mem =
      case W4.asConstantPred cond of
        Just False -> return mem
        _ -> do
          fresh <- PMC.readMemCell sym memP cell
          --CLM.LLVMPointer _ original <- MT.readMemArr sym memO ptr repr
          --val <- W4.baseTypeIte sym cond fresh original
          mem' <- PMC.writeMemCell sym mem cell fresh
          mem'' <- W4.baseTypeIte sym cond (MT.memArr mem') (MT.memArr mem)
          return $ mem { MT.memArr = mem'' }

    -- | For the negative case, we assume that the patched trace is equivalent
    -- to the original trace with arbitrary modifications to excluded addresses
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') memO (memPredToList memPred)
      getRegionEquality memEqRegion mem' memP

newtype MemRegionEquality sym arch =
  MemRegionEquality
    { getRegionEquality ::
        MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
        MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
        IO (W4.Pred sym)
    }

-- | Memory states are equivalent everywhere but the given region.
memEqOutsideRegion ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.SymExpr sym W4.BaseNatType ->
  MemRegionEquality sym arch
memEqOutsideRegion sym region = MemRegionEquality $ \mem1 mem2 -> do
  mem1Stack <- W4.arrayLookup sym (MT.memArr mem1) (Ctx.singleton region)
  mem2' <- W4.arrayUpdate sym (MT.memArr mem2) (Ctx.singleton region) mem1Stack
  W4.isEq sym (MT.memArr mem1) mem2'


-- | Memory states are equivalent in the given region.
memEqAtRegion ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | stack memory region
  W4.SymExpr sym W4.BaseNatType ->
  MemRegionEquality sym arch
memEqAtRegion sym stackRegion = MemRegionEquality $ \mem1 mem2 -> do
  mem1Stack <- W4.arrayLookup sym (MT.memArr mem1) (Ctx.singleton stackRegion)
  mem2Stack <- W4.arrayLookup sym (MT.memArr mem2) (Ctx.singleton stackRegion)
  W4.isEq sym mem1Stack mem2Stack

regPredRel ::
  forall sym arch.
  W4.IsExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PT.Original ->
  SimState sym arch PT.Patched ->
  RegEquivRelation sym arch ->
  Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  IO (W4.Pred sym)
regPredRel sym stO stP regEquiv regPred  = do
  let
    regsO = simRegs stO
    regsP = simRegs stP
    regRel r p =
      impM sym (return p) $ applyRegEquivRelation regEquiv r (regsO ^. MM.boundValue r) (regsP ^. MM.boundValue r)
  foldr (\(Some r, p) -> andM sym (regRel r p)) (return $ W4.truePred sym) (M.toList regPred)

statePredPre ::
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymExpr sym W4.BaseNatType ->
  SimInput sym arch PT.Original ->
  SimInput sym arch PT.Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
statePredPre sym stackRegion inO inP eqRel stPred  = do
  let
    stO = simInState inO
    stP = simInState inP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (predRegs stPred) 
    stacksEq =
      memPredPre sym (memEqAtRegion sym stackRegion) inO inP (eqRelStack eqRel) (predStack stPred)
    memEq =
      memPredPre sym (memEqOutsideRegion sym stackRegion) inO inP (eqRelMem eqRel) (predMem stPred)
  andM sym regsEq (andM sym stacksEq memEq)

statePredPost ::
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch PT.Original ->
  SimOutput sym arch PT.Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
statePredPost sym outO outP eqRel stPred  = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (predRegs stPred) 
    stacksEq = memPredPost sym outO outP (eqRelStack eqRel) (predStack stPred) 
    memEq = memPredPost sym outO outP (eqRelMem eqRel) (predMem stPred) 
  andM sym regsEq (andM sym stacksEq memEq)

-----------------------------------------
-- ExprMappable instances

instance PEM.ExprMappable sym (MemPred sym arch) where
  mapExpr sym f memPred = do
    locs <- MapF.traverseWithKey (\_ -> PEM.mapExpr sym f) (memPredLocs memPred)
    pol <- f (memPredPolarity memPred)
    return $ MemPred locs pol

instance PEM.ExprMappable sym (StatePred sym arch) where
  mapExpr sym f stPred = do
    regs <- mapM f (predRegs stPred)
    stack <- PEM.mapExpr sym f (predStack stPred)
    mem <- PEM.mapExpr sym f (predMem stPred)
    return $ StatePred regs stack mem
