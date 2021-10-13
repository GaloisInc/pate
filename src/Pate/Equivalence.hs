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
  ( StatePredSpec
  , EquivRelation(..)
  , MemEquivRelation(..)
  , applyMemEquivRelation
  , RegEquivRelation(..)
  , EquivalenceStatus(..)
  , weakenEquivRelation
  , getPostcondition
  , getPrecondition
  , impliesPrecondition
  , impliesPostcondPred
  , memPredPre
  , equalValuesIO
  , registerEquivalence
  , stateEquivalence
  , memEqAtRegion
  , memEqOutsideRegion
  , statePredPre
  ) where

import           Control.Lens hiding ( op, pre )
import           Control.Monad ( foldM )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Map ( Map )
import qualified Data.Map as M
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import qualified Data.Set as S
import           GHC.Stack ( HasCallStack )
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import           What4.ExprHelpers
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES

data EquivalenceStatus =
    Equivalent
  | Inequivalent
  | ConditionallyEquivalent
  | Errored String
  deriving (Show)

instance Semigroup EquivalenceStatus where
  Errored err <> _ = Errored err
  _ <> Errored err = Errored err
  Inequivalent <> _ = Inequivalent
  _ <> Inequivalent = Inequivalent
  ConditionallyEquivalent <> _ = ConditionallyEquivalent
  _ <> ConditionallyEquivalent = ConditionallyEquivalent
  Equivalent <> Equivalent = Equivalent

instance Monoid EquivalenceStatus where
  mempty = Equivalent

type StatePredSpec sym arch = SimSpec sym arch (PES.StatePred sym arch)

regPredAt ::
  W4.IsExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  MM.ArchReg arch tp ->
  PES.StatePred sym arch -> W4.Pred sym
regPredAt sym reg stPred  = case M.lookup (Some reg) (PES.predRegs stPred)  of
  Just p -> p
  Nothing -> W4.falsePred sym

---------------------------------------
-- Equivalence relations

-- The state predicates define equality, meant to be guarded by a 'PES.StatePred' which
-- defines the domain that the equality holds over

-- | Check if two memory cells are equivalent in the original and patched
-- program states.  The comparisons are done as bitvectors.  The 'CLM.LLVMPtr'
-- is a single bitvector of the necessary width (i.e., it can be larger than
-- pointer sized).
--
-- Note that this works at the level of bytes.
newtype MemEquivRelation sym arch =
  MemEquivRelation
    { memEquivCellCond :: forall w. PMC.MemCell sym arch w -> IO (W4.Pred sym) }


applyMemEquivRelation ::
  W4.IsExprBuilder sym =>
  sym ->
  MemEquivRelation sym arch ->
  PMC.MemCell sym arch w ->
  CLM.LLVMPtr sym (8 W4.* w) ->
  CLM.LLVMPtr sym (8 W4.* w) ->
  IO (W4.Pred sym)
applyMemEquivRelation sym memEq cell ptr1 ptr2 =
  impM sym (memEquivCellCond memEq cell) (MT.llvmPtrEq sym ptr1 ptr2)

-- | Check if two register values are the equivalent in the original and patched
-- program states.
newtype RegEquivRelation sym arch =
  RegEquivRelation { applyRegEquivRelation :: (forall tp. MM.ArchReg arch tp -> PSR.MacawRegEntry sym tp -> PSR.MacawRegEntry sym tp -> IO (W4.Pred sym)) }

-- | The equivalence relation specifies how (symbolic) values in the original
-- program must relate to (symbolic) values in the patched program.
--
-- The 'EquivalenceRelation' must be paired with a 'PES.StatePred' to be useful; the
-- 'PES.StatePred' tells the verifier which pieces of program state (registers and
-- memory locations) must be equivalent under the 'EquivRelation'.
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
  PA.HasDedicatedRegister arch ->
  sym ->
  RegEquivRelation sym arch
registerEquivalence hdr sym = RegEquivRelation $ \r vO vP -> do
  case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return $ W4.truePred sym
    PRe.RegSP -> do
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
  PA.HasDedicatedRegister arch ->
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  EquivRelation sym arch
stateEquivalence hdr sym stackRegion =
  let
    isStackCell cell = do
      let CLM.LLVMPointer region _ = PMC.cellPtr cell
      W4.natEq sym region stackRegion

    memEq = MemEquivRelation $ \cell -> isStackCell cell >>= W4.notPred sym
    stackEq = MemEquivRelation isStackCell
  in EquivRelation (registerEquivalence hdr sym) stackEq memEq

-- | Resolve a domain predicate and equivalence relation into a precondition
getPrecondition ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  PES.StatePred sym arch ->
  IO (W4.Pred sym)
getPrecondition sym stackRegion bundle eqRel stPred = do
  statePredPre sym stackRegion (simInO bundle) (simInP bundle) eqRel stPred

-- | True if the first precondition implies the second under the given
-- equivalence relation
impliesPrecondition ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PES.StatePred sym arch ->
  PES.StatePred sym arch ->
  IO (W4.Pred sym)  
impliesPrecondition sym stackRegion inO inP eqRel stPredAsm stPredConcl = do
  asm <- statePredPre sym stackRegion inO inP eqRel stPredAsm
  concl <- statePredPre sym stackRegion inO inP eqRel stPredConcl

  W4.impliesPred sym asm concl

impliesPostcondPred ::
  forall sym arch s st fs.
  sym ~ W4B.ExprBuilder s st fs =>
  PA.ValidArch arch =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  PPa.PatchPair (SimState sym arch) ->
  -- | assumed (i.e. stronger) post-condition
  StatePredSpec sym arch ->
  -- | implies (i.e. weaker) post-condition
  StatePredSpec sym arch ->
  IO (W4.Pred sym)  
impliesPostcondPred sym (PPa.PatchPair stO stP) stPredAsmSpec stPredConclSpec = do
  (precondAsm, stPredAsm) <- bindSpec sym stO stP stPredAsmSpec
  (precondConcl, stPredConcl) <- bindSpec sym stO stP stPredConclSpec
  regImp <- allPreds sym =<< mapM (getReg stPredAsm) (M.assocs (PES.predRegs stPredConcl))
  let
    stackCells = S.toList $ PEM.memPredCells (PES.predStack stPredAsm) <> PEM.memPredCells (PES.predStack stPredConcl)
    memCells = S.toList $ PEM.memPredCells (PES.predMem stPredAsm) <> PEM.memPredCells (PES.predMem stPredConcl)
  stackImp <- allPreds sym =<< mapM (getMem (PES.predStack stPredAsm) (PES.predStack stPredConcl)) stackCells
  globalImp <- allPreds sym =<< mapM (getMem (PES.predMem stPredAsm) (PES.predMem stPredConcl)) memCells
  allImps <- allPreds sym [precondConcl, regImp, stackImp, globalImp]
  W4.impliesPred sym precondAsm allImps
  where
    getMem ::
      PEM.MemPred sym arch ->
      PEM.MemPred sym arch ->
      (Some (PMC.MemCell sym arch)) ->
      IO (W4.Pred sym)
    getMem memAsm memConcl (Some cell) = do
     mAsm <- PEM.memPredAt sym memAsm cell
     mConcl <- PEM.memPredAt sym memConcl cell
     W4.impliesPred sym mAsm mConcl
      
    getReg ::
      PES.StatePred sym arch ->
      (Some (MM.ArchReg arch), W4.Pred sym) ->
      IO (W4.Pred sym)
    getReg stPredAsm (Some r, p) =
      W4.impliesPred sym (regPredAt sym r stPredAsm) p

-- | Resolve a domain predicate and equivalence relation into a postcondition and associated
-- structured equivalence relation (for reporting counterexamples)
getPostcondition ::
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MT.UndefinedPtrOps sym (MM.ArchAddrWidth arch) ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  PES.StatePred sym arch ->
  IO (EquivRelation sym arch, W4.Pred sym)
getPostcondition sym undef bundle eqRel stPred = do
  post <- statePredPost sym undef (simOutO bundle) (simOutP bundle) eqRel stPred
  return (weakenEquivRelation sym stPred eqRel, post)

-- | Weaken an equivalence relation to be conditional on exactly this predicate.
-- This is meant to be used for reporting only.
weakenEquivRelation ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  PES.StatePred sym arch ->
  EquivRelation sym arch ->
  EquivRelation sym arch
weakenEquivRelation sym stPred eqRel =
  let
    regsFn = RegEquivRelation $ \r v1 v2 -> do
      case M.lookup (Some r) (PES.predRegs stPred) of
        Just cond ->
          impM sym (return cond) $
            applyRegEquivRelation (eqRelRegs eqRel) r v1 v2
        Nothing -> return $ W4.truePred sym
    stackFn = MemEquivRelation $ \cell -> do
      cond' <- PEM.memPredAt sym (PES.predStack stPred) cell
      cond <- memEquivCellCond (eqRelStack eqRel) cell
      W4.andPred sym cond cond'
    memFn = MemEquivRelation $ \cell -> do
      cond' <- PEM.memPredAt sym (PES.predMem stPred) cell
      cond <- memEquivCellCond (eqRelMem eqRel) cell
      W4.andPred sym cond cond'
  in EquivRelation regsFn stackFn memFn

-- | Compute a predicate that is true iff the output states are equal according to
-- the given 'MemEquivRelation' at the locations defined by the given 'PEM.MemPred'
memPredPost ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MT.UndefinedPtrOps sym (MM.ArchAddrWidth arch) ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemPred sym arch ->
  IO (W4.Pred sym)
memPredPost sym undef outO outP memEq memPred = do
  iteM sym (return $ (PEM.memPredPolarity memPred))
    (positiveMemPredPost sym undef stO stP memEq memPred) negativePolarity
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
      impM sym (PEM.memPredAt sym memPred cell) $
        resolveCellPostEquiv sym undef stO stP memEq cell cond

    -- | For the negative case, we need to consider the domain of the state itself -
    -- we assure that all writes are equivalent when they have not been excluded
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      footO <- MT.traceFootprint sym (MT.memSeq $ memO)
      footP <- MT.traceFootprint sym (MT.memSeq $ memP)
      let foot = S.union footO footP
      footCells <- PEM.memPredToList <$> PEM.footPrintsToPred sym foot (W4.falsePred sym)
      foldr (\(Some cell, cond) -> andM sym (resolveCell cell cond)) (return $ W4.truePred sym) footCells

positiveMemPredPost ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MT.UndefinedPtrOps sym (MM.ArchAddrWidth arch) ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemPred sym arch ->
  IO (W4.Pred sym)
positiveMemPredPost sym undef stO stP memEq memPred = do
  let
    memCells = PEM.memPredToList memPred
    resolveCellPos = resolveCellPostEquiv sym undef stO stP memEq
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells

-- | Assert equality on two memory states by stating that their underlying
-- representations are equal at the given cells (without respect to how the memory
-- model would resolve those cells as pointers)
positiveMemPredPre ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemPred sym arch ->
  IO (W4.Pred sym)
positiveMemPredPre sym stO stP memEq memPred = do
  let
    memCells = PEM.memPredToList memPred
    resolveCellPos = resolveCellPreEquiv sym stO stP memEq
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells


resolveCellPreEquiv ::
  forall sym arch w.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellPreEquiv sym stO stP eqRel cell@(PMC.MemCell{}) cond =
  impM sym (return cond) $
  impM sym (memEquivCellCond eqRel cell) $
  MT.memEqAt sym (simMem stO) (simMem stP) (PMC.cellPtr cell) (PMC.cellWidth cell)

resolveCellPostEquiv ::
  forall sym arch w.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MT.UndefinedPtrOps sym (MM.ArchAddrWidth arch) ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellPostEquiv sym _undef stO stP eqRel cell@(PMC.MemCell{}) cond =
  impM sym (return cond) $
  impM sym (memEquivCellCond eqRel cell) $
  MT.memByteEqAt sym (simMem stO) (simMem stP) (PMC.cellPtr cell) (PMC.cellWidth cell)


-- | Compute a precondition that is sufficiently strong to imply the given
-- equivalence relation on the given domain for the given input state
-- This predicate is meant to be *assumed* true.
memPredPre ::
  forall sym arch.
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemPred sym arch ->
  IO (W4.Pred sym)
memPredPre sym memEqRegion inO inP memEq memPred  = do
  iteM sym (return $ (PEM.memPredPolarity memPred))
    (positiveMemPredPre sym stO stP memEq memPred) negativePolarity
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
          fresh <- PMC.readMemCellChunk sym memP cell
          mem' <- PMC.writeMemCellChunk sym mem cell fresh
          mem'' <- W4.baseTypeIte sym cond (MT.memArr mem') (MT.memArr mem)
          return $ mem { MT.memArr = mem'' }

    -- | For the negative case, we assume that the patched trace is equivalent
    -- to the original trace with arbitrary modifications to excluded addresses
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') memO (PEM.memPredToList memPred)
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
  W4.SymNat sym ->
  MemRegionEquality sym arch
memEqOutsideRegion sym region = MemRegionEquality $ \mem1 mem2 -> do
  iRegion <- W4.natToInteger sym region
  mem1Stack <- W4.arrayLookup sym (MT.memArr mem1) (Ctx.singleton iRegion)
  mem2' <- W4.arrayUpdate sym (MT.memArr mem2) (Ctx.singleton iRegion) mem1Stack
  W4.isEq sym (MT.memArr mem1) mem2'


-- | Memory states are equivalent in the given region.
memEqAtRegion ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  MemRegionEquality sym arch
memEqAtRegion sym stackRegion = MemRegionEquality $ \mem1 mem2 -> do
  iStackRegion <- W4.natToInteger sym stackRegion
  mem1Stack <- W4.arrayLookup sym (MT.memArr mem1) (Ctx.singleton iStackRegion)
  mem2Stack <- W4.arrayLookup sym (MT.memArr mem2) (Ctx.singleton iStackRegion)
  W4.isEq sym mem1Stack mem2Stack

regPredRel ::
  forall sym arch.
  W4.IsExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
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
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PES.StatePred sym arch ->
  IO (W4.Pred sym)
statePredPre sym stackRegion inO inP eqRel stPred  = do
  let
    stO = simInState inO
    stP = simInState inP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (PES.predRegs stPred)
    stacksEq =
      memPredPre sym (memEqAtRegion sym stackRegion) inO inP (eqRelStack eqRel) (PES.predStack stPred)
    memEq =
      memPredPre sym (memEqOutsideRegion sym stackRegion) inO inP (eqRelMem eqRel) (PES.predMem stPred)
  andM sym regsEq (andM sym stacksEq memEq)

statePredPost ::
  CB.IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MT.UndefinedPtrOps sym (MM.ArchAddrWidth arch) ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PES.StatePred sym arch ->
  IO (W4.Pred sym)
statePredPost sym undef outO outP eqRel stPred = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (PES.predRegs stPred)
    stacksEq = memPredPost sym undef outO outP (eqRelStack eqRel) (PES.predStack stPred)
    memEq = memPredPost sym undef outO outP (eqRelMem eqRel) (PES.predMem stPred)
  andM sym regsEq (andM sym stacksEq memEq)
