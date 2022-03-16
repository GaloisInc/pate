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
  ( DomainSpec
  , EquivRelation(..)
  , MemEquivRelation(..)
  , RegEquivRelation(..)
  , EquivalenceStatus(..)
  , MemRegionEquality(..)
  , getPostdomain
  , getPredomain
  , impliesPredomain
  , impliesPostdomainPred
  , memDomPre
  , stateEquivalence
  ) where

import           Control.Lens hiding ( op, pre )
import           Control.Monad ( foldM )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import qualified Data.Set as S
import           GHC.Stack ( HasCallStack )
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT
import           Lang.Crucible.Backend (IsSymInterface)

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import           What4.ExprHelpers
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED

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

-- | An 'PED.EquivalenceDomain' that is closed under a symbolic machine state via
-- 'SimSpec'.
-- In general, a 'SimSpec' serves as a lambda abstraction over the variables representing
-- the machine state in the subterms of any type (as defined by the term traversal
-- in 'Pate.ExprMappable'). In essence, this represents a function from a 'SimState' to
-- an 'PED.EquivalenceDomain' (applied via 'bindSpec').
--
-- The variables in a 'DomainSpec' are instantiated in two different contexts:
--    1. When used as an *assumed* pre-domain, variables are instantiated to the initial *free*
--       variables of the slice.
--    2. When used as a *target* post-domain, variables are instantiated to terms representing
--       the final values of the slice.
-- For example: a domain could say @r1[r2_O != 0, r2_P > 2]@ (i.e. register @r1@ is in the domain if
-- the value in @r2@ is nonzero in the original program and greater than two in the patched program).
-- A slice contains two major components: a fully symbolic initial state (i.e. a 'SimInput') and
-- a resulting final state (i.e. a 'SimOutput').
-- Assume the slice under analysis simply assigns @1@ to @r2@ in both programs.
--
-- When instantiated as a pre-domain, we simply assign r2_O and r2_P to the free variables
-- representing the initial state of the slice.
-- When instantiated as a post-domain, we instantiate @r2_O@ and @r2_P@ to @1@, resulting in
-- an 'PED.EquivalenceDomain' that looks like @r1[1 != 0, 1 > 2]@. Since this condition is false,
-- @r1@ is excluded from the resulting instantiated domain.

type DomainSpec sym arch = SimSpec sym arch (PED.EquivalenceDomain sym arch)



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
  MemEquivRelation { applyMemEquivRelation :: (forall w. PMC.MemCell sym arch w -> CLM.LLVMPtr sym (8 W4.* w) -> CLM.LLVMPtr sym (8 W4.* w) -> IO (W4.Pred sym)) }

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

    memEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell >>= W4.notPred sym) $
        MT.llvmPtrEq sym vO vP

    stackEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell) $
        MT.llvmPtrEq sym vO vP
  in EquivRelation (registerEquivalence hdr sym) stackEq memEq

-- | Resolve a domain predicate and equivalence relation into a precondition.
-- This resulting predicate is a conjunction asserting that each location is
-- initially equal in the given slice.
-- This intended to be assumed true for the purposes of
-- generating an equivalence problem.
-- The 'EquivRelation' defines the relation that holds on each location in the initial
-- machine state. Currently this is always exact equality, and can likely be
-- deprecated (see: https://github.com/GaloisInc/pate/issues/213)
getPredomain ::
  forall sym arch.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
getPredomain sym stackRegion bundle eqRel eqDom = do
  eqDomPre sym stackRegion (simInO bundle) (simInP bundle) eqRel eqDom

-- | True if the first precondition implies the second under the given
-- equivalence relation
impliesPredomain ::
  forall sym arch.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PED.EquivalenceDomain sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)  
impliesPredomain sym stackRegion inO inP eqRel domAsm domConcl = do
  asm <- eqDomPre sym stackRegion inO inP eqRel domAsm
  concl <- eqDomPre sym stackRegion inO inP eqRel domConcl
  W4.impliesPred sym asm concl

impliesPostdomainPred ::
  forall sym arch s st fs.
  sym ~ W4B.ExprBuilder s st fs =>
  PA.ValidArch arch =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  PPa.PatchPair (SimState sym arch) ->
  -- | assumed (i.e. stronger) post-condition
  DomainSpec sym arch ->
  -- | implies (i.e. weaker) post-condition
  DomainSpec sym arch ->
  IO (W4.Pred sym)  
impliesPostdomainPred sym (PPa.PatchPair stO stP) domAsmSpec domConclSpec = do
  (precondAsm, domAsm) <- bindSpec sym stO stP domAsmSpec
  (precondConcl, domConcl) <- bindSpec sym stO stP domConclSpec
  regImp <- allPreds sym =<< mapM (getReg (PED.eqDomainRegisters domAsm)) (PER.toList (PED.eqDomainRegisters domConcl))
  let
    stackCells = S.toList $ PEM.cells (PED.eqDomainStackMemory domAsm) <> PEM.cells (PED.eqDomainStackMemory domConcl)
    memCells = S.toList $ PEM.cells (PED.eqDomainGlobalMemory domAsm) <> PEM.cells (PED.eqDomainGlobalMemory domConcl)
  stackImp <- allPreds sym =<< mapM (getMem (PED.eqDomainStackMemory domAsm) (PED.eqDomainStackMemory domConcl)) stackCells
  globalImp <- allPreds sym =<< mapM (getMem (PED.eqDomainGlobalMemory domAsm) (PED.eqDomainGlobalMemory domConcl)) memCells
  allImps <- allPreds sym [precondConcl, regImp, stackImp, globalImp]
  W4.impliesPred sym precondAsm allImps
  where
    getMem ::
      PEM.MemoryDomain sym arch ->
      PEM.MemoryDomain sym arch ->
      (Some (PMC.MemCell sym arch)) ->
      IO (W4.Pred sym)
    getMem memAsm memConcl (Some cell) = do
     mAsm <- PEM.containsCell sym memAsm cell
     mConcl <- PEM.containsCell sym memConcl cell
     W4.impliesPred sym mAsm mConcl
      
    getReg ::
      PER.RegisterDomain sym arch ->
      (Some (MM.ArchReg arch), W4.Pred sym) ->
      IO (W4.Pred sym)
    getReg domAsm (Some r, p) =
      W4.impliesPred sym (PER.registerInDomain sym r domAsm) p

-- | Compute a predicate which asserts equality on the post-state
-- of the given 'SimBundle' with respect to the given 'PED.EquivalenceDomain'
-- (i.e. assert that the resulting machine states are equal on every location
-- covered by the domain).
-- This predicate is intended to be proven, rather than assumed. See
-- 'eqDomPre' for computing an assumed predicate from a pre-domain.
-- 'EquivRelation' is intended to abstract away the exact equivalence relation
-- used, however relations aside from exact equality are not well supported and
-- this will likely be deprecated (see https://github.com/GaloisInc/pate/issues/213)
getPostdomain ::
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (EquivRelation sym arch, W4.Pred sym)
getPostdomain sym bundle eqRel stPred = do
  post <- eqDomPost sym (simOutO bundle) (simOutP bundle) eqRel stPred
  return (weakenEquivRelation sym stPred eqRel, post)

-- | Weaken an equivalence relation to be conditional on exactly this domain.
-- This is meant to be used for reporting only.
-- To be deprecated: (see https://github.com/GaloisInc/pate/issues/213)
weakenEquivRelation ::
  W4.IsExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  PED.EquivalenceDomain sym arch ->
  EquivRelation sym arch ->
  EquivRelation sym arch
weakenEquivRelation sym eqDom eqRel =
  let
    regsFn = RegEquivRelation $ \r v1 v2 ->
      impM sym (return $ PER.registerInDomain sym r (PED.eqDomainRegisters eqDom)) $
        applyRegEquivRelation (eqRelRegs eqRel) r v1 v2
    stackFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (PEM.containsCell sym (PED.eqDomainStackMemory eqDom) cell) $
        applyMemEquivRelation (eqRelStack eqRel) cell v1 v2
    memFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (PEM.containsCell sym (PED.eqDomainGlobalMemory eqDom) cell) $
        applyMemEquivRelation (eqRelMem eqRel) cell v1 v2
  in EquivRelation regsFn stackFn memFn

-- | Compute a predicate that is true iff the output states are equal according to
-- the given 'MemEquivRelation' at the locations defined by the given 'PEM.MemPred'
memDomPost ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemoryDomain sym arch ->
  IO (W4.Pred sym)
memDomPost sym outO outP memEq memPred = do
  iteM sym (return $ (PEM.memDomainPolarity memPred))
    (positiveMemCells sym stO stP memEq (PEM.memDomainPred memPred)) negativePolarity
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
      impM sym (PEM.containsCell sym memPred cell) $
        resolveCellEquiv sym stO stP memEq cell cond

    -- | For the negative case, we need to consider the domain of the state itself -
    -- we assure that all writes are equivalent when they have not been excluded
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      footO <- MT.traceFootprint sym memO
      footP <- MT.traceFootprint sym memP
      let foot = S.union footO footP
      footCells <- PEM.toList <$> PEM.fromFootPrints sym foot (W4.falsePred sym)
      foldr (\(Some cell, cond) -> andM sym (resolveCell cell cond)) (return $ W4.truePred sym) footCells

-- | Compute a predicate that asserts that the two states are equivalent
-- with respect to the given 'PEM.MemCellPred'.
-- This is intended to be used for the 'PMC.MemCellPred' of a positive polarity 'PEM.MemoryDomain',
-- as it simply asserts that the states are equal on each cell in the given 'PMC.MemCellPred'.
positiveMemCells :: 
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PMC.MemCellPred sym arch ->
  IO (W4.Pred sym)
positiveMemCells sym stO stP memEq memPred = do
  let
    memCells = PMC.predToList memPred
    resolveCellPos = resolveCellEquiv sym stO stP memEq
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells

resolveCellEquiv ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquiv sym stO stP eqRel cell cond = do
  val1 <- PMC.readMemCell sym (MT.memState $ simMem stO) cell
  val2 <- PMC.readMemCell sym (MT.memState $ simMem stP) cell
  impM sym (return cond) $ applyMemEquivRelation eqRel cell val1 val2


-- | Compute a precondition that is sufficiently strong to imply the given
-- equivalence relation on the given domain for the given input state
-- This predicate is meant to be *assumed* true.
memDomPre ::
  forall sym arch.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  MemEquivRelation sym arch ->
  PEM.MemoryDomain sym arch ->
  IO (W4.Pred sym)
memDomPre sym memEqRegion inO inP memEq memPred  = do
  iteM sym (return $ (PEM.memDomainPolarity memPred))
    (positiveMemCells sym stO stP memEq (PEM.memDomainPred memPred)) negativePolarity
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
      MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
      IO (MT.MemTraceState sym (MM.ArchAddrWidth arch))
    freshWrite cell@(PMC.MemCell{}) cond mem =
      case W4.asConstantPred cond of
        Just False -> return mem
        _ -> do
          fresh <- PMC.readMemCell sym (MT.memState memP) cell
          --CLM.LLVMPointer _ original <- MT.readMemArr sym memO ptr repr
          --val <- W4.baseTypeIte sym cond fresh original
          PMC.writeMemCell sym cond mem cell fresh

    -- | For the negative case, we assume that the patched trace is equivalent
    -- to the original trace with arbitrary modifications to excluded addresses
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') (MT.memState memO) (PEM.toList memPred)
      getRegionEquality memEqRegion mem' (MT.memState memP)

newtype MemRegionEquality sym arch =
  MemRegionEquality
    { getRegionEquality ::
        MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
        MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
        IO (W4.Pred sym)
    }

-- | Compute a predicate that is true iff the two given states are equal
-- (up to 'RegEquivRelation') on the given 'PER.RegisterDomain'.
-- The 'RegEquivRelation' is currently always simple equality (see: https://github.com/GaloisInc/pate/issues/213)
regDomRel ::
  forall sym arch.
  W4.IsExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  RegEquivRelation sym arch ->
  PER.RegisterDomain sym arch ->
  IO (W4.Pred sym)
regDomRel sym stO stP regEquiv regDom  = do
  let
    regsO = simRegs stO
    regsP = simRegs stP
    regRel r p =
      impM sym (return p) $ applyRegEquivRelation regEquiv r (regsO ^. MM.boundValue r) (regsP ^. MM.boundValue r)
  foldr (\(Some r, p) -> andM sym (regRel r p)) (return $ W4.truePred sym) (PER.toList regDom)

eqDomPre ::
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  -- | stack memory region
  W4.SymNat sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
eqDomPre sym stackRegion inO inP eqRel eqDom  = do
  let
    stO = simInState inO
    stP = simInState inP
    
    regsEq = regDomRel sym stO stP (eqRelRegs eqRel) (PED.eqDomainRegisters eqDom)
    stacksEq =
      memDomPre sym (MemRegionEquality $ MT.memEqAtRegion sym stackRegion) inO inP (eqRelStack eqRel) (PED.eqDomainStackMemory eqDom)
    memEq =
      memDomPre sym (MemRegionEquality $ MT.memEqOutsideRegion sym stackRegion) inO inP (eqRelMem eqRel) (PED.eqDomainGlobalMemory eqDom)
  andM sym regsEq (andM sym stacksEq memEq)

eqDomPost ::
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  EquivRelation sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
eqDomPost sym outO outP eqRel stPred  = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
    regsEq = regDomRel sym stO stP (eqRelRegs eqRel) (PED.eqDomainRegisters stPred)
    stacksEq = memDomPost sym outO outP (eqRelStack eqRel) (PED.eqDomainStackMemory stPred)
    memEq = memDomPost sym outO outP (eqRelMem eqRel) (PED.eqDomainGlobalMemory stPred)
  andM sym regsEq (andM sym stacksEq memEq)
