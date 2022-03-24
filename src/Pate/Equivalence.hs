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
  , EquivalenceStatus(..)
  , MemRegionEquality(..)
  , getPostdomain
  , getPredomain
  , impliesPredomain
  , impliesPostdomainPred
  , memDomPre
  , eqDomPost
  , resolveCellEquiv
  , resolveCellEquivMem
  , resolveCellEquivStack
  , registerValuesEqual
  , EquivContext(..)
  , applyRegEquiv
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

-- | A flag for whether or not a given memory equality test should be relaxed or
-- exclusive to a specific region of memory (i.e. inclusive or exclusive of the stack)
data MemRegionEquality sym arch =
    MemEqAtRegion (W4.SymNat sym)
  | MemEqOutsideRegion (W4.SymNat sym)

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

-- | Equates register in a given state pair, except the instruction pointer.
-- Explicitly ignores the region of the stack pointer register, as this is checked elsewhere.
registerEquivalence ::
  forall sym arch tp.
  PA.ValidArch arch =>
  W4.IsSymExprBuilder sym =>
  PA.HasDedicatedRegister arch ->
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  MM.ArchReg arch tp ->
  IO (W4.Pred sym)
registerEquivalence hdr sym inO inP r = registerValuesEqual hdr sym r vO vP 
  where
    vO = (simRegs inO) ^. MM.boundValue r
    vP = (simRegs inP) ^. MM.boundValue r

-- | Equates 'MacawRegEntry' values with respect to a given register.
-- Ignores the instruction pointer.
-- Explicitly ignores the region of the stack pointer register, as this is checked elsewhere.
registerValuesEqual ::
  forall sym arch tp.
  PA.ValidArch arch =>
  W4.IsSymExprBuilder sym =>
  PA.HasDedicatedRegister arch ->
  sym ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp -> 
  IO (W4.Pred sym)  
registerValuesEqual hdr sym r vO vP =
  case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return $ W4.truePred sym
    PRe.RegSP -> do
      let
        CLM.LLVMPointer _ offO = PSR.macawRegValue vO
        CLM.LLVMPointer _ offP = PSR.macawRegValue vP
      W4.isEq sym offO offP
    _ -> equalValuesIO sym vO vP  

-- | Resolve a domain predicate and equivalence relation into a precondition.
-- This resulting predicate is a conjunction asserting that each location is
-- initially equal in the given slice.
-- This intended to be assumed true for the purposes of
-- generating an equivalence problem.
getPredomain ::
  forall sym arch.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
getPredomain sym bundle eqCtx eqDom =
  eqDomPre sym (simInO bundle) (simInP bundle) eqCtx eqDom

-- | True if the first precondition implies the second under the given
-- equivalence relation
impliesPredomain ::
  forall sym arch.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)  
impliesPredomain sym inO inP eqCtx domAsm domConcl = do
  asm <- eqDomPre sym inO inP eqCtx domAsm
  concl <- eqDomPre sym inO inP eqCtx domConcl
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
getPostdomain ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
getPostdomain sym bundle eqCtx stPred =
  eqDomPost sym (simOutO bundle) (simOutP bundle) eqCtx stPred

-- | Compute a predicate that is true iff the output states are equal according to
-- the given 'MemEquivRelation' at the locations defined by the given 'PEM.MemPred'
memDomPost ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  MemRegionEquality sym arch ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  PEM.MemoryDomain sym arch ->
  IO (W4.Pred sym)
memDomPost sym memEqRegion outO outP memPred = do
  iteM sym (return $ (PEM.memDomainPolarity memPred))
    (positiveMemCells sym memEqRegion stO stP (PEM.memDomainPred memPred)) negativePolarity
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
        resolveCellEquiv sym memEqRegion stO stP cell cond

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
  MemRegionEquality sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCellPred sym arch ->
  IO (W4.Pred sym)
positiveMemCells sym memEqRegion stO stP memPred = do
  let
    memCells = PMC.predToList memPred
    resolveCellPos = resolveCellEquiv sym memEqRegion stO stP
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells

resolveCellEquiv ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquiv sym memEqRegion stO stP cell cond = do
  val1 <- PMC.readMemCell sym (MT.memState $ simMem stO) cell
  val2 <- PMC.readMemCell sym (MT.memState $ simMem stP) cell
  let CLM.LLVMPointer region _ = PMC.cellPtr cell
  isInRegionScope <- case memEqRegion of
    MemEqAtRegion stackRegion -> W4.natEq sym region stackRegion
    MemEqOutsideRegion stackRegion -> W4.notPred sym =<< W4.natEq sym region stackRegion
  impM sym (W4.andPred sym cond isInRegionScope) $ MT.llvmPtrEq sym val1 val2


resolveCellEquivMem ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquivMem sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqOutsideRegion stackRegion) stO stP cell cond

resolveCellEquivStack ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquivStack sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqAtRegion stackRegion) stO stP cell cond

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
  PEM.MemoryDomain sym arch ->
  IO (W4.Pred sym)
memDomPre sym memEqRegion inO inP memPred  = do
  iteM sym (return $ (PEM.memDomainPolarity memPred))
    (positiveMemCells sym memEqRegion stO stP (PEM.memDomainPred memPred)) negativePolarity
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
      getRegionEquality sym memEqRegion mem' (MT.memState memP)

-- | Assert that the two memory states are exactly equal with respect to the given
-- type of region equality
getRegionEquality ::
  forall sym arch.
  W4.IsExprBuilder sym =>
  sym ->
  MemRegionEquality sym arch ->
  MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
  MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
  IO (W4.Pred sym)
getRegionEquality sym memEq memO memP = case memEq of
  MemEqAtRegion stackRegion -> MT.memEqAtRegion sym stackRegion memO memP
  MemEqOutsideRegion stackRegion -> MT.memEqOutsideRegion sym stackRegion memO memP

-- | Compute a predicate that is true iff the two given states are equal with respect to
-- the given 'PER.RegisterDomain'.
regDomRel ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  PA.HasDedicatedRegister arch ->
  sym ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PER.RegisterDomain sym arch ->
  IO (W4.Pred sym)
regDomRel hdr sym stO stP regDom  = do
  let regRel r p = impM sym (return p) $ registerEquivalence hdr sym stO stP r
  foldr (\(Some r, p) -> andM sym (regRel r p)) (return $ W4.truePred sym) (PER.toList regDom)

eqDomPre ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
eqDomPre sym inO inP (EquivContext hdr stackRegion) eqDom  = do
  let
    stO = simInState inO
    stP = simInState inP
    
    regsEq = regDomRel hdr sym stO stP (PED.eqDomainRegisters eqDom)
    stacksEq =
      memDomPre sym (MemEqAtRegion stackRegion) inO inP (PED.eqDomainStackMemory eqDom)
    memEq =
      memDomPre sym (MemEqOutsideRegion stackRegion) inO inP (PED.eqDomainGlobalMemory eqDom)
  andM sym regsEq (andM sym stacksEq memEq)

eqDomPost ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)
eqDomPost sym outO outP (EquivContext hdr stackRegion) stPred = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
    regsEq = regDomRel hdr sym stO stP (PED.eqDomainRegisters stPred)
    stacksEq = memDomPost sym (MemEqAtRegion stackRegion) outO outP (PED.eqDomainStackMemory stPred)
    memEq = memDomPost sym (MemEqOutsideRegion stackRegion) outO outP (PED.eqDomainGlobalMemory stPred)
  andM sym regsEq (andM sym stacksEq memEq)

-- | This simply bundles up the necessary state elements necessary to resolve equality.
data EquivContext sym arch where
  EquivContext ::
    { eqCtxHDR :: PA.HasDedicatedRegister arch
    , eqCtxStackRegion :: W4.SymNat sym
    } -> EquivContext sym arch

applyRegEquiv ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  EquivContext sym arch ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp ->
  IO (W4.Pred sym)
applyRegEquiv sym (EquivContext hdr _) r vO vP = registerValuesEqual hdr sym r vO vP
