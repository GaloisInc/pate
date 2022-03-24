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
  , MemoryCondition(..)
  , RegisterCondition(..)
  , StateCondition(..)
  , preCondPredicate
  , postCondPredicate
  , memPreCondToPred
  , memPostCondToPred
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

import qualified Pate.Panic as PP

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

-- | A flag for whether or not a given memory equality test should be inclusive or
-- exclusive to a specific region of memory. Currently this region is simply the stack region,
-- and represents whether or not an equality test should be considering *only* the stack, or
-- considering global (i.e. non-stack) memory.
data MemRegionEquality sym arch =
    -- | Memory is equal at all addresses in the region represented by the given Nat
    MemEqAtRegion (W4.SymNat sym)
    -- | Memory is equal at all addresses outside the region represented by the given Nat
  | MemEqOutsideRegion (W4.SymNat sym)

instance TestEquality (W4.SymExpr sym) => Eq (MemRegionEquality sym arch) where
  MemEqAtRegion r1 == MemEqAtRegion r2 = r1 == r2
  MemEqOutsideRegion r1 == MemEqOutsideRegion r2 = r1 == r2
  _ == _ = False

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


registerValuesEqual' ::
  forall sym arch tp.
  PA.ValidArch arch =>
  W4.IsSymExprBuilder sym =>
  PA.HasDedicatedRegister arch ->
  sym ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp -> 
  IO (W4.Pred sym)  
registerValuesEqual' hdr sym r vO vP =
  case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return $ W4.truePred sym
    PRe.RegSP -> do
      let
        CLM.LLVMPointer _ offO = PSR.macawRegValue vO
        CLM.LLVMPointer _ offP = PSR.macawRegValue vP
      W4.isEq sym offO offP
    _ -> equalValuesIO sym vO vP  

-- | This simply bundles up the necessary state elements necessary to resolve equality.
data EquivContext sym arch where
  EquivContext ::
    { eqCtxHDR :: PA.HasDedicatedRegister arch
    , eqCtxStackRegion :: W4.SymNat sym
    } -> EquivContext sym arch

-- | Equates 'MacawRegEntry' values with respect to a given register.
-- Always returns 'True' if given the instruction pointer.
-- Explicitly ignores the region of the stack pointer register, as this is checked elsewhere.
registerValuesEqual ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  EquivContext sym arch ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp ->
  IO (W4.Pred sym)
registerValuesEqual sym (EquivContext hdr _) r vO vP = registerValuesEqual' hdr sym r vO vP

-- | Resolve a domain predicate into a structured precondition.
-- This resulting condition is asserting that each location is
-- initially equal in the given slice.
-- It can be converted into a predicate with 'preCondPredicate'.
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
  IO (StateCondition sym arch)
getPredomain sym bundle eqCtx eqDom =
  eqDomPre sym (simInO bundle) (simInP bundle) eqCtx eqDom

-- | True if the first precondition implies the second
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
  asm <- eqDomPre sym inO inP eqCtx domAsm >>= preCondPredicate sym inO inP
  concl <- eqDomPre sym inO inP eqCtx domConcl >>= preCondPredicate sym inO inP
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

-- | Resolve a domain predicate into a structured precondition.
-- This resulting condition is asserting equality on the post-state
-- of the given 'SimBundle' with respect to the given 'PED.EquivalenceDomain'
-- (i.e. assert that the resulting machine states are equal on every location
-- covered by the domain).
-- It can be converted into a predicate with 'postCondPredicate'.
-- This predicate is intended to be proven, rather than assumed. See
-- 'eqDomPre' for computing an assumed predicate from a pre-domain.
getPostdomain ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StateCondition sym arch)
getPostdomain sym bundle eqCtx stPred =
  eqDomPost sym (simOutO bundle) (simOutP bundle) eqCtx stPred

-- | Flatten a structured 'MemoryCondition' representing a memory post-condition into
-- a single predicate.
memPostCondToPred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  MemoryCondition sym arch ->
  IO (W4.Pred sym)
memPostCondToPred sym memCond = do
  let preds = map snd $ PEM.toList $ memCondDomain memCond
  foldM (W4.andPred sym) (W4.truePred sym) preds

-- | Compute a structured 'MemoryCondition' that is true iff the output states are equal according to
-- the given 'MemRegionEquality' at the locations defined by the given 'PEM.MemPred'
memDomPost ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  MemRegionEquality sym arch ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  PEM.MemoryDomain sym arch ->
  IO (MemoryCondition sym arch)
memDomPost sym memEqRegion outO outP memPred = do
  muxMemCond sym (PEM.memDomainPolarity memPred)
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
    negativePolarity :: IO (MemoryCondition sym arch)
    negativePolarity = do
      footO <- MT.traceFootprint sym memO
      footP <- MT.traceFootprint sym memP
      let foot = S.union footO footP
      footCells <- PEM.fromFootPrints sym foot (W4.falsePred sym)
      MemoryCondition <$> PEM.traverseWithCell footCells resolveCell <*> pure memEqRegion


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
  IO (MemoryCondition sym arch)
positiveMemCells sym memEqRegion stO stP memPred = do
  let resolveCellPos = resolveCellEquiv sym memEqRegion stO stP
  memPred' <- PMC.traverseWithCell memPred resolveCellPos
  return $ MemoryCondition (PEM.MemoryDomain memPred' (W4.truePred sym)) memEqRegion

-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- The predicate is conditional on the region of the cell agreeing with
-- the given 'MemRegionEquality':
-- * for 'MemEqAtRegion' the given region must match the cell
--    (i.e. for cells outside the region the resulting predicate is always true).
-- * for 'MemEqOutsideRegion' the given region must *not* match the cell
--    (i.e. for cells in the region the resulting predicate is always true)
resolveCellEquiv ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquiv sym memEqRegion stO stP cell cond = do
  val1 <- PMC.readMemCell sym (MT.memState $ simMem stO) cell
  val2 <- PMC.readMemCell sym (MT.memState $ simMem stP) cell
  let CLM.LLVMPointer cellRegion _ = PMC.cellPtr cell
  isInRegionScope <- case memEqRegion of
    MemEqAtRegion atRegion -> W4.natEq sym cellRegion atRegion
    MemEqOutsideRegion outRegion -> W4.notPred sym =<< W4.natEq sym cellRegion outRegion
  impM sym (W4.andPred sym cond isInRegionScope) $ MT.llvmPtrEq sym val1 val2

-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- Trivially true when the given 'PMC.MemCell' covers the stack region.
resolveCellEquivMem ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquivMem sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqOutsideRegion stackRegion) stO stP cell cond

-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- Trivially true when the given 'PMC.MemCell' is outside the stack region.
resolveCellEquivStack ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch PBi.Original ->
  SimState sym arch PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquivStack sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqAtRegion stackRegion) stO stP cell cond


-- | Structurally equivalent to a 'PEM.MemoryDomain', however the predicates
-- relate to equality on the given cells.
-- Note in the case of a negative polarity precondition, this isn't quite true,
-- since there is not a pointwise assertion for equality. Instead the predicate
-- is simply the condition under which that cell should be excluded from the
-- assumed initial equality.
data MemoryCondition sym arch = MemoryCondition
  { memCondDomain :: PEM.MemoryDomain sym arch
    -- | the region equality used to derive the predicates in the domain
    -- this is only needed to derive the final predicate when this condition represents an
    -- exclusive (i.e. negative polarity) precondition
  , memCondRegEq :: MemRegionEquality sym arch
  }

muxMemCond ::
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  IO (MemoryCondition sym arch) ->
  IO (MemoryCondition sym arch) ->
  IO (MemoryCondition sym arch)
muxMemCond sym p fT fF = case W4.asConstantPred p of
  Just True -> fT
  Just False -> fF
  _ -> do
    MemoryCondition condT memEqT <- fT
    MemoryCondition condF memEqF <- fF
    if memEqT == memEqF then
      MemoryCondition <$> PEM.mux sym p condT condF <*> pure memEqT
    else PP.panic PP.Verifier "muxMemCond" ["Incompatible memory region conditions"]


-- | Flatten a structured 'MemoryCondition' representing a memory post-condition into
-- a single predicate.
-- We require the pre-states in order to construct the initial equality assumption
-- for an exclusive (i.e. negative polarity) condition.
memPreCondToPred ::
  forall sym arch.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  MemoryCondition sym arch ->
  IO (W4.Pred sym)
memPreCondToPred sym inO inP memCond  = do
  iteM sym (return $ PEM.memDomainPolarity $ memCondDomain memCond)
    positivePolarity negativePolarity
  where  
    memO = simInMem inO
    memP = simInMem inP

    positivePolarity :: IO (W4.Pred sym)
    positivePolarity = do
      let preds = map snd $ PEM.toList $ memCondDomain memCond
      foldM (W4.andPred sym) (W4.truePred sym) preds

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
      let cells = PEM.toList $ memCondDomain memCond
      let memEqRegion = memCondRegEq memCond
      mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') (MT.memState memO) cells
      getRegionEquality sym memEqRegion mem' (MT.memState memP)

-- | Compute a precondition that is sufficiently strong to imply equality
-- on the given domain for the given input state
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
  IO (MemoryCondition sym arch)
memDomPre sym memEqRegion inO inP memPred  = do
  muxMemCond sym (PEM.memDomainPolarity memPred)
    (positiveMemCells sym memEqRegion stO stP (PEM.memDomainPred memPred)) negativePolarity
  where
    stO = simInState inO
    stP = simInState inP

    -- | For the negative case, we simply collect the locations in the domain with their existing
    -- conditions
    negativePolarity :: IO (MemoryCondition sym arch)
    negativePolarity =
      return $ MemoryCondition (memPred { PEM.memDomainPolarity = W4.falsePred sym }) memEqRegion
    

-- | Compute a predicate that is true if the two memory states are exactly equal with respect to the given
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

newtype RegisterCondition sym arch =
  RegisterCondition { regCondDom :: PER.RegisterDomain sym arch }

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
  IO (RegisterCondition sym arch)
regDomRel hdr sym stO stP regDom  = do
  let regRel r p = do
        let vO = (simRegs stO) ^. MM.boundValue r
        let vP = (simRegs stP) ^. MM.boundValue r
        impM sym (return p) $ registerValuesEqual' hdr sym r vO vP
  RegisterCondition <$> PER.traverseWithReg regDom regRel

regCondToPred ::
  W4.IsSymExprBuilder sym =>
  sym ->
  RegisterCondition sym arch ->
  IO (W4.Pred sym)
regCondToPred sym regCond = do
  let preds = map snd $ PER.toList $ regCondDom regCond
  foldM (W4.andPred sym) (W4.truePred sym) preds

-- | A structured pre or post condition
data StateCondition sym arch = StateCondition
  { stRegCond :: RegisterCondition sym arch
  , stStackCond :: MemoryCondition sym arch
  , stMemCond :: MemoryCondition sym arch
  }

eqDomPre ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StateCondition sym arch)
eqDomPre sym inO inP (EquivContext hdr stackRegion) eqDom  = do
  let
    stO = simInState inO
    stP = simInState inP
    
  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters eqDom)
  stacksEq <-
    memDomPre sym (MemEqAtRegion stackRegion) inO inP (PED.eqDomainStackMemory eqDom)
  memEq <-
    memDomPre sym (MemEqOutsideRegion stackRegion) inO inP (PED.eqDomainGlobalMemory eqDom)
  return $ StateCondition regsEq stacksEq memEq

eqDomPost ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  SimOutput sym arch PBi.Original ->
  SimOutput sym arch PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StateCondition sym arch)
eqDomPost sym outO outP (EquivContext hdr stackRegion) stPred = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters stPred)
  stacksEq <- memDomPost sym (MemEqAtRegion stackRegion) outO outP (PED.eqDomainStackMemory stPred)
  memEq <- memDomPost sym (MemEqOutsideRegion stackRegion) outO outP (PED.eqDomainGlobalMemory stPred)
  return $ StateCondition regsEq stacksEq memEq

-- | Flatten a structured 'StateCondition' representing a pre-condition into
-- a single predicate.
preCondPredicate ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch PBi.Original ->
  SimInput sym arch PBi.Patched ->
  StateCondition sym arch ->
  IO (W4.Pred sym)
preCondPredicate sym inO inP stCond = do
  regsPred <- regCondToPred sym (stRegCond stCond)
  stackPred <- memPreCondToPred sym inO inP (stStackCond stCond)
  memPred <- memPreCondToPred sym inO inP (stMemCond stCond)
  W4.andPred sym regsPred stackPred >>= W4.andPred sym memPred

-- | Flatten a structured 'StateCondition' representing a post-condition into
-- a single predicate.
postCondPredicate ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  StateCondition sym arch ->
  IO (W4.Pred sym)
postCondPredicate sym stCond = do
  regsPred <- regCondToPred sym (stRegCond stCond)
  stackPred <- memPostCondToPred sym (stStackCond stCond)
  memPred <- memPostCondToPred sym (stMemCond stCond)
  W4.andPred sym regsPred stackPred >>= W4.andPred sym memPred
