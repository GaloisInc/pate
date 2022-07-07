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
  ( EquivalenceStatus(..)
  , MemRegionEquality(..)
  , getPostdomain
  , getPredomain
  , impliesPredomain
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
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import qualified Data.Set as S
import           GHC.Stack ( HasCallStack )
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT
import           Lang.Crucible.Backend (IsSymInterface)

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Register as PRe
import qualified Pate.Register.Traversal as PRt
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
  forall sym arch v.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StateCondition sym arch)
getPredomain sym bundle eqCtx eqDom =
  eqDomPre sym (simInO bundle) (simInP bundle) eqCtx eqDom

-- | True if the first precondition implies the second
impliesPredomain ::
  forall sym arch v.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch v PBi.Original ->
  SimInput sym arch v PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)  
impliesPredomain sym inO inP eqCtx domAsm domConcl = do
  asm <- eqDomPre sym inO inP eqCtx domAsm >>= preCondPredicate sym inO inP
  concl <- eqDomPre sym inO inP eqCtx domConcl >>= preCondPredicate sym inO inP
  W4.impliesPred sym asm concl

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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch {- ^ pre-domain for this slice -} ->
  PED.EquivalenceDomain sym arch {- ^ target post-domain -} ->
  IO (StateCondition sym arch)
getPostdomain sym bundle eqCtx domPre domPost =
  eqDomPost sym (simOutO bundle) (simOutP bundle) eqCtx domPre domPost

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
-- the given 'MemRegionEquality' at the locations defined by the given 'PEM.MemoryDomain'
-- post-domain.
-- Additionally takes a 'PEM.MemoryDomain' representing the assumed pre-domain, in order
-- to check for equality on any locations which were initially assumed to be unequal.
-- For the post-equality condition to hold, these locations must therefore either be
-- made equal by the slice, or excluded in the given post-domain.
memDomPost ::
  forall sym arch v.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  MemRegionEquality sym arch ->
  SimOutput sym arch v PBi.Original ->
  SimOutput sym arch v PBi.Patched ->
  PEM.MemoryDomain sym arch {- ^ pre-domain for this slice -} ->
  PEM.MemoryDomain sym arch {- ^ target post-domain -} ->
  IO (MemoryCondition sym arch)
memDomPost sym memEqRegion outO outP domPre domPost = do
  footO <- MT.traceFootprint sym memO
  footP <- MT.traceFootprint sym memP
  let foot = S.union footO footP
  footCells <- PEM.excludeFootPrints sym (S.filter (MT.isDir MT.Write) foot) domPre
  MemoryCondition <$> PEM.traverseWithCell footCells resolveCell <*> pure memEqRegion
  where
    stO = simOutState outO
    stP = simOutState outP
    
    memO = simOutMem outO
    memP = simOutMem outP

    -- | Cell equivalence that is conditional on whether or not this
    -- cell is in the target post-domain. If it is, then we read the
    -- contents of memory at the cell in the original and patched post-states
    -- and assert that the resulting values are equal.
    resolveCell ::
      PMC.MemCell sym arch w ->
      W4.Pred sym ->
      IO (W4.Pred sym)
    resolveCell cell cond = do
      impM sym (PEM.mayContainCell sym domPost cell) $
        resolveCellEquiv sym memEqRegion stO stP cell cond


-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- The predicate is conditional on the region of the cell agreeing with
-- the given 'MemRegionEquality':
-- * for 'MemEqAtRegion' the given region must match the cell
--    (i.e. for cells outside the region the resulting predicate is always true).
-- * for 'MemEqOutsideRegion' the given region must *not* match the cell
--    (i.e. for cells in the region the resulting predicate is always true)
resolveCellEquiv ::
  forall sym arch v w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquiv sym memEqRegion stO stP cell cond = do
  val1 <- PMC.readMemCell sym (simMem stO) cell
  val2 <- PMC.readMemCell sym (simMem stP) cell
  let CLM.LLVMPointer cellRegion _ = PMC.cellPtr cell
  isInRegionScope <- case memEqRegion of
    MemEqAtRegion atRegion -> W4.natEq sym cellRegion atRegion
    MemEqOutsideRegion outRegion -> W4.notPred sym =<< W4.natEq sym cellRegion outRegion
  impM sym (W4.andPred sym cond isInRegionScope) $ MT.llvmPtrEq sym val1 val2

-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- Trivially true when the given 'PMC.MemCell' covers the stack region.
resolveCellEquivMem ::
  forall sym arch v w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquivMem sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqOutsideRegion stackRegion) stO stP cell cond

-- | Compute a predicate that is true if the area of memory covered by the
-- given 'PMC.MemCell' is equivalent on the two given states.
-- Trivially true when the given 'PMC.MemCell' is outside the stack region.
resolveCellEquivStack ::
  forall sym arch v w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  EquivContext sym arch ->
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PMC.MemCell sym arch w ->
  W4.Pred sym {- ^ Additional pre-condition for the predicate -} ->
  IO (W4.Pred sym)
resolveCellEquivStack sym (EquivContext _ stackRegion) stO stP cell cond =
  resolveCellEquiv sym (MemEqAtRegion stackRegion) stO stP cell cond


-- | Structurally equivalent to a 'PEM.MemoryDomain', however the predicates
-- relate to equality on the given cells.
-- Note in the case of a precondition, this isn't quite true,
-- since there is not a pointwise assertion for equality. Instead the predicate
-- is simply the condition under which that cell should be excluded from the
-- assumed initial equality ( see 'memDomPre' and 'memPreCondToPred' )
data MemoryCondition sym arch = MemoryCondition
  { memCondDomain :: PEM.MemoryDomain sym arch
    -- | the region equality used to derive the predicates in the domain
    -- this is needed to derive the final predicate
  , memCondRegEq :: MemRegionEquality sym arch
  }

-- | Flatten a structured 'MemoryCondition' representing a memory pre-condition into
-- a single predicate.
-- We require the pre-states in order to construct the initial equality assumption.
-- Specifically we assume that the patched trace is equivalent
-- to the original trace with arbitrary modifications to excluded addresses
memPreCondToPred ::
  forall sym arch v.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimInput sym arch v PBi.Original ->
  SimInput sym arch v PBi.Patched ->
  MemoryCondition sym arch ->
  IO (W4.Pred sym)
memPreCondToPred sym inO inP memCond  = do
  let cells = PEM.toList $ memCondDomain memCond
  let memEqRegion = memCondRegEq memCond
  mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') (MT.memState memO) cells
  getRegionEquality sym memEqRegion mem' (MT.memState memP)
  where  
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
          fresh <- PMC.readMemCell sym memP cell
          --CLM.LLVMPointer _ original <- MT.readMemArr sym memO ptr repr
          --val <- W4.baseTypeIte sym cond fresh original
          PMC.writeMemCell sym cond mem cell fresh

-- | Compute a precondition that is sufficiently strong to imply equality
-- on the given domain
-- This predicate is meant to be *assumed* true.
-- Note that since there is not a pointwise assertion for equality, the
-- resulting condition is simply the condition under which that cell should be excluded from the
-- assumed initial equality
memDomPre ::
  forall sym arch.
  IsSymInterface sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  MemRegionEquality sym arch ->
  PEM.MemoryDomain sym arch ->
  IO (MemoryCondition sym arch)
memDomPre _sym memEqRegion memPred = return $ MemoryCondition memPred memEqRegion

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

-- | A mapping from registers to a predicate representing an equality condition for
-- that specific register.
-- The conjunction of these predicates represents the assumption (as a precondition)
-- or assertion (as a postcondition) that all of the registers are equal with respect
-- to some equivalence domain.
newtype RegisterCondition sym arch =
  RegisterCondition { regCondPreds :: MM.RegState (MM.ArchReg arch) (Const (W4.Pred sym)) }

-- | Compute a structured 'RegisterCondition'
-- where the predicate associated with each register
-- is true iff the register is equal in two given states (conditional on
-- the register being present in the given 'PER.RegisterDomain')
regDomRel ::
  forall sym arch v.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  PA.HasDedicatedRegister arch ->
  sym ->
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PER.RegisterDomain sym arch ->
  IO (RegisterCondition sym arch)
regDomRel hdr sym stO stP regDom  = RegisterCondition <$> do
  PRt.zipWithRegStatesM (simRegs stO) (simRegs stP) $ \r vO vP -> Const <$> do
    let p = PER.registerInDomain sym r regDom
    impM sym (return p) $ registerValuesEqual' hdr sym r vO vP


regCondToPred ::
  W4.IsSymExprBuilder sym =>
  sym ->
  RegisterCondition sym arch ->
  IO (W4.Pred sym)
regCondToPred sym regCond = do
  let preds = MM.regStateMap (regCondPreds regCond)
  MapF.foldrMWithKey (\_ (Const p) p' -> W4.andPred sym p p') (W4.truePred sym) preds

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
  SimInput sym arch v PBi.Original ->
  SimInput sym arch v PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StateCondition sym arch)
eqDomPre sym inO inP (EquivContext hdr stackRegion) eqDom  = do
  let
    stO = simInState inO
    stP = simInState inP
    
  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters eqDom)
  stacksEq <-
    memDomPre sym (MemEqAtRegion stackRegion) (PED.eqDomainStackMemory eqDom)
  memEq <-
    memDomPre sym (MemEqOutsideRegion stackRegion) (PED.eqDomainGlobalMemory eqDom)
  return $ StateCondition regsEq stacksEq memEq

eqDomPost ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  SimOutput sym arch v PBi.Original ->
  SimOutput sym arch v PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch {- ^ pre-domain for this slice -} ->
  PED.EquivalenceDomain sym arch {- ^ target post-domain -} ->
  IO (StateCondition sym arch)
eqDomPost sym outO outP (EquivContext hdr stackRegion) domPre domPost = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters domPost)
  stacksEq <- memDomPost sym (MemEqAtRegion stackRegion) outO outP (PED.eqDomainStackMemory domPre) (PED.eqDomainStackMemory domPost)
  memEq <- memDomPost sym (MemEqOutsideRegion stackRegion) outO outP (PED.eqDomainGlobalMemory domPre) (PED.eqDomainGlobalMemory domPost)
  return $ StateCondition regsEq stacksEq memEq

-- | Flatten a structured 'StateCondition' representing a pre-condition into
-- a single predicate.
preCondPredicate ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimInput sym arch v PBi.Original ->
  SimInput sym arch v PBi.Patched ->
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
