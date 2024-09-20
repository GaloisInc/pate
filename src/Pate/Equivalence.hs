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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Equivalence
  ( EquivalenceStatus(..)
  , getPostdomain
  , getPredomain
  , impliesPredomain
  , eqDomPost
  , resolveCellEquiv
  , resolveCellEquivMem
  , resolveCellEquivStack
  , registerValuesEqual
  , EquivContext(..)
  , MemoryCondition(..)
  , StatePreCondition(..)
  , StatePostCondition(..)
  , preCondAssumption
  , postCondPredicate
  , memPreCondToPred
  , memPostCondToPred
  ) where

import           Control.Lens hiding ( op, pre, (.=) )
import           Control.Monad ( foldM )
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Set as S
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM
import           Lang.Crucible.Backend (IsSymInterface)
import qualified What4.Expr.Builder as W4B

import qualified Pate.Arch as PA
import           Pate.AssumptionSet
import qualified Pate.Binary as PBi
import qualified Pate.Location as PL
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Register as PRe
import qualified Pate.Register.Traversal as PRt
import qualified Pate.PatchPair as PPa
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo
import           What4.ExprHelpers
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified What4.PredMap as WPM
import qualified Pate.ExprMappable as PEM

import           Pate.TraceTree
import Data.Data (Typeable)
import qualified What4.JSON as W4S
import           What4.JSON ((.=))

data EquivalenceStatus =
    Equivalent
  | Inequivalent
  | ConditionallyEquivalent
  | Errored PEE.EquivalenceError

deriving instance Show EquivalenceStatus

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

instance IsTraceNode k "equivalence_result" where
  type TraceNodeType k "equivalence_result" = EquivalenceStatus
  prettyNode () = \case
    Equivalent -> "Binaries are observably equivalent"
    Inequivalent -> "Binaries are not observably equivalent"
    ConditionallyEquivalent -> "Binaries are conditionally, observably equivalent"
    Errored{} -> "Analysis failure due to error"
  nodeTags = mkTags @k @"equivalence_result" [Summary, Simplified]

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


registerValuesEqual' ::
  forall sym arch tp.
  PA.ValidArch arch =>
  W4.IsSymExprBuilder sym =>
  PA.HasDedicatedRegister arch ->
  sym ->
  MM.ArchReg arch tp ->
  W4.Pred sym ->
  PSR.MacawRegEntry sym tp ->
  PSR.MacawRegEntry sym tp ->
  IO (AssumptionSet sym)
registerValuesEqual' hdr sym r precond vO vP = do
  asm <- case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return $ mempty
    PRe.RegSP -> do
      let
        CLM.LLVMPointer _ offO = PSR.macawRegValue vO
        CLM.LLVMPointer _ offP = PSR.macawRegValue vP
      return $ exprBinding offO offP
    _ -> return $ macawRegBinding sym vO vP
  case W4.asConstantPred precond of
    Just True -> return asm
    Just False -> return mempty
    _ -> fromPred <$> (impM sym (return precond) (toPred sym asm))

-- | This simply bundles up the necessary state elements necessary to resolve equality.
data EquivContext sym arch where
  EquivContext ::
    { eqCtxHDR :: PA.HasDedicatedRegister arch
    , eqCtxStackRegion :: W4.SymNat sym
    , eqCtxConstraints :: forall a. (forall t st fs. (sym ~ W4B.ExprBuilder t st fs, PA.ValidArch arch, PSo.ValidSym sym) => a) -> a
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
registerValuesEqual sym eqCtx r vO vP = registerValuesEqual' (eqCtxHDR eqCtx) sym r (W4.truePred sym) vO vP >>= toPred sym

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
  SimScope sym arch v ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StatePreCondition sym arch v)
getPredomain sym scope bundle eqCtx eqDom = do
  let (stO, stP) = asStatePair scope (simIn bundle) simInState
  eqDomPre sym stO stP eqCtx eqDom

-- | True if the first precondition implies the second
impliesPredomain ::
  forall sym arch v.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimScope sym arch v ->
  PPa.PatchPair (SimInput sym arch v) ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (W4.Pred sym)  
impliesPredomain sym scope input eqCtx domAsm domConcl = do
  let (stO, stP) = asStatePair scope input simInState
  asm <- eqDomPre sym stO stP eqCtx domAsm >>= preCondAssumption sym scope input eqCtx >>= toPred sym
  concl <- eqDomPre sym stO stP eqCtx domConcl >>= preCondAssumption sym scope input eqCtx >>= toPred sym
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
  SimScope sym arch v ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch {- ^ pre-domain for this slice -} ->
  PED.EquivalenceDomain sym arch {- ^ target post-domain -} ->
  IO (StatePostCondition sym arch v)
getPostdomain sym scope bundle eqCtx domPre domPost = do
  let (stO, stP) = asStatePair scope (simOut bundle) simOutState
  eqDomPost sym stO stP eqCtx domPre domPost

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
  let preds = map snd $ WPM.toList $ memCondPred memCond
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
  -- explicitly not a 'PatchPair' because we are always comparing two states
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PEM.MemoryDomain sym arch {- ^ pre-domain for this slice -} ->
  PEM.MemoryDomain sym arch {- ^ target post-domain -} ->
  IO (MemoryCondition sym arch)
memDomPost sym memEqRegion stO stP domPre domPost = do
  footO <- MT.traceFootprint sym memO
  footP <- MT.traceFootprint sym memP
  let foot = S.union footO footP
  footCells <- PEM.toList <$> PEM.excludeFootPrints sym (S.filter (MT.isDir MT.Write) foot) domPre
  condPredList <- mapM (\(Some cell, p) -> resolveCell cell p >>= \p' -> return (Some cell, p')) footCells
  condPred <- WPM.fromList sym WPM.PredConjRepr condPredList
  return $ MemoryCondition condPred
  where
    memO = simMem stO
    memP = simMem stP
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
  -- explicitly not a 'PatchPair' because we are always comparing two states
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
resolveCellEquivMem sym eqCtx stO stP cell cond = do
  resolveCellEquiv sym (MemEqOutsideRegion (eqCtxStackRegion eqCtx)) stO stP cell cond

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
resolveCellEquivStack sym eqCtx stO stP cell cond =
  resolveCellEquiv sym (MemEqAtRegion (eqCtxStackRegion eqCtx)) stO stP cell cond


-- | Structurally equivalent to a 'PEM.MemoryDomain', however the predicates
-- relate to equality on the given cells.
data MemoryCondition sym arch = MemoryCondition
  { memCondPred :: PMC.MemCellPred sym arch WPM.PredConjT
  }

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) => PL.LocationTraversable sym arch (MemoryCondition sym arch) where
  traverseLocation sym mcond f = do
    dom' <- PL.traverseLocation sym (memCondPred mcond) f
    return $ mcond { memCondPred = dom' }

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) => PEM.ExprMappable sym (MemoryCondition sym arch) where
  mapExpr sym f (MemoryCondition cond) = MemoryCondition <$> PEM.mapExpr sym f cond

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MemoryCondition sym arch) where
  w4Serialize (MemoryCondition cond) = W4S.w4Serialize cond

-- | Flatten a structured 'MemoryCondition' representing a memory pre-condition into
-- a single predicate.
-- We require the pre-states in order to construct the initial equality assumption.
-- Specifically we assume that the patched trace is equivalent
-- to the original trace with arbitrary modifications to excluded addresses
memPreCondToPred ::
  forall sym arch v.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimScope sym arch v ->
  MemRegionEquality sym arch ->
  PPa.PatchPair (SimInput sym arch v) ->
  PEM.MemoryDomain sym arch ->
  IO (W4.Pred sym)
memPreCondToPred sym scope memEqRegion input memDom  = do
  let 
    (stO, stP) = asStatePair scope input simInState
    memO = simMem stO
    memP = simMem stP
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
  let cells = PEM.toList memDom
  mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') (MT.memState memO) cells
  getRegionEquality sym memEqRegion mem' (MT.memState memP)


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




-- | Compute a structured 'RegisterCondition'
-- where the predicate associated with each register
-- is true iff the register is equal in two given states (conditional on
-- the register being present in the given 'PER.RegisterDomain')
regDomRel ::
  forall sym arch v .
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  PA.HasDedicatedRegister arch ->
  sym ->
  -- explicitly not a 'PatchPair' because we are always comparing two states
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  PER.RegisterDomain sym arch ->
  IO (PEC.RegisterCondition sym arch v)
regDomRel hdr sym st1 st2 regDom  = PEC.RegisterCondition <$> do
  PRt.zipWithRegStatesM (simRegs st1) (simRegs st2) $ \r vO vP -> Const <$> do
    let p = PER.registerInDomain sym r regDom
    registerValuesEqual' hdr sym r p vO vP



regCondToAsm ::
  W4.IsSymExprBuilder sym =>
  sym ->
  PEC.RegisterCondition sym arch v ->
  IO (AssumptionSet sym)
regCondToAsm _sym regCond = return $ PRt.collapse (PEC.regCondPreds regCond)

-- | A structured pre condition
data StatePreCondition sym arch v = StatePreCondition
  { stRegPreCond :: PEC.RegisterCondition sym arch v
  , stStackPreDom :: PEM.MemoryDomain sym arch
  , stMemPreDom :: PEM.MemoryDomain sym arch
  , stMaxRegionPreCond :: NamedAsms sym "maxRegion"
  , stStackBasePreCond :: NamedAsms sym "stackBase"
  }

-- | A structured post condition
-- TODO: It may make sense to redefine this as a general 'PL.Location' to 'AssumptionSet'
-- map, which would make it more natural to include additional meta-state elements
-- rather than having a catch-all "extra" condition at the end.
-- We only ever intepret this data via 'PL.traverseLocation' to collect and prove the
-- individual assertions.
data StatePostCondition sym arch v = StatePostCondition
  { stRegPostCond :: PEC.RegisterCondition sym arch v
  , stStackPostCond :: MemoryCondition sym arch
  , stMemPostCond :: MemoryCondition sym arch
  , stMaxRegionPostCond :: NamedAsms sym "maxRegion"
  , stStackBasePostCond :: NamedAsms sym "stackBase"
  -- ^ conditions on meta-state (i.e. 'simMaxRegion' and 'simStackBase')
  }


instance (MM.RegisterInfo (MM.ArchReg arch), W4.IsSymExprBuilder sym) => PL.LocationTraversable sym arch (StatePostCondition sym arch v) where
  traverseLocation sym (StatePostCondition a b c d e) f =
    StatePostCondition 
    <$> PL.traverseLocation sym a f 
    <*> PL.traverseLocation sym b f 
    <*> PL.traverseLocation sym c f
    <*> PL.traverseLocation sym d f
    <*> PL.traverseLocation sym e f

instance W4.IsSymExprBuilder sym => PEM.ExprMappable sym (StatePostCondition sym arch v) where
  mapExpr sym f (StatePostCondition a b c d e) =
    StatePostCondition <$> PEM.mapExpr sym f a <*> PEM.mapExpr sym f b <*> PEM.mapExpr sym f c <*> PEM.mapExpr sym f d <*>  PEM.mapExpr sym f e

instance (W4S.W4SerializableF sym (MM.ArchReg arch), W4S.SerializableExprs sym) => W4S.W4Serializable sym (StatePostCondition sym arch v) where
  w4Serialize (StatePostCondition a b c d e) =
    W4S.object [ "registers" .= a, "stack" .= b, "memory" .= c, "max_region" .= d, "stack_base" .= e]

instance (W4S.W4SerializableF sym (MM.ArchReg arch), W4S.SerializableExprs sym) => W4S.W4SerializableF sym (StatePostCondition sym arch)


eqDomPre ::
  forall sym arch v.
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  -- explicitly not a 'PatchPair' because we are always comparing two states
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch ->
  IO (StatePreCondition sym arch v)
eqDomPre sym stO stP (eqCtxHDR -> hdr) eqDom  = do
  let
    st = PPa.PatchPair stO stP
    maxRegion = TF.fmapF (\st' -> Const $ unSE $ simMaxRegion st') st
    stackBase = TF.fmapF (\st' -> Const $ unSE $ simStackBase st') st

  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters eqDom)
  maxRegionsEq <- mkNamedAsm sym (PED.eqDomainMaxRegion eqDom) (bindExprPair maxRegion)
  -- stack base equality is implied by stack register equality, so we don't need an explicit entry
  -- for it in the domain
  stackBaseEq <-  mkNamedAsm sym (PL.knownNamedPred (PER.registerInDomain sym MM.sp_reg (PED.eqDomainRegisters eqDom))) (bindExprPair stackBase)
  return $ StatePreCondition regsEq (PED.eqDomainStackMemory eqDom) (PED.eqDomainGlobalMemory eqDom) maxRegionsEq stackBaseEq

mkNamedAsm :: W4.IsSymExprBuilder sym => sym -> PL.NamedPred sym WPM.PredDisjT nm -> AssumptionSet sym -> IO (NamedAsms sym nm)
mkNamedAsm sym (PL.NamedPred pm) asms = do
  ((), p) <- WPM.collapse sym (\_ -> return) () pm
  case W4.asConstantPred p of
    Just True -> return $ NamedAsms asms
    Just False -> return $ NamedAsms mempty
    Nothing -> do
      asmsP <- toPred sym asms
      (NamedAsms . fromPred) <$> W4.impliesPred sym p asmsP

eqDomPost ::
  forall sym arch v.
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  -- explicitly not a 'PatchPair' because we are always comparing two states
  SimState sym arch v PBi.Original ->
  SimState sym arch v PBi.Patched ->
  EquivContext sym arch ->
  PED.EquivalenceDomain sym arch {- ^ pre-domain for this slice -} ->
  PED.EquivalenceDomain sym arch {- ^ target post-domain -} ->
  IO (StatePostCondition sym arch v)
eqDomPost sym stO stP eqCtx domPre domPost = do
  let
    st = PPa.PatchPair stO stP
    hdr = eqCtxHDR eqCtx
    stackRegion = eqCtxStackRegion eqCtx
    maxRegion = TF.fmapF (\st' -> Const $ unSE $ simMaxRegion st') st
  
  regsEq <- regDomRel hdr sym stO stP (PED.eqDomainRegisters domPost)
  stacksEq <- memDomPost sym (MemEqAtRegion stackRegion) stO stP (PED.eqDomainStackMemory domPre) (PED.eqDomainStackMemory domPost)
  memEq <- memDomPost sym (MemEqOutsideRegion stackRegion) stO stP (PED.eqDomainGlobalMemory domPre) (PED.eqDomainGlobalMemory domPost)
  maxRegionsEq <- mkNamedAsm sym (PED.eqDomainMaxRegion domPost) (bindExprPair maxRegion)

  -- post condition does not care about the stack base, as it is derived
  -- from the stack pointer
  stackBaseEq <- mkNamedAsm sym (PL.knownNamedPred (W4.falsePred sym)) mempty
  return $ StatePostCondition regsEq stacksEq memEq maxRegionsEq stackBaseEq

-- | Flatten a structured 'StateCondition' representing a pre-condition into
-- a single 'AssumptionSet'.
preCondAssumption ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  SimScope sym arch v ->
  PPa.PatchPair (SimInput sym arch v) ->
  EquivContext sym arch ->
  StatePreCondition sym arch v ->
  IO (AssumptionSet sym)
preCondAssumption sym scope input (eqCtxStackRegion -> stackRegion) stCond = do
  regsPred <- regCondToAsm sym (stRegPreCond stCond)
  stackPred <- memPreCondToPred sym scope (MemEqAtRegion stackRegion) input (stStackPreDom stCond)
  memPred <- memPreCondToPred sym scope (MemEqOutsideRegion stackRegion) input (stMemPreDom stCond)
  return $ (fromPred memPred) <> (fromPred stackPred) <> regsPred <> (namedAsms (stMaxRegionPreCond stCond)) <> (namedAsms (stStackBasePreCond stCond))

-- | Flatten a structured 'StateCondition' representing a post-condition into
-- a single predicate.
postCondPredicate ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  StatePostCondition sym arch v ->
  IO (W4.Pred sym)
postCondPredicate sym stCond = do
  regsAsm <- regCondToAsm sym (stRegPostCond stCond)
  regsPred <- toPred sym regsAsm
  stackPred <- memPostCondToPred sym (stStackPostCond stCond)
  memPred <- memPostCondToPred sym (stMemPostCond stCond)
  maxRegionPred <- toPred sym (namedAsms (stMaxRegionPostCond stCond))
  stackBasePred <- toPred sym (namedAsms (stStackBasePostCond stCond))
  allPreds sym [regsPred, stackPred, memPred, maxRegionPred, stackBasePred]