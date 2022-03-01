{-|
Module           : Pate.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Representation and presentation of the equivalence proofs
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE ViewPatterns   #-}
{-# LANGUAGE ImplicitParams #-}

module Pate.Proof
  ( EquivTripleBody(..)
  , EquivTriple
  , VerificationStatus(..)
  , ProofApp(..)
  , MemoryDomain(..)
  , traverseProofApp
  , mapProofApp
  , ProofNonce(..)
  , proofNonceValue
  , ProofNonceExpr(..)
  , ProofNonceApp
  , unNonceProof
  , ProofExpr(..)
  , collectProofExpr
  , BlockSliceTransition(..)
  , foldrMBlockStateLocs
  , BlockSliceState(..)
  , BlockSliceRegOp(..)
  , BlockSliceMemOp(..)
  -- nodes
  , type ProofNodeType
  , type ProofBlockSliceType
  , type ProofDomainType
  , type ProofTripleType
  , type ProofFunctionCallType
  , type ProofStatusType
  , type SymScope
  -- leaves
  , InequivalenceResultC(..)
  , InequivalenceResult
  , withIneqResult
  , CondEquivalenceResult(..)
  , emptyCondEqResult
  , EquivalenceDomain(..)
  ) where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Writer.Strict as CMW
import qualified Data.Kind as DK
import           GHC.TypeNats
import           Numeric.Natural ( Natural )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Proxy

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as FC

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Address as PA
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.ExprMappable as PEM
import qualified Pate.Ground as PG
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PSo
import qualified Pate.Verification.MemoryLog as PVM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.SimulatorRegisters as PSR

import qualified What4.ExprHelpers as W4H
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Concrete as W4C
import qualified What4.Partial as W4P

---------------------------------------------
-- proof objects


-- | The body of an 'EquivTriple'.
data EquivTripleBody sym arch where
  EquivTripleBody ::
    {
      eqPair :: PPa.BlockPair arch
      -- ^ the entry points that yield equivalent states on the post-domain
      -- after execution, assuming initially equivalent states on the pre-domain
    , eqPreDomain :: PES.StatePred sym arch
      -- ^ the pre-domain: the state that was assumed initially equivalent
      -- closed over the bound variables representing the initial state
    , eqPostDomain :: PE.StatePredSpec sym arch
      -- ^ the post-domain: the state that was proven equivalent after execution
      -- abstracted over the bound variables representing the final state
    } -> EquivTripleBody sym arch

instance PEM.ExprMappable sym (EquivTripleBody sym arch) where
  mapExpr sym f triple = do
    eqPreDomain' <- PEM.mapExpr sym f (eqPreDomain triple)
    eqPostDomain' <- PEM.mapExpr sym f (eqPostDomain triple)
    return $ EquivTripleBody (eqPair triple) eqPreDomain' eqPostDomain'

-- | An triple representing the equivalence conditions for a block pair. Abstracted
-- over the initial machine state. This is analogous to a 'ProofExpr' of type
-- 'ProofTriple', but contains the 'PE.StatePred' type that the verifier uses.
-- This redundancy can potentially be eliminated at some point.
type EquivTriple sym arch = PS.SimSpec sym arch (EquivTripleBody sym arch)

data ProofNodeType where
    ProofTripleType :: ProofNodeType
    ProofFunctionCallType :: ProofNodeType
    ProofDomainType :: ProofNodeType
    ProofBlockSliceType :: ProofNodeType
    ProofStatusType :: ProofNodeType

type ProofDomainType = 'ProofDomainType
type ProofTripleType = 'ProofTripleType
type ProofFunctionCallType = 'ProofFunctionCallType
type ProofBlockSliceType = 'ProofBlockSliceType
type ProofStatusType = 'ProofStatusType


data InequivalenceResultC arch grnd where
  InequivalenceResult :: PA.ValidArch arch =>
    { ineqSlice :: BlockSliceTransition grnd arch
    , ineqPre :: EquivalenceDomain grnd arch
    , ineqPost :: EquivalenceDomain grnd arch
    , ineqReason :: PEE.InequivalenceReason
    } -> InequivalenceResultC arch grnd

instance PEM.ExprMappable grnd (InequivalenceResultC arch grnd) where
  mapExpr sym f (InequivalenceResult a1 a2 a3 a4) = InequivalenceResult
    <$> PEM.mapExpr sym f a1
    <*> PEM.mapExpr sym f a2
    <*> PEM.mapExpr sym f a3
    <*> pure a4

type InequivalenceResult arch = PG.Grounded (InequivalenceResultC arch)

withIneqResult ::
  InequivalenceResult arch ->
  (forall grnd. PA.ValidArch arch => PG.IsGroundSym grnd => InequivalenceResultC arch grnd -> a) ->
  a
withIneqResult ineq f = PG.withGroundSym ineq $ \ineq'@InequivalenceResult{} -> f ineq'

data CondEquivalenceResult sym arch where
  CondEquivalenceResult :: PA.ValidArch arch =>
    { condEqExample :: MapF.MapF (W4.SymExpr sym) W4G.GroundValueWrapper
    -- ^ bindings for variables in counter-example
    , condEqPred :: W4.Pred sym
    -- ^ condition that is sufficient to imply equivalence
    , condEqAbortValid :: Bool
    -- ^ true if the negation of this predicate necessarily implies an
    -- abort path on the original binary
    } -> CondEquivalenceResult sym arch

emptyCondEqResult ::
  forall arch sym.
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  sym ->
  CondEquivalenceResult sym arch
emptyCondEqResult sym = CondEquivalenceResult MapF.empty (W4.falsePred sym) False



instance PEM.ExprMappable sym (CondEquivalenceResult sym arch) where
  mapExpr _sym f (CondEquivalenceResult e1 e2 b) =
    CondEquivalenceResult
      <$> (MapF.fromList <$> traverse (\(MapF.Pair e1' e2') -> MapF.Pair <$> f e1' <*> pure e2') (MapF.toList e1))
      <*> f e2
      <*> pure b


-- | The status of some verification problem: either producing a successful result
-- or yielding a counterexample. The resulting
-- predicate represents an additional assumption required for equivalence to hold.
-- (i.e. conditional equivalence).
-- In the case of inequality, the predicate simply false
data VerificationStatus sym arch =
    Unverified
  | VerificationSkipped
  | VerificationSuccess
  | VerificationFail
      { verStatusCounterExample :: InequivalenceResult arch,
        verStatusCondEq :: CondEquivalenceResult sym arch
      }

instance PEM.ExprMappable sym (VerificationStatus sym arch) where
  mapExpr sym f s = case s of
    VerificationFail ce condeq -> do
      ce' <- PEM.mapExpr sym f ce
      condeq' <- PEM.mapExpr sym f condeq
      return $ VerificationFail ce' condeq'
    _ -> return s

-- | An abstract proof object, representing the overall structure of an equivalence proof.
-- The type parameter 'prf' abstracts this structure over the specific types used in the proof,
-- which may be symbolic or concrete (i.e. ground terms from a counterexample).
-- The two instantiations for this parameter are given in
-- 'Pate.Proof.Instances'.
data ProofApp sym arch (node :: ProofNodeType -> DK.Type) (tp :: ProofNodeType) where
  -- | Proof that the post-domain of a given triple is satisfied when the function
  -- corresponding to this 'slice' returns, assuming the pre-domain of the triple
  -- is initially satisifed. The start of this slice (i.e. 'prfTripleBlocks') may either
  -- be the start of a function, or some intermediate point within a function.
  -- The end of this slice is the next function return (or unclassifed jump).

  ProofBlockSlice ::
    { -- | The pre-domain and post-domain that this slice is proven to satisfy upon return.
      -- This triple is not directly proven, but is a consequence of the intermediate proofs
      -- for all function calls (i.e. 'prfBlockSliceCalls').
      prfBlockSliceTriple :: node ProofTripleType
      -- | Proofs for all intermediate function calls between the start of this slice and the final
      -- exit of this slice, showing that the post-domain is satisfied by continuing after each
      -- function call returns.
    , prfBlockSliceCalls :: [(PPa.BlockPair arch, node ProofFunctionCallType)]
      -- | Proof that the post-domain is satisfied if this block slice exits with a return.
    , prfBlockSliceReturn :: Maybe (node ProofTripleType)
      -- | Proof that the post-domain is satisfied if this block slice exits with an unknown branch class.
    , prfBlockSliceUnknownExit :: Maybe (node ProofTripleType)
      -- | The symbolic semantics of the head of this block slice (i.e. from the start of the triple
      -- to some exit condition, either a return or some function call).
    , prfBlockSliceTrans :: BlockSliceTransition sym arch
    } -> ProofApp sym arch node ProofBlockSliceType

  -- | A proof node for a sub-tree of the call graph that is simulated as a unit
  -- (rather than in the sliced up manner of the rest of the verifier)
  --
  -- This node enables much more fine-grained comparison of memory post-states
  -- in the presence of significant control flow changes (e.g., with calls to
  -- different functions in the different sub-trees).
  --
  -- The post-states indicate what memory locations have different values after
  -- the two programs execute
  ProofInlinedCall ::
    { prfInlinedBlocks :: PPa.BlockPair arch
    , prfInlinedResults :: Either String (PVM.WriteSummary sym (MM.ArchAddrWidth arch))
    } -> ProofApp sym arch node ProofBlockSliceType

  -- | Proof that a function call is valid. Specifically, if a function 'g' is called from
  -- 'f', we represent this as follows:
  -- > f(x) =
  -- >   pre(x);
  -- >   g(x);
  -- >   post(x);
  -- >   return;
  ProofFunctionCall ::
    {
      -- | Proof that the pre-domain of the called function is satisifed, assuming
      -- the pre-domain of the caller (i.e. the proof of @pre(x)@).
      prfFunctionCallPre :: node ProofTripleType
      -- | Proof that the function, when called, satisifes the pre-domain of
      -- @post(x)@, assuming the post-domain of @pre(x)@ (i.e. the proof of @g(x)@).
    , prfFunctionCallBody :: node ProofBlockSliceType
      -- | Proof that the post-domain of the caller is satisifed, assuming the
      -- domain of @post(x)@ (i.e. the proof of @post(x)@).
    , prfFunctionCallContinue :: Maybe (node ProofBlockSliceType)
      -- | Metadata identifying the call target and call site
    , prfFunctionCallMetadata :: PA.ConcreteAddress arch
    } -> ProofApp sym arch node ProofFunctionCallType

  -- | Proof that two block slices are equal according to a given post-domain, assuming
  -- a given pre-domain. The scope of the slice is dependent on which parent node
  -- this is attached to.
  ProofTriple ::
    { prfTripleBlocks :: PPa.BlockPair arch
    , prfTriplePreDomain :: node ProofDomainType
    , prfTriplePostDomain :: node ProofDomainType
    , prfTripleStatus :: node ProofStatusType
    } -> ProofApp sym arch node ProofTripleType

  -- TODO: where does it make sense to manage the bound variables in domains?
  -- Since we're not consuming these at the moment it's not an issue, but this needs to
  -- be solved in order to unify 'StatePred', 'EquivalenceDomain' and 'ProofTriple' types
  ProofDomain :: EquivalenceDomain sym arch -> ProofApp sym arch node ProofDomainType
  ProofStatus :: VerificationStatus sym arch -> ProofApp sym arch node ProofStatusType

-- | The domain of an equivalence problem: representing the state that is either
-- assumed (in a pre-domain) or proven (in a post-domain) to be equivalent.
data EquivalenceDomain sym arch where
  EquivalenceDomain ::
    { -- | Each register is considered to be in this domain if the given predicate is true.
      eqDomainRegisters :: MM.RegState (MM.ArchReg arch) (Const (W4.Pred sym))
      -- | The memory domain that is specific to stack variables.
    , eqDomainStackMemory :: MemoryDomain sym arch
      -- | The memory domain that is specific to non-stack (i.e. global) variables.
    , eqDomainGlobalMemory :: MemoryDomain sym arch
    }  -> EquivalenceDomain sym arch

instance PEM.ExprMappable sym (EquivalenceDomain sym arch) where
  mapExpr sym f (EquivalenceDomain a1 a2 a3) = EquivalenceDomain
    <$> MM.traverseRegsWith (\_ (Const p) -> Const <$> f p) a1
    <*> PEM.mapExpr sym f a2
    <*> PEM.mapExpr sym f a3

-- | A memory domain for an equivalence problem.
data MemoryDomain sym arch where
  MemoryDomain ::
    { -- | Associating each memory location (i.e. an address and a number of bytes) with
      -- a predicate.
      memoryDomain :: MapF.MapF (PMC.MemCell sym arch) (Const (W4.Pred sym))
      -- | A predicate indicating if this domain is inclusive or exclusive.
      -- * For positive polarity:
      --   a location is in this domain if it is in the map, and its associated predicate
      --   is true.
      -- * For negative polarity:
      --   a location is in this domain if it is not in the map,
      --   or it is in the map and its associated predicate is false.
    , memoryDomainPolarity :: W4.Pred sym
    }  -> MemoryDomain sym arch


instance PEM.ExprMappable sym (MemoryDomain sym arch) where
  mapExpr sym f (MemoryDomain a1 a2) = 
     MemoryDomain
       <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList a1)))
       <*> f a2
   where
     transMemCell (MapF.Pair cell (Const p)) = MapF.Pair
       <$> PEM.mapExpr sym f cell
       <*> (Const <$> f p)

-- | Traverse the nodes of a 'ProofApp', changing the
-- recursive 'node' type while leaving the leafs (i.e. the 'prf' type) unchanged.
traverseProofApp ::
  Applicative m =>
  (forall tp. node tp -> m (node' tp)) ->
  ProofApp sym arch node utp ->
  m ((ProofApp sym arch node') utp)
traverseProofApp f = \case
  ProofBlockSlice a1 a2 a3 a4 a5 -> ProofBlockSlice
    <$> f a1
    <*> traverse (\(blks,v) -> (,) <$> pure blks <*> f v) a2
    <*> traverse f a3
    <*> traverse f a4
    <*> pure a5
  ProofInlinedCall a1 a2 -> ProofInlinedCall
    <$> pure a1
    <*> pure a2
  ProofFunctionCall a1 a2 a3 md -> ProofFunctionCall
    <$> f a1
    <*> f a2
    <*> traverse f a3
    <*> pure md
  ProofTriple a1 a2 a3 a4 -> ProofTriple
    <$> pure a1
    <*> f a2
    <*> f a3
    <*> f a4
  ProofDomain a1 -> ProofDomain <$> pure a1
  ProofStatus a1 -> ProofStatus <$> pure a1

-- instance
--   (forall tp. PEM.ExprMappable sym (node tp)) =>
--   PEM.ExprMappable sym (ProofApp sym arch node utp) where
--   mapExpr sym f = \case
--     ProofLeaf a1 -> ProofLeaf <$> PEM.mapExpr sym f a1
--     app -> traverseProofApp (PEM.mapExpr sym f) app
--

-- | Map over the nodes of a 'ProofApp', changing the
-- 'node' type while leaving the leafs (i.e. the 'prf' type) unchanged.
mapProofApp ::
  (forall tp. node tp -> node' tp) ->
  ProofApp sym arch node utp ->
  ProofApp sym arch node' utp
mapProofApp f app = runIdentity $ traverseProofApp (\app' -> Identity $ f app') app

-- -- | A bundle of functions for converting the leafs of a proof graph
-- data ProofTransformer m prf prf' where
--   ProofTransformer ::
--     {
--       prfPredTrans :: ProofPredicate prf -> m (ProofPredicate prf')
--     , prfMemCellTrans :: forall n. ProofMemCell prf n -> m (ProofMemCell prf' n)
--     , prfBVTrans :: forall n. ProofBV prf n -> m (ProofBV prf' n)
--     , prfExitTrans :: ProofBlockExit prf -> m (ProofBlockExit prf')
--     , prfValueTrans :: forall tp. ProofMacawValue prf tp -> m (ProofMacawValue prf' tp)
--     , prfContextTrans :: ProofContext prf -> m (ProofContext prf')
--     , prfCounterExampleTrans :: ProofCounterExample prf -> m (ProofCounterExample prf')
--     , prfConditionTrans :: ProofCondition prf -> m (ProofCondition prf')
--     , prfConstraint ::
--         forall a. ((IsProof prf'
--                    , ProofRegister prf ~ ProofRegister prf'
--                    , ProofBlock prf ~ ProofBlock prf'
--                    , ProofInlinedResult prf ~ ProofInlinedResult prf') => a) -> a
--     } -> ProofTransformer m prf prf'
-- 
-- transformMemDomain ::
--   forall m prf prf'.
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   ProofMemoryDomain prf ->
--   m (ProofMemoryDomain prf')
-- transformMemDomain f (ProofMemoryDomain dom pol) = prfConstraint f $ ProofMemoryDomain
--   <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList dom)))
--   <*> prfPredTrans f pol
--     where
--       transMemCell :: MapF.Pair (ProofMemCell prf) (Const (ProofPredicate prf))
--         -> m (MapF.Pair (ProofMemCell prf') (Const (ProofPredicate prf')))
--       transMemCell (MapF.Pair cell (Const p)) = MapF.Pair
--         <$> prfMemCellTrans f cell
--         <*> (Const <$> (prfPredTrans f p))
-- 
-- -- | Traverse the leafs of 'ProofApp' with the given 'ProofTransformer', leaving the
-- -- 'node' type unchanged, but changing the 'prf' type.
-- transformProofApp ::
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   ProofApp prf node utp ->
--   m ((ProofApp prf' node) utp)
-- transformProofApp f app = prfConstraint f $ case app of
--   ProofBlockSlice a1 a2 a3 a4 a5 -> ProofBlockSlice
--     <$> pure a1
--     <*> pure a2
--     <*> pure a3
--     <*> pure a4
--     <*> transformBlockSlice f a5
--   ProofInlinedCall pp res -> pure (ProofInlinedCall pp res)
--   ProofFunctionCall a1 a2 a3 md -> ProofFunctionCall
--     <$> pure a1
--     <*> pure a2
--     <*> pure a3
--     <*> pure md
--   ProofTriple a1 a2 a3 a4 -> ProofTriple
--     <$> pure a1
--     <*> pure a2
--     <*> pure a3
--     <*> pure a4
--     
--   ProofStatus a1 -> ProofStatus
--     <$> traverse (\(cex, cond) -> (,) <$> prfCounterExampleTrans f cex <*> prfConditionTrans f cond) a1
--   ProofDomain a1 a2 a3 a4 -> ProofDomain
--     <$> MM.traverseRegsWith (\_ (Const v) -> Const <$> prfPredTrans f v) a1
--     <*> transformMemDomain f a2
--     <*> transformMemDomain f a3
--     <*> prfContextTrans f a4
-- 

-- | A 'ProofExpr' is an direct proof representation, where
-- nodes hold completed sub-proofs.
data ProofExpr sym arch tp where
  ProofExpr :: { unApp :: ProofApp sym arch (ProofExpr sym arch) tp } -> ProofExpr sym arch tp

-- | Traverse all sub-expressions of a 'ProofExpr'
traverseProofExpr ::
  Monad m =>
  (forall tp'. ProofExpr sym arch tp' -> m (ProofExpr sym arch tp')) ->
  ProofExpr sym arch tp ->
  m (ProofExpr sym arch tp)
traverseProofExpr f e =
  ProofExpr <$> (traverseProofApp (traverseProofExpr f) =<< (unApp <$> f e))

-- transformProofExpr ::
--   Monad m =>
--   ProofTransformer m prf prf' ->
--   ProofExpr prf tp ->
--   m (ProofExpr prf' tp)
-- transformProofExpr f (ProofExpr app) =
--   ProofExpr <$> (traverseProofApp (transformProofExpr f) =<< (transformProofApp f app))
--

-- | Collect results from all sub-expressions
collectProofExpr ::
  forall w sym arch tp.
  Monoid w =>
  (forall tp'. ProofExpr sym arch tp' -> w) ->
  ProofExpr sym arch tp ->
  w
collectProofExpr f e_outer = runIdentity $ CMW.execWriterT (traverseProofExpr go e_outer)
  where
    go :: ProofExpr sym arch tp' -> CMW.WriterT w Identity (ProofExpr sym arch tp')
    go e = do
      CMW.tell (f e)
      return e

-- -- | A domain expression is actually independent of the 'app' parameter, so we can
-- -- project it to any one.
-- appDomain ::
--   ProofExpr prf ProofDomainType ->
--   ProofApp prf app ProofDomainType
-- appDomain (ProofExpr (ProofDomain regs stack glob domCtx)) = ProofDomain regs stack glob domCtx
-- 
-- emptyDomain ::
--   forall prf m.
--   Monad m =>
--   IsProof prf =>
--   IsBoolLike prf m =>
--   ProofContext prf ->
--   m (ProofExpr prf ProofDomainType)
-- emptyDomain domCtx = do
--   regs <- MM.mkRegStateM (\_ -> Const <$> proofPredFalse @prf)
--   stack <- emptyMemDomain
--   globs <- emptyMemDomain
--   return $ ProofExpr $ ProofDomain regs stack globs domCtx
-- 
-- emptyMemDomain ::
--   forall prf m.
--   Monad m =>
--   IsBoolLike prf m =>
--   m (ProofMemoryDomain prf)
-- emptyMemDomain = do
--   falsePred <- proofPredFalse @prf
--   return $ ProofMemoryDomain MapF.empty falsePred
--

type family SymScope sym :: DK.Type
type instance SymScope (W4B.ExprBuilder t fs scope) = t

-- | A nonce representing an indirect reference to a proof node.
data ProofNonce sym (tp :: ProofNodeType) where
  ProofNonce :: N.Nonce (SymScope sym) tp -> ProofNonce sym tp

deriving instance Show (ProofNonce sym tp)

instance ShowF (ProofNonce sym) where
  showF (ProofNonce n) = showF n

instance TestEquality (ProofNonce sym) where
  testEquality (ProofNonce n1) (ProofNonce n2) = testEquality n1 n2

instance OrdF (ProofNonce prf) where
  compareF (ProofNonce n1) (ProofNonce n2) = compareF n1 n2

proofNonceValue :: ProofNonce sym tp -> Natural
proofNonceValue (ProofNonce n) = fromIntegral (N.indexValue n)

-- | A proof expression, annotated with nonces.
data ProofNonceExpr sym arch tp where
  ProofNonceExpr ::
    { prfNonce :: ProofNonce sym tp
    , prfParent :: Some (ProofNonce sym)
    , prfNonceBody :: ProofApp sym arch (ProofNonceExpr sym arch) tp
    } -> ProofNonceExpr sym arch tp

type ProofNonceApp sym arch tp = ProofApp sym arch (ProofNonceExpr sym arch) tp

-- | Strip the nonces from a 'ProofNonceExpr', yielding an equivalent 'ProofExpr'.
unNonceProof :: ProofNonceExpr sym arch tp -> ProofExpr sym arch tp
unNonceProof prf = ProofExpr $ mapProofApp unNonceProof (prfNonceBody prf)

-- | The semantics of executing two block slices: an original and a patched variant.
-- The type parameter 'prf' abstracts this over the specific types,
-- which may be symbolic or concrete (i.e. ground terms from a counterexample).
data BlockSliceTransition sym arch where
  BlockSliceTransition ::
    { -- | The pre-states of the blocks prior to execution.
      slBlockPreState :: BlockSliceState sym arch
      -- | The post-states of the blocks after execution.
    , slBlockPostState :: BlockSliceState sym arch
      -- | The exit condition of the blocks (i.e. return, function call, etc)
    , slBlockExitCase :: PPa.PatchPairC (CS.RegValue sym (MS.MacawBlockEndType arch))
    } -> BlockSliceTransition sym arch

instance PEM.ExprMappable sym (BlockSliceTransition sym arch) where
  mapExpr sym f (BlockSliceTransition a1 a2 a3) = 
     BlockSliceTransition
       <$> PEM.mapExpr sym f a1
       <*> PEM.mapExpr sym f a2
       <*> PEM.mapExpr sym f a3

-- | Traverse the leafs of a 'BlockSliceTransition' with the given 'ProofTransformer',
-- changing the 'prf' type. In particular, this is used to ground a counterexample.
-- transformBlockSlice ::
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   BlockSliceTransition prf ->
--   m (BlockSliceTransition prf')
-- transformBlockSlice f (BlockSliceTransition a1 a2 a3) =
--     BlockSliceTransition
--       <$> transformBlockSliceState f a1
--       <*> transformBlockSliceState f a2
--       <*> traverse (prfExitTrans f) a3
--

-- | The machine state of two block slices: original and patched.
data BlockSliceState sym arch where
  BlockSliceState ::
    { -- | The state of memory for all memory locations that are associated with this
      -- slice: i.e. the pre-state contains all reads and the post-state contains all writes.
      slMemState :: MapF.MapF (PMC.MemCell sym arch) (BlockSliceMemOp sym)
      -- | The state of all registers.
    , slRegState :: MM.RegState (MM.ArchReg arch) (BlockSliceRegOp sym)
    } -> BlockSliceState sym arch

instance PEM.ExprMappable sym (BlockSliceState sym arch) where
  mapExpr sym f (BlockSliceState a1 a2) = 
     BlockSliceState
       <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList a1)))
       <*> MM.traverseRegsWith (\_ v -> PEM.mapExpr sym f v) a2
   where
     transMemCell (MapF.Pair cell mop) = MapF.Pair
       <$> PEM.mapExpr sym f cell
       <*> PEM.mapExpr sym f mop

-- transformBlockSliceState ::
--   forall m prf prf'.
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   BlockSliceState prf ->
--   m (BlockSliceState prf')
-- transformBlockSliceState f (BlockSliceState a1 a2) = prfConstraint f $
--     BlockSliceState
--       <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList a1)))
--       <*> MM.traverseRegsWith (\_ v -> transformBlockSliceRegOp f v) a2
--   where
--     transMemCell :: MapF.Pair (ProofMemCell prf) (BlockSliceMemOp prf)
--       -> m (MapF.Pair (ProofMemCell prf') (BlockSliceMemOp prf'))
--     transMemCell (MapF.Pair cell mop) = MapF.Pair
--       <$> prfMemCellTrans f cell
--       <*> transformBlockSliceMemOp f mop
-- 
-- | The original and patched values for a register.
data BlockSliceRegOp sym tp where
  BlockSliceRegOp ::
    { slRegOpValues :: PPa.PatchPairC (PSR.MacawRegEntry sym tp)
    , slRegOpRepr :: CT.TypeRepr (MS.ToCrucibleType tp)
    -- | True if these values are considered equivalent (without
    -- considering a particular equivalence domain).
    , slRegOpEquiv :: W4.Pred sym
    } -> BlockSliceRegOp sym tp

instance PEM.ExprMappable sym (BlockSliceRegOp sym tp) where
  mapExpr sym f regOp = BlockSliceRegOp
    <$> traverse (PEM.mapExpr sym f) (slRegOpValues regOp)
    <*> pure (slRegOpRepr regOp)
    <*> f (slRegOpEquiv regOp)


-- transformBlockSliceRegOp ::
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   BlockSliceRegOp prf tp ->
--   m (BlockSliceRegOp prf' tp)
-- transformBlockSliceRegOp f (BlockSliceRegOp a1 a2 a3) =
--     BlockSliceRegOp
--       <$> traverse (prfValueTrans f) a1
--       <*> pure a2
--       <*> prfPredTrans f a3
-- 
-- | The original and patched values for a memory location, where
-- 'w' represents the number of bytes read or written.
data BlockSliceMemOp sym w where
  BlockSliceMemOp ::
    { slMemOpValues :: PPa.PatchPairC (CLM.LLVMPtr sym (8 W4.* w))
    -- | True if these values are considered equivalent (without
    -- considering a particular equivalence domain).
    , slMemOpEquiv :: W4.Pred sym
    -- | True if this memory operation is "live".
    , slMemOpCond :: W4.Pred sym
    } -> BlockSliceMemOp sym w

instance PEM.ExprMappable sym (BlockSliceMemOp sym w) where
  mapExpr sym f memOp = BlockSliceMemOp
    <$> traverse (W4H.mapExprPtr sym f) (slMemOpValues memOp)
    <*> f (slMemOpEquiv memOp)
    <*> f (slMemOpCond memOp)

-- transformBlockSliceMemOp ::
--   Applicative m =>
--   ProofTransformer m prf prf' ->
--   BlockSliceMemOp prf tp ->
--   m (BlockSliceMemOp prf' tp)
-- transformBlockSliceMemOp f (BlockSliceMemOp a1 a2 a3) =
--     BlockSliceMemOp
--       <$> traverse (prfBVTrans f) a1
--       <*> prfPredTrans f a2
--       <*> prfPredTrans f a3
-- 
foldrMBlockStateLocs ::
  Monad m =>
  (forall tp. MM.ArchReg arch tp -> BlockSliceRegOp sym tp -> b -> m b) ->
  (forall w. PMC.MemCell sym arch w -> BlockSliceMemOp sym w -> b -> m b) ->
  b ->
  BlockSliceState sym arch ->
  m b
foldrMBlockStateLocs f_reg f_mem b (BlockSliceState a1 a2) = do
  b' <- MapF.foldrMWithKey f_mem b a1
  MapF.foldrMWithKey f_reg b' (MM.regStateMap a2) 
