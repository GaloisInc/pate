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
  ( VerificationStatus(..)
  , ProofApp(..)
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
  , InequivalenceResultSym(..)
  , InequivalenceResult
  , withIneqResult
  , CondEquivalenceResult(..)
  , emptyCondEqResult
  ) where

import           Data.Functor.Const
import           Control.Monad.Identity
import           Control.Monad.Writer.Strict as CMW
import qualified Data.Kind as DK
import           Numeric.Natural ( Natural )

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.Symbolic as MS

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Address as PA
import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.ExprMappable as PEM
import qualified Pate.Ground as PG
import qualified Pate.PatchPair as PPa
import qualified Pate.Solver as PSo
import qualified Pate.Verification.MemoryLog as PVM
import qualified Pate.MemCell as PMC
import qualified Pate.SimulatorRegisters as PSR

import qualified What4.ExprHelpers as W4H
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4

---------------------------------------------
-- proof objects


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

-- | A (possibly symbolic) inequivalence result, representing a snapshot of
-- an attempted equivalence proof.
data InequivalenceResultSym arch sym where
  InequivalenceResultSym :: PA.ValidArch arch =>
    { ineqSlice :: BlockSliceTransition sym arch
    , ineqPre :: PED.EquivalenceDomain sym arch
    , ineqPost :: PED.EquivalenceDomain sym arch
    , ineqReason :: PEE.InequivalenceReason
    } -> InequivalenceResultSym arch sym

instance PEM.ExprMappable sym (InequivalenceResultSym arch sym) where
  mapExpr sym f (InequivalenceResultSym a1 a2 a3 a4) = InequivalenceResultSym
    <$> PEM.mapExpr sym f a1
    <*> PEM.mapExpr sym f a2
    <*> PEM.mapExpr sym f a3
    <*> pure a4

instance PEM.ExprFoldableIO sym (InequivalenceResultSym arch sym) where

-- | An 'InequivalenceResultSym' once it has been grounded to a particular
-- model (representing the counter-example for an inequivalence proof)
type InequivalenceResult arch = PG.Grounded (InequivalenceResultSym arch)

withIneqResult ::
  InequivalenceResult arch ->
  (forall grnd. PA.ValidArch arch => PG.IsGroundSym grnd => InequivalenceResultSym arch grnd -> a) ->
  a
withIneqResult ineq f = PG.withGroundSym ineq $ \ineq'@InequivalenceResultSym{} -> f ineq'

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

-- | A proof object, representing the overall structure of an equivalence proof.
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
    , prfBlockSliceCalls :: [(PB.BlockPair arch, node ProofFunctionCallType)]
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
    { prfInlinedBlocks :: PB.BlockPair arch
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
    { prfTripleBlocks :: PB.BlockPair arch
    , prfTriplePreDomain :: node ProofDomainType
    , prfTriplePostDomain :: node ProofDomainType
    , prfTripleStatus :: node ProofStatusType
    } -> ProofApp sym arch node ProofTripleType

  -- TODO: where does it make sense to manage the bound variables in domains?
  -- Since we're not consuming these at the moment it's not an issue, but this needs to
  -- be solved in order to unify 'StatePred', 'EquivalenceDomain' and 'ProofTriple' types
  ProofDomain :: PED.EquivalenceDomain sym arch -> ProofApp sym arch node ProofDomainType
  ProofStatus :: VerificationStatus sym arch -> ProofApp sym arch node ProofStatusType

-- | Traverse the nodes of a 'ProofApp', changing the
-- recursive 'node' type while leaving the leaves unchanged.
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

-- | Map over the nodes of a 'ProofApp', changing the
-- 'node' type while leaving the leaves unchanged.
mapProofApp ::
  (forall tp. node tp -> node' tp) ->
  ProofApp sym arch node utp ->
  ProofApp sym arch node' utp
mapProofApp f app = runIdentity $ traverseProofApp (\app' -> Identity $ f app') app

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

-- | A proof expression that encoding the tree structure of the proof by annotating
-- each node with a unique nonce, and the nonce of its parent.
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
data BlockSliceTransition sym arch where
  BlockSliceTransition ::
    { -- | The pre-states of the blocks prior to execution.
      slBlockPreState :: BlockSliceState sym arch
      -- | The post-states of the blocks after execution.
    , slBlockPostState :: BlockSliceState sym arch
      -- | The exit condition of the blocks (i.e. return, function call, etc)
    , slBlockExitCase :: PPa.PatchPairC (CS.RegValue sym (MCS.MacawBlockEndType arch))
    } -> BlockSliceTransition sym arch

instance PEM.ExprMappable sym (BlockSliceTransition sym arch) where
  mapExpr sym f (BlockSliceTransition a1 a2 a3) = 
     BlockSliceTransition
       <$> PEM.mapExpr sym f a1
       <*> PEM.mapExpr sym f a2
       <*> PEM.mapExpr sym f a3

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
    <$> PPa.traverse (PEM.mapExpr sym f) (slRegOpValues regOp)
    <*> pure (slRegOpRepr regOp)
    <*> f (slRegOpEquiv regOp)


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
    <$> PPa.traverse (\(Const x) -> Const <$> W4H.mapExprPtr sym f x) (slMemOpValues memOp)
    <*> f (slMemOpEquiv memOp)
    <*> f (slMemOpCond memOp)


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
