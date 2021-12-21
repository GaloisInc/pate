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

module Pate.Proof
  ( EquivTripleBody(..)
  , EquivTriple
  , VerificationStatus(..)
  , ProofApp(..)
  , ProofMemoryDomain(..)
  , IsProof
  , IsBoolLike(..)
  , traverseProofApp
  , mapProofApp
  , emptyDomain
  , appDomain
  , ProofFunctionCallMetadata(..)
  , ProofNonce(..)
  , proofNonceValue
  , ProofNonceExpr(..)
  , ProofNonceApp
  , ProofScope
  , unNonceProof
  , ProofExpr(..)
  , collectProofExpr
  , ProofTransformer(..)
  , transformProofApp
  , transformProofExpr
  , BlockSliceTransition(..)
  , transformBlockSlice
  , transformBlockSliceRegOp
  , transformBlockSliceMemOp
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
  , type ProofInlineType
  -- leafs
  , ProofBlock
  , ProofRegister
  , ProofMemCell
  , ProofBV
  , ProofMacawValue
  , ProofPredicate
  , ProofCounterExample
  , ProofCondition
  , ProofContext
  , ProofBlockExit
  , ProofInlinedResult
  ) where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Writer.Strict as CMW
import qualified Data.Kind as DK
import           GHC.TypeNats
import           Numeric.Natural ( Natural )

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Map as MapF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT

import qualified Lang.Crucible.Types as CT

import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.ExprMappable as PEM
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS

import qualified What4.Interface as W4

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


-- | A concrete block (instantiated to 'Pate.Type.ConcreteBlock')
type family ProofBlock prf :: PBi.WhichBinary -> DK.Type
-- | A machine register (instantiated to 'Data.Macaw.CFG.AssignRhs.ArchReg')
type family ProofRegister prf :: MT.Type -> DK.Type
-- | A predicate (instantiated to either 'What4.Interface.Pred' or 'Bool')
type family ProofPredicate prf :: DK.Type
-- | A memory location (instantiated to either 'Pate.MemCell.MemCell' or 'Pate.Instances.GroundMemCell')
type family ProofMemCell prf :: Nat -> DK.Type
-- | A proof counterexample (instantiated to 'Pate.Proof.Instances.InequivalenceResult')
type family ProofCounterExample prf :: DK.Type
-- | Side conditions for a proof (instantiated to 'Pate.Proof.Instances.CondEquivalenceResult')
type family ProofCondition prf :: DK.Type
-- | Additional ontext for a domain (instantiated to a 'Pate.SimState' pair)
type family ProofContext prf :: DK.Type
-- | A bitvector value
-- (instantiated to 'Pate.Proof.Instances.SymBV' which wraps 'Lang.Crucible.LLVM.Types.LLVMPtr',
-- or 'Pate.Proof.Instances.GroundBV')
type family ProofBV prf :: Nat -> DK.Type
-- | A classification for the exit condition of a block.
-- (instantiated to either a 'Data.Macaw.Symbolic.MacawBlockEndType' term or 'Pate.Proof.Instances.GroundBlockExit')
type family ProofBlockExit prf :: DK.Type
-- | A register value, parameterized over a macaw type.
-- (instantiated to either 'Pate.SimulatorRegisters.MacawRegEntry' or 'Pate.Proof.Instances.GroundMacawValue')
type family ProofMacawValue prf :: MT.Type -> DK.Type
-- | The results of the inline-callee analysis (instantiated to 'Pate.Verification.MemoryLog.WriteSummary')
type family ProofInlinedResult prf :: DK.Type

class (MM.RegisterInfo (ProofRegister prf),
       OrdF (ProofMemCell prf)) => IsProof prf

class IsBoolLike prf m where
  proofPredAnd :: ProofPredicate prf -> ProofPredicate prf -> m (ProofPredicate prf)
  proofPredOr :: ProofPredicate prf -> ProofPredicate prf -> m (ProofPredicate prf)
  proofPredEq :: ProofPredicate prf -> ProofPredicate prf -> m (ProofPredicate prf)
  proofPredTrue :: m (ProofPredicate prf)
  proofPredFalse :: m (ProofPredicate prf)
  proofPredAssertEqual :: ProofPredicate prf -> ProofPredicate prf  -> m ()

data ProofNodeType =
    ProofTripleType
  | ProofFunctionCallType
  | ProofDomainType
  | ProofBlockSliceType
  | ProofStatusType
  | ProofInlineType

type ProofDomainType = 'ProofDomainType
type ProofTripleType = 'ProofTripleType
type ProofFunctionCallType = 'ProofFunctionCallType
type ProofBlockSliceType = 'ProofBlockSliceType
type ProofStatusType = 'ProofStatusType
type ProofInlineType = 'ProofInlineType


data VerificationStatus ce =
    Unverified
  | VerificationSkipped
  | VerificationSuccess
  | VerificationFail ce
  deriving (Functor, Foldable, Traversable)

instance PEM.ExprMappable sym a => PEM.ExprMappable sym (VerificationStatus a) where
  mapExpr sym f = traverse (PEM.mapExpr sym f)

data ProofFunctionCallMetadata where
  ProofFunctionCallMetadata ::
    { prfFunctionCallMetadataAddress :: PA.ConcreteAddress arch
    } -> ProofFunctionCallMetadata

-- | An abstract proof object, representing the overall structure of an equivalence proof.
-- The type parameter 'prf' abstracts this structure over the specific types used in the proof,
-- which may be symbolic or concrete (i.e. ground terms from a counterexample).
-- The two instantiations for this parameter are given in
-- 'Pate.Proof.Instances'.
data ProofApp prf (node :: ProofNodeType -> DK.Type) (tp :: ProofNodeType) where
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
    , prfBlockSliceCalls :: [(PPa.PatchPair (ProofBlock prf), node ProofFunctionCallType)]
      -- | Proof that the post-domain is satisfied if this block slice exits with a return.
    , prfBlockSliceReturn :: Maybe (node ProofTripleType)
      -- | Proof that the post-domain is satisfied if this block slice exits with an unknown branch class.
    , prfBlockSliceUnknownExit :: Maybe (node ProofTripleType)
      -- | The symbolic semantics of the head of this block slice (i.e. from the start of the triple
      -- to some exit condition, either a return or some function call).
    , prfBlockSliceTrans :: BlockSliceTransition prf
    } -> ProofApp prf node ProofBlockSliceType

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
    { prfInlinedBlocks :: PPa.PatchPair (ProofBlock prf)
    , prfInlinedResults :: ProofInlinedResult prf
    } -> ProofApp prf node ProofBlockSliceType

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
    , prfFunctionCallMetadata :: ProofFunctionCallMetadata
    } -> ProofApp prf node ProofFunctionCallType

  -- | Proof that two block slices are equal according to a given post-domain, assuming
  -- a given pre-domain. The scope of the slice is dependent on which parent node
  -- this is attached to.
  ProofTriple ::
    { prfTripleBlocks :: PPa.PatchPair (ProofBlock prf)
    , prfTriplePreDomain :: node ProofDomainType
    , prfTriplePostDomain :: node ProofDomainType
    , prfTripleStatus :: node ProofStatusType
    } -> ProofApp prf node ProofTripleType

  -- | The status of some verification problem: either producing a successful result
  -- or yielding a counterexample. The resulting
  -- predicate represents an additional assumption required for equivalence to hold.
  -- (i.e. conditional equivalence).
  -- In the case of inequality, the predicate simply false
  ProofStatus ::
    { prfStatus :: VerificationStatus (ProofCounterExample prf, ProofCondition prf)
    } -> ProofApp prf node ProofStatusType

  -- | The domain of an equivalence problem: representing the state that is either
  -- assumed (in a pre-domain) or proven (in a post-domain) to be equivalent.
  ProofDomain ::
    { -- | Each register is considered to be in this domain if the given predicate is true.
      prfDomainRegisters :: MM.RegState (ProofRegister prf) (Const (ProofPredicate prf))
      -- | The memory domain that is specific to stack variables.
    , prfDomainStackMemory :: ProofMemoryDomain prf
      -- | The memory domain that is specific to non-stack (i.e. global) variables.
    , prfDomainGlobalMemory :: ProofMemoryDomain prf
      -- | Additional context for the domain. In the case of symbolic leafs, this
      -- corresponds to the bound variables appearing in the symbolic terms in this domain.
    , prfDomainContext :: ProofContext prf
    }  -> ProofApp prf node ProofDomainType

-- | A memory domain for an equivalence problem.
data ProofMemoryDomain prf where
  ProofMemoryDomain ::
    { -- | Associating each memory location (i.e. an address and a number of bytes) with
      -- a predicate.
      prfMemoryDomain :: MapF.MapF (ProofMemCell prf) (Const (ProofPredicate prf))
      -- | A predicate indicating if this domain is inclusive or exclusive.
      -- * For positive polarity:
      --   a location is in this domain if it is in the map, and its associated predicate
      --   is true.
      -- * For negative polarity:
      --   a location is in this domain if it is not in the map,
      --   or it is in the map and its associated predicate is false.
    , prfMemoryDomainPolarity :: ProofPredicate prf
    }  -> ProofMemoryDomain prf

-- | Traverse the nodes of a 'ProofApp', changing the
-- recursive 'node' type while leaving the leafs (i.e. the 'prf' type) unchanged.
traverseProofApp ::
  Applicative m =>
  (forall tp. node tp -> m (node' tp)) ->
  ProofApp prf node utp ->
  m ((ProofApp prf node') utp)
traverseProofApp f = \case
  ProofBlockSlice a1 a2 a3 a4 a5 -> ProofBlockSlice
    <$> f a1
    <*> traverse (\(blks,v) -> (,) <$> pure blks <*> f v) a2
    <*> traverse f a3
    <*> traverse f a4
    <*> pure a5
  ProofInlinedCall pp res -> pure (ProofInlinedCall pp res)
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
    
  ProofStatus a1 -> ProofStatus
    <$> pure a1
  ProofDomain a1 a2 a3 a4 -> ProofDomain
    <$> pure a1
    <*> pure a2
    <*> pure a3
    <*> pure a4

-- | Map over the nodes of a 'ProofApp', changing the
-- 'node' type while leaving the leafs (i.e. the 'prf' type) unchanged.
mapProofApp ::
  (forall tp. node tp -> node' tp) ->
  ProofApp prf node utp ->
  ProofApp prf node' utp
mapProofApp f app = runIdentity $ traverseProofApp (\app' -> Identity $ f app') app

-- | A bundle of functions for converting the leafs of a proof graph
data ProofTransformer m prf prf' where
  ProofTransformer ::
    {
      prfPredTrans :: ProofPredicate prf -> m (ProofPredicate prf')
    , prfMemCellTrans :: forall n. ProofMemCell prf n -> m (ProofMemCell prf' n)
    , prfBVTrans :: forall n. ProofBV prf n -> m (ProofBV prf' n)
    , prfExitTrans :: ProofBlockExit prf -> m (ProofBlockExit prf')
    , prfValueTrans :: forall tp. ProofMacawValue prf tp -> m (ProofMacawValue prf' tp)
    , prfContextTrans :: ProofContext prf -> m (ProofContext prf')
    , prfCounterExampleTrans :: ProofCounterExample prf -> m (ProofCounterExample prf')
    , prfConditionTrans :: ProofCondition prf -> m (ProofCondition prf')
    , prfConstraint ::
        forall a. ((IsProof prf'
                   , ProofRegister prf ~ ProofRegister prf'
                   , ProofBlock prf ~ ProofBlock prf'
                   , ProofInlinedResult prf ~ ProofInlinedResult prf') => a) -> a
    } -> ProofTransformer m prf prf'

transformMemDomain ::
  forall m prf prf'.
  Applicative m =>
  ProofTransformer m prf prf' ->
  ProofMemoryDomain prf ->
  m (ProofMemoryDomain prf')
transformMemDomain f (ProofMemoryDomain dom pol) = prfConstraint f $ ProofMemoryDomain
  <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList dom)))
  <*> prfPredTrans f pol
    where
      transMemCell :: MapF.Pair (ProofMemCell prf) (Const (ProofPredicate prf))
        -> m (MapF.Pair (ProofMemCell prf') (Const (ProofPredicate prf')))
      transMemCell (MapF.Pair cell (Const p)) = MapF.Pair
        <$> prfMemCellTrans f cell
        <*> (Const <$> (prfPredTrans f p))

-- | Traverse the leafs of 'ProofApp' with the given 'ProofTransformer', leaving the
-- 'node' type unchanged, but changing the 'prf' type.
transformProofApp ::
  Applicative m =>
  ProofTransformer m prf prf' ->
  ProofApp prf node utp ->
  m ((ProofApp prf' node) utp)
transformProofApp f app = prfConstraint f $ case app of
  ProofBlockSlice a1 a2 a3 a4 a5 -> ProofBlockSlice
    <$> pure a1
    <*> pure a2
    <*> pure a3
    <*> pure a4
    <*> transformBlockSlice f a5
  ProofInlinedCall pp res -> pure (ProofInlinedCall pp res)
  ProofFunctionCall a1 a2 a3 md -> ProofFunctionCall
    <$> pure a1
    <*> pure a2
    <*> pure a3
    <*> pure md
  ProofTriple a1 a2 a3 a4 -> ProofTriple
    <$> pure a1
    <*> pure a2
    <*> pure a3
    <*> pure a4
    
  ProofStatus a1 -> ProofStatus
    <$> traverse (\(cex, cond) -> (,) <$> prfCounterExampleTrans f cex <*> prfConditionTrans f cond) a1
  ProofDomain a1 a2 a3 a4 -> ProofDomain
    <$> MM.traverseRegsWith (\_ (Const v) -> Const <$> prfPredTrans f v) a1
    <*> transformMemDomain f a2
    <*> transformMemDomain f a3
    <*> prfContextTrans f a4


-- | A 'ProofExpr' is an direct proof representation, where
-- nodes hold completed sub-proofs.
data ProofExpr prf tp where
  ProofExpr :: { unApp :: ProofApp prf (ProofExpr prf) tp } -> ProofExpr prf tp

-- | Traverse all sub-expressions of a 'ProofExpr'
traverseProofExpr ::
  Monad m =>
  (forall tp'. ProofExpr prf tp' -> m (ProofExpr prf tp')) ->
  ProofExpr prf tp ->
  m (ProofExpr prf tp)
traverseProofExpr f e =
  ProofExpr <$> (traverseProofApp (traverseProofExpr f) =<< (unApp <$> f e))

transformProofExpr ::
  Monad m =>
  ProofTransformer m prf prf' ->
  ProofExpr prf tp ->
  m (ProofExpr prf' tp)
transformProofExpr f (ProofExpr app) =
  ProofExpr <$> (traverseProofApp (transformProofExpr f) =<< (transformProofApp f app))

-- | Collect results from all sub-expressions
collectProofExpr ::
  forall w prf tp.
  Monoid w =>
  (forall tp'. ProofExpr prf tp' -> w) ->
  ProofExpr prf tp ->
  w
collectProofExpr f e_outer = runIdentity $ CMW.execWriterT (traverseProofExpr go e_outer)
  where
    go :: ProofExpr prf tp' -> CMW.WriterT w Identity (ProofExpr prf tp')
    go e = do
      CMW.tell (f e)
      return e

-- | A domain expression is actually independent of the 'app' parameter, so we can
-- project it to any one.
appDomain ::
  ProofExpr prf ProofDomainType ->
  ProofApp prf app ProofDomainType
appDomain (ProofExpr (ProofDomain regs stack glob domCtx)) = ProofDomain regs stack glob domCtx

emptyDomain ::
  forall prf m.
  Monad m =>
  IsProof prf =>
  IsBoolLike prf m =>
  ProofContext prf ->
  m (ProofExpr prf ProofDomainType)
emptyDomain domCtx = do
  regs <- MM.mkRegStateM (\_ -> Const <$> proofPredFalse @prf)
  stack <- emptyMemDomain
  globs <- emptyMemDomain
  return $ ProofExpr $ ProofDomain regs stack globs domCtx

emptyMemDomain ::
  forall prf m.
  Monad m =>
  IsBoolLike prf m =>
  m (ProofMemoryDomain prf)
emptyMemDomain = do
  falsePred <- proofPredFalse @prf
  return $ ProofMemoryDomain MapF.empty falsePred

type family ProofScope prf :: DK.Type

-- | A nonce representing an indirect reference to a proof node.
data ProofNonce prf (tp :: ProofNodeType) where
  ProofNonce :: N.Nonce (ProofScope prf) tp -> ProofNonce prf tp

deriving instance Show (ProofNonce prf tp)

instance ShowF (ProofNonce prf) where
  showF (ProofNonce n) = showF n

instance TestEquality (ProofNonce prf) where
  testEquality (ProofNonce n1) (ProofNonce n2) = testEquality n1 n2

instance OrdF (ProofNonce prf) where
  compareF (ProofNonce n1) (ProofNonce n2) = compareF n1 n2

proofNonceValue :: ProofNonce prf tp -> Natural
proofNonceValue (ProofNonce n) = fromIntegral (N.indexValue n)

-- | A proof expression, annotated with nonces.
data ProofNonceExpr prf tp where
  ProofNonceExpr ::
    { prfNonce :: ProofNonce prf tp
    , prfParent :: Some (ProofNonce prf)
    , prfNonceBody :: ProofApp prf (ProofNonceExpr prf) tp
    } -> ProofNonceExpr prf tp

type ProofNonceApp prf tp = ProofApp prf (ProofNonceExpr prf) tp

-- | Strip the nonces from a 'ProofNonceExpr', yielding an equivalent 'ProofExpr'.
unNonceProof :: ProofNonceExpr prf tp -> ProofExpr prf tp
unNonceProof prf = ProofExpr $ mapProofApp unNonceProof (prfNonceBody prf)

-- | The semantics of executing two block slices: an original and a patched variant.
-- The type parameter 'prf' abstracts this over the specific types,
-- which may be symbolic or concrete (i.e. ground terms from a counterexample).
data BlockSliceTransition prf where
  BlockSliceTransition ::
    { -- | The pre-states of the blocks prior to execution.
      slBlockPreState :: BlockSliceState prf
      -- | The post-states of the blocks after execution.
    , slBlockPostState :: BlockSliceState prf
      -- | The exit condition of the blocks (i.e. return, function call, etc)
    , slBlockExitCase :: PPa.PatchPairC (ProofBlockExit prf)
    } -> BlockSliceTransition prf

-- | Traverse the leafs of a 'BlockSliceTransition' with the given 'ProofTransformer',
-- changing the 'prf' type. In particular, this is used to ground a counterexample.
transformBlockSlice ::
  Applicative m =>
  ProofTransformer m prf prf' ->
  BlockSliceTransition prf ->
  m (BlockSliceTransition prf')
transformBlockSlice f (BlockSliceTransition a1 a2 a3) =
    BlockSliceTransition
      <$> transformBlockSliceState f a1
      <*> transformBlockSliceState f a2
      <*> traverse (prfExitTrans f) a3

-- | The machine state of two block slices: original and patched.
data BlockSliceState prf where
  BlockSliceState ::
    { -- | The state of memory for all memory locations that are associated with this
      -- slice: i.e. the pre-state contains all reads and the post-state contains all writes.
      slMemState :: MapF.MapF (ProofMemCell prf) (BlockSliceMemOp prf)
      -- | The state of all registers.
    , slRegState :: MM.RegState (ProofRegister prf) (BlockSliceRegOp prf)
    } -> BlockSliceState prf

transformBlockSliceState ::
  forall m prf prf'.
  Applicative m =>
  ProofTransformer m prf prf' ->
  BlockSliceState prf ->
  m (BlockSliceState prf')
transformBlockSliceState f (BlockSliceState a1 a2) = prfConstraint f $
    BlockSliceState
      <$> (MapF.fromList <$> (traverse transMemCell (MapF.toList a1)))
      <*> MM.traverseRegsWith (\_ v -> transformBlockSliceRegOp f v) a2
  where
    transMemCell :: MapF.Pair (ProofMemCell prf) (BlockSliceMemOp prf)
      -> m (MapF.Pair (ProofMemCell prf') (BlockSliceMemOp prf'))
    transMemCell (MapF.Pair cell mop) = MapF.Pair
      <$> prfMemCellTrans f cell
      <*> transformBlockSliceMemOp f mop

-- | The original and patched values for a register.
data BlockSliceRegOp prf tp where
  BlockSliceRegOp ::
    { slRegOpValues :: PPa.PatchPairC (ProofMacawValue prf tp)
    , slRegOpRepr :: CT.TypeRepr (MS.ToCrucibleType tp)
    -- | True if these values are considered equivalent (without
    -- considering a particular equivalence domain).
    , slRegOpEquiv :: ProofPredicate prf
    } -> BlockSliceRegOp prf tp

transformBlockSliceRegOp ::
  Applicative m =>
  ProofTransformer m prf prf' ->
  BlockSliceRegOp prf tp ->
  m (BlockSliceRegOp prf' tp)
transformBlockSliceRegOp f (BlockSliceRegOp a1 a2 a3) =
    BlockSliceRegOp
      <$> traverse (prfValueTrans f) a1
      <*> pure a2
      <*> prfPredTrans f a3

-- | The original and patched values for a memory location, where
-- 'w' represents the number of bytes read or written.
data BlockSliceMemOp prf w where
  BlockSliceMemOp ::
    { slMemOpValues :: PPa.PatchPairC (ProofBV prf (8 W4.* w))
    -- | True if these values are considered equivalent (without
    -- considering a particular equivalence domain).
    , slMemOpEquiv :: ProofPredicate prf
    -- | True if this memory operation is "live".
    , slMemOpCond :: ProofPredicate prf
    } -> BlockSliceMemOp prf w


transformBlockSliceMemOp ::
  Applicative m =>
  ProofTransformer m prf prf' ->
  BlockSliceMemOp prf tp ->
  m (BlockSliceMemOp prf' tp)
transformBlockSliceMemOp f (BlockSliceMemOp a1 a2 a3) =
    BlockSliceMemOp
      <$> traverse (prfBVTrans f) a1
      <*> prfPredTrans f a2
      <*> prfPredTrans f a3

foldrMBlockStateLocs ::
  Monad m =>
  (forall tp. ProofRegister prf tp -> BlockSliceRegOp prf tp -> b -> m b) ->
  (forall w. ProofMemCell prf w -> BlockSliceMemOp prf w -> b -> m b) ->
  b ->
  BlockSliceState prf ->
  m b
foldrMBlockStateLocs f_reg f_mem b (BlockSliceState a1 a2) = do
  b' <- MapF.foldrMWithKey f_mem b a1
  MapF.foldrMWithKey f_reg b' (MM.regStateMap a2) 
