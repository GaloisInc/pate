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

module Pate.Proof
  ( EquivTripleBody(..)
  , EquivTriple
  , VerificationStatus(..)
  , ProofApp(..)
  , ProofMemoryDomain(..)
  , IsProof
  , traverseProofApp
  , mapProofApp
  , ProofNonce(..)
  , ProofNonceExpr(..)
  , ProofNonceApp
  , ProofScope
  , unNonceProof
  , ProofExpr(..)
  , traverseProofExpr
  , collectProofExpr
  , appProofExpr
  , ProofTransformer(..)
  , transformProofApp
  , transformProofExpr
  , BlockSliceTransition(..)
  , transformBlockSlice
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
  -- leafs
  , ProofBlock
  , ProofRegister
  , ProofMemCell
  , ProofBV
  , ProofMacawValue
  , ProofPredicate
  , ProofCounterExample
  , ProofContext
  , ProofBlockExit
  ) where

import           GHC.TypeNats
import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Writer.Strict as CMW

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Map as MapF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT

import qualified Lang.Crucible.Types as CT

import qualified Pate.Equivalence as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.SimState as PS
import qualified Pate.Types as PT

import qualified What4.Interface as W4

---------------------------------------------
-- proof objects


-- | The body of an 'EquivTriple'.
data EquivTripleBody sym arch where
  EquivTripleBody ::
    {
      eqPair :: PT.BlockPair arch
      -- ^ the entry points that yield equivalent states on the post-domain
      -- after execution, assuming initially equivalent states on the pre-domain
    , eqPreDomain :: PE.StatePred sym arch
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


type family ProofBlock prf :: PT.WhichBinary -> *
type family ProofRegister prf :: MT.Type -> *
type family ProofPredicate prf :: *
type family ProofMemCell prf :: Nat -> *
type family ProofCounterExample prf :: *
type family ProofContext prf :: *
type family ProofBV prf :: Nat -> *
type family ProofBlockExit prf :: *
type family ProofMacawValue prf :: MT.Type -> *

class (OrdF (ProofRegister prf),
       OrdF (ProofMemCell prf)) => IsProof prf

data ProofNodeType =
    ProofTripleType
  | ProofFunctionCallType
  | ProofDomainType
  | ProofBlockSliceType
  | ProofStatusType

type ProofDomainType = 'ProofDomainType
type ProofTripleType = 'ProofTripleType
type ProofFunctionCallType = 'ProofFunctionCallType
type ProofBlockSliceType = 'ProofBlockSliceType
type ProofStatusType = 'ProofStatusType


data VerificationStatus ce =
    Unverified
  | VerificationSkipped
  | VerificationSuccess
  | VerificationFail ce
  deriving (Functor, Foldable, Traversable)


-- | An abstract proof object, representing the overall structure of an equivalence proof.
data ProofApp prf (node :: ProofNodeType -> *) (tp :: ProofNodeType) where
  -- | Proof that the top-level triple is satisfied, according to all possible
  -- exits from the given block slice
  ProofBlockSlice ::
    { prfBlockSliceTriple :: node ProofTripleType
    , prfBlockSliceCalls :: [(PT.PatchPair (ProofBlock prf), node ProofFunctionCallType)]
    , prfBlockSliceReturn :: Maybe (node ProofTripleType)
    , prfBlockSliceUnknownExit :: Maybe (node ProofTripleType)
    , prfBlockSliceTrans :: BlockSliceTransition prf
    } -> ProofApp prf node ProofBlockSliceType

  ProofFunctionCall ::
    { prfFunctionCallPre :: node ProofTripleType
    , prfFunctionCallBody :: node ProofBlockSliceType
    , prfFunctionCallContinue :: Maybe (node ProofBlockSliceType)
    } -> ProofApp prf node ProofFunctionCallType

  ProofTriple ::
    { prfTripleBlocks :: PT.PatchPair (ProofBlock prf)
    , prfTriplePreDomain :: node ProofDomainType
    , prfTriplePostDomain :: node ProofDomainType
    , prfTripleStatus :: node ProofStatusType
    
    } -> ProofApp prf node ProofTripleType

  ProofStatus ::
    { prfStatus :: VerificationStatus (ProofCounterExample prf) }
    -> ProofApp prf node ProofStatusType

  ProofDomain ::
    { prfDomainRegisters :: MM.RegState (ProofRegister prf) (Const (ProofPredicate prf))
    , prfDomainStackMemory :: ProofMemoryDomain prf
    , prfDomainGlobalMemory :: ProofMemoryDomain prf
    , prfDomainContext :: ProofContext prf
    }  -> ProofApp prf node ProofDomainType


data ProofMemoryDomain prf where
  ProofMemoryDomain ::
    { prfMemoryDomain :: MapF.MapF (ProofMemCell prf) (Const (ProofPredicate prf))
    , prfMemoryDomainPolarity :: ProofPredicate prf
    }  -> ProofMemoryDomain prf

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
  ProofFunctionCall a1 a2 a3 -> ProofFunctionCall
    <$> f a1
    <*> f a2
    <*> traverse f a3
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

mapProofApp ::
  (forall tp. node tp -> node' tp) ->
  ProofApp prf node utp ->
  ProofApp prf node' utp
mapProofApp f app = runIdentity $ traverseProofApp (\app' -> Identity $ f app') app

-- | A bundle of functions for converting the leafs of a proof graph
data ProofTransformer m prf prf' where
  ProofTransformer ::
    { prfPredTrans :: ProofPredicate prf -> m (ProofPredicate prf')
    , prfMemCellTrans :: forall n. ProofMemCell prf n -> m (ProofMemCell prf' n)
    , prfBVTrans :: forall n. ProofBV prf n -> m (ProofBV prf' n)
    , prfExitTrans :: ProofBlockExit prf -> m (ProofBlockExit prf')
    , prfValueTrans :: forall tp. ProofMacawValue prf tp -> m (ProofMacawValue prf' tp)
    , prfContextTrans :: ProofContext prf -> m (ProofContext prf')
    , prfConstraint ::
        forall a. ((IsProof prf'
                   , ProofRegister prf ~ ProofRegister prf'
                   , ProofBlock prf ~ ProofBlock prf'
                   , ProofCounterExample prf ~ ProofCounterExample prf') => a) -> a
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
  ProofFunctionCall a1 a2 a3 -> ProofFunctionCall
    <$> pure a1
    <*> pure a2
    <*> pure a3
  ProofTriple a1 a2 a3 a4 -> ProofTriple
    <$> pure a1
    <*> pure a2
    <*> pure a3
    <*> pure a4
    
  ProofStatus a1 -> ProofStatus
    <$> pure a1
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

appProofExpr ::
  forall m prf app tp.
  Monad m =>
  (forall tp2. app tp2 -> m (ProofApp prf app tp2)) ->
  ProofApp prf app tp ->
  m (ProofExpr prf tp)  
appProofExpr f app =
  ProofExpr <$> traverseProofApp go app
  where
     go :: forall tp2. app tp2 -> m (ProofExpr prf tp2)
     go app' = appProofExpr f =<< f app'

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

type family ProofScope prf :: *

-- | A nonce representing an indirect reference to a proof node.
data ProofNonce prf (tp :: ProofNodeType) where
  ProofNonce :: N.Nonce (ProofScope prf) tp -> ProofNonce prf tp

-- | A proof expression, annotated with nonces.
data ProofNonceExpr prf tp where
  ProofNonceExpr ::
    { prfNonce :: ProofNonce prf tp
    , prfParent :: Some (ProofNonce prf)
    , prfNonceBody :: ProofApp prf (ProofNonceExpr prf) tp
    } -> ProofNonceExpr prf tp

type ProofNonceApp prf tp = ProofApp prf (ProofNonceExpr prf) tp

unNonceProof :: ProofNonceExpr prf tp -> ProofExpr prf tp
unNonceProof prf = ProofExpr $ runIdentity $ (traverseProofApp (\e -> Identity $ unNonceProof e)) (prfNonceBody prf)

data BlockSliceTransition prf where
  BlockSliceTransition ::
    { slBlockPreState :: BlockSliceState prf
    , slBlockPostState :: BlockSliceState prf
    , slBlockExitCase :: PT.PatchPairC (ProofBlockExit prf)
    } -> BlockSliceTransition prf

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

data BlockSliceState prf where
  BlockSliceState ::
    { slMemState :: MapF.MapF (ProofMemCell prf) (BlockSliceMemOp prf)
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

data BlockSliceRegOp prf tp where
  BlockSliceRegOp ::
    { slRegOpValues :: PT.PatchPairC (ProofMacawValue prf tp)
    , slRegOpRepr :: CT.TypeRepr (MS.ToCrucibleType tp)
    -- | true if the values in this register are considered equivalent
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

data BlockSliceMemOp prf w where
  BlockSliceMemOp ::
    { slMemOpValues :: PT.PatchPairC (ProofBV prf (8 W4.* w))
    -- | true if the values of the memory operation are considered equivalent
    , slMemOpEquiv :: ProofPredicate prf
    -- | conditional on memory operation
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
