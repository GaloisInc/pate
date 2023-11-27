{-|
Module           : Pate.Ground
Copyright        : (c) Galois, Inc 2021
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Grounding symbolic expressions
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
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
-- {-# LANGUAGE NoMonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Ground 
  ( SymGroundEvalFn(..)
  , ground
  , groundValue
  , groundPartial
  , groundInfo
  , groundInfoNat
  , groundNat
  -- , isStackRegion
  , groundMacawEndCase
  , GroundSym(..)
  , IsGroundSym
  ) where

import           Data.Proxy

import           Numeric.Natural ( Natural )
import qualified Data.Kind as DK
import qualified Data.BitVector.Sized as BV

import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFGSlice as MCS

import qualified Lang.Crucible.Simulator as CS

import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Solver as PS

import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Partial as W4P
import qualified What4.Utils.AbstractDomains as W4

import qualified SemMC.Util as SU

import qualified Pate.Panic as PP
import Lang.Crucible.LLVM.MemModel.Pointer
import Lang.Crucible.Simulator.Intrinsics
import Lang.Crucible.CFG.Core
import qualified What4.Expr.Builder as WE
import qualified Control.Monad.IO.Class as IO
import Control.Monad.State (StateT (runStateT), gets, MonadState (get), MonadTrans (lift), modify)
import qualified Data.Parameterized.TraversableFC as TFC
import Control.Applicative (Const (..))
import qualified What4.ExprHelpers as WEH
import qualified Data.Set as Set
import Data.Coerce
import           Lang.Crucible.Simulator.RegMap (SymSequence(..))
import Unsafe.Coerce (unsafeCoerce)
import qualified What4.Concrete as W4
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Map as Map
import qualified What4.PredMap as WPM

-- | This module allows a model from What4 to be captured with respect to
-- some expression-containing type. This is used to ground concrete counter-examples
-- from the verifier which prove inequivalence of block slices.

data GroundSym (k :: W4.BaseType -> DK.Type) = GroundSym

data GroundInfo k tp where
  GroundInfo :: 
    { grndMetaData :: Maybe (k tp)
    , grndValue :: W4.ConcreteVal tp 
    } -> GroundInfo k tp

data GroundAnnotation k tp = GroundAnnotation (W4.BaseTypeRepr tp)

instance TestEquality (GroundAnnotation k) where
  testEquality (GroundAnnotation r1) (GroundAnnotation r2) = testEquality r1 r2

instance OrdF (GroundAnnotation k) where
  compareF (GroundAnnotation r1) (GroundAnnotation r2) = compareF r1 r2

instance HashableF (GroundAnnotation k) where
  hashWithSaltF salt (GroundAnnotation r) = hashWithSalt salt r

type instance W4.SymExpr (GroundSym k) = GroundInfo k
type instance W4.SymAnnotation (GroundSym k) = GroundAnnotation k

instance Hashable (W4.ConcreteVal tp) where
  hashWithSalt salt v = hashWithSaltF salt v

instance HashableF W4.ConcreteVal where
  hashWithSaltF salt v = case v of
    W4.ConcreteBool b -> hashWithSalt salt' b
    W4.ConcreteInteger i -> hashWithSalt salt' i
    W4.ConcreteReal r -> hashWithSalt salt' r
    W4.ConcreteFloat a b -> hashWithSalt (hashWithSaltF salt' a) b
    W4.ConcreteString s -> hashWithSalt salt' s
    W4.ConcreteComplex c -> hashWithSalt salt' c
    W4.ConcreteBV _w bv -> hashWithSalt salt' (BV.asUnsigned bv)
    W4.ConcreteArray _a b c -> hashWithSalt (hashWithSalt salt' b) c
    W4.ConcreteStruct vs -> hashWithSalt salt' vs
    where 
      salt' = hashWithSalt salt (W4.concreteType v)

instance HashableF (GroundInfo k) where
  hashWithSaltF salt (GroundInfo _ v) = hashWithSaltF salt v

instance (OrdF k, TestEquality k) => TestEquality (GroundInfo k) where
  testEquality a b = case compareF a b of
    EQF -> Just Refl
    _ -> Nothing 


instance OrdF k => OrdF (GroundInfo k) where
  compareF (GroundInfo k1 r1) (GroundInfo k2 r2) = 
    lexCompareF r1 r2 $ case (k1, k2) of
      (Just k1_, Just k2_) -> compareF k1_ k2_
      (Nothing,Nothing) -> EQF
      (Just{},Nothing) -> LTF
      (Nothing,Just{}) -> GTF

type IsGroundSym sym k = sym ~ GroundSym k

valToValue :: W4.ConcreteVal tp -> W4.ConcreteValue tp
valToValue v = case v of
    W4.ConcreteBool b -> b
    W4.ConcreteInteger i -> i
    W4.ConcreteReal r -> r
    W4.ConcreteFloat{} -> ()
    W4.ConcreteString s -> s
    W4.ConcreteComplex c -> c
    W4.ConcreteBV _w bv -> BV.asUnsigned bv
    W4.ConcreteArray{} -> ()
    W4.ConcreteStruct vs -> TFC.fmapFC (W4.ConcreteValueWrapper . valToValue) vs



instance W4.HasAbsValue (GroundInfo k) where
  getAbsValue info = W4.avSingle (W4.concreteType (grndValue info)) (valToValue (grndValue info))

instance W4.IsExpr (GroundInfo k) where
  asConstantPred info = Just $ W4.fromConcreteBool (grndValue info)
  asInteger info = Just $ W4.fromConcreteInteger (grndValue info)
  integerBounds info = W4.singleRange (W4.fromConcreteInteger (grndValue info))
  asRational info = Just $ W4.fromConcreteReal (grndValue info)
  asFloat info = case grndValue info of
    W4.ConcreteFloat _ f -> Just f
  rationalBounds info = W4.singleRange (W4.fromConcreteReal (grndValue info))
  asComplex info = Just $ W4.fromConcreteComplex (grndValue info)
  asBV info = Just $ W4.fromConcreteBV (grndValue info)
  unsignedBVBounds info = case grndValue info of
    W4.ConcreteBV _w bv -> Just (BV.asUnsigned bv, BV.asUnsigned bv)
  signedBVBounds info = case grndValue info of
    W4.ConcreteBV w bv -> Just (BV.asSigned w bv, BV.asSigned w bv)
  asAffineVar _ = Nothing
  asString info = Just $ W4.fromConcreteString (grndValue info)
  stringInfo info = W4.stringLiteralInfo $ W4.fromConcreteString (grndValue info)
  asConstantArray info = case grndValue info of
    W4.ConcreteArray _ d upd | Map.null upd -> Just $ GroundInfo Nothing d
    _ -> Nothing
  asStruct info = case grndValue info of
    W4.ConcreteStruct s -> Just $ TFC.fmapFC (GroundInfo Nothing) s
  exprType info = W4.concreteType (grndValue info)
  printSymExpr info = W4.ppConcrete (grndValue info)
  unsafeSetAbstractValue _ = id

instance WEH.HasIntegerToNat (GroundSym k) where
  -- Fixme: SymNat interface requires IsExprBuilder, but we can
  -- just coerce an int into a SymNat here by checking it statically
  intToNat _ info@(GroundInfo metadata (W4.ConcreteInteger v)) = case v >= 0 of
    True -> return $ unsafeCoerce info
    False -> return $ unsafeCoerce (GroundInfo metadata (W4.ConcreteInteger 0))

instance WPM.HasPredOps (GroundSym k) where

-- | Retrieve the ground information of a symbolic expression with respect to the
-- grounding environment bound by 'IsGroundSym'
groundInfo :: forall k tp.  W4.SymExpr (GroundSym k) tp -> Maybe (k tp)
groundInfo e = grndMetaData e

-- | Retrieve the ground information of a symbolic natural with respect to the
-- grounding environment bound by 'IsGroundSym'
groundInfoNat :: W4.SymNat (GroundSym k) -> (Maybe (k W4.BaseIntegerType), Natural)
groundInfoNat e =
  let
    e_int = W4.natToIntegerPure e
    info = groundInfo $ e_int
  in (info, integerToNat (groundValue e_int))

-- TODO: this breaks the abstraction boundary for block ends
-- (see: https://github.com/GaloisInc/pate/issues/196)

-- | Retrieve the concrete 'MS.MacawBlockEndCase' of
-- a symbolic 'MS.MacawBlockEndType' with respect to the
-- grounding environment bound by 'IsGroundSym'
groundMacawEndCase ::
  forall arch k.
  Proxy arch ->
  CS.RegValue (GroundSym k) (MCS.MacawBlockEndType arch) ->
  MCS.MacawBlockEndCase
groundMacawEndCase _ (_ Ctx.:> CS.RV blend Ctx.:> _) =
  toEnum $ fromIntegral $ groundValue blend

-- | Retrieve the concrete value of a symbolic expression with respect to the
-- grounding environment bound by 'IsGroundSym'
groundValue :: forall k tp. W4.SymExpr (GroundSym k) tp -> W4.ConcreteValue tp
groundValue e = valToValue $ grndValue e

groundVal :: forall k tp. W4.SymExpr (GroundSym k) tp -> W4.ConcreteVal tp
groundVal e = grndValue e

-- | Ground the predicate in a 'W4P.PartExpr' with respect to the grounding environment
-- bound by 'IsGroundSym' and return the inner value if it evaluates to True.
groundPartial :: W4P.PartExpr (W4.Pred (GroundSym k)) a -> Maybe a
groundPartial = \case
  W4P.Unassigned -> Nothing
  W4P.PE p v -> case groundValue p of
    True -> Just v
    False -> Nothing

-- | Retrieve the concrete value of a symbolic natural with respect to the
-- grounding environment bound by 'IsGroundSym'
groundNat :: W4.SymNat (GroundSym k) -> Natural
groundNat e = snd $ groundInfoNat e

-- | Clamp an integer to be a positive natural (reflecting the semantics of
-- 'W4.integerToNat' for a concrete value).
integerToNat :: Integer -> Natural
integerToNat i
  | i >= 0 = fromIntegral i
  | otherwise = 0

litToConcrete :: W4.IndexLit tp -> W4.ConcreteVal tp
litToConcrete = \case
  W4.IntIndexLit i -> W4.ConcreteInteger i
  W4.BVIndexLit w bv -> W4.ConcreteBV w bv

groundToVal :: W4.BaseTypeRepr tp -> W4G.GroundValue tp -> W4.ConcreteVal tp
groundToVal t v = case t of
  W4.BaseBoolRepr -> W4.ConcreteBool v
  W4.BaseIntegerRepr -> W4.ConcreteInteger v
  W4.BaseRealRepr -> W4.ConcreteReal v
  W4.BaseBVRepr w -> W4.ConcreteBV w v
  W4.BaseFloatRepr fp -> W4.ConcreteFloat fp v
  W4.BaseComplexRepr -> W4.ConcreteComplex v
  W4.BaseStringRepr{} -> W4.ConcreteString v
  W4.BaseArrayRepr idx_repr v_repr -> case v of
    W4G.ArrayMapping{} -> error "groundToVal: unsupported"
    W4G.ArrayConcrete gv upd -> 
      W4.ConcreteArray idx_repr (groundToVal v_repr gv)
      (Map.fromList $ (map (\(idx, x) -> (TFC.fmapFC litToConcrete idx, groundToVal v_repr x)))
        (Map.toList upd))
  W4.BaseStructRepr reprs -> W4.ConcreteStruct $ 
    Ctx.zipWith (\repr (W4G.GVW gv) -> groundToVal repr gv) reprs v 

-- | Ground a value via its 'PEM.ExprMappable2' implementation, by swapping out
-- the 'sym' parameter for a 'GroundSym'. 
ground ::
  forall sym m k a b.
  PS.ValidSym sym =>
  PEM.ExprMappable2 sym (GroundSym k) a b =>
  OrdF k =>
  IO.MonadIO m =>
  sym ->
  -- | Grounding inner expressions
  SymGroundEvalFn sym k ->
  a ->
  m b
ground sym (SymGroundEvalFn evalFn mkinfo) a = do
  cache <- WE.newIdxCache
  let
    f' :: forall tp. W4.SymExpr sym tp -> m (W4.SymExpr (GroundSym k) tp)
    f' e = WE.idxCacheEval cache e $ do
      gv <- case SU.exprToGroundVal @sym (W4.exprType e) e of
        Just gv -> return gv
        Nothing -> IO.liftIO $ W4G.groundEval evalFn e
      info <- IO.liftIO $ mkinfo e gv
      return $ GroundInfo info (groundToVal (W4.exprType e) gv)
  let
    constraints :: 
      forall x. ((PEM.HasSymComparator sym (GroundSym k), PEM.ValidTargetSym (GroundSym k)) => x) -> x  
    constraints x = let ?compareSym = Nothing in x
  constraints $ PEM.mapExpr2 sym GroundSym f' a

data SymGroundEvalFn sym k where
  SymGroundEvalFn ::
    W4G.GroundEvalFn scope ->
    (forall tp. W4.SymExpr (WE.ExprBuilder scope solver fs) tp -> W4G.GroundValue tp -> IO (Maybe (k tp))) -> 
    SymGroundEvalFn (WE.ExprBuilder scope solver fs) k


-- trivial instance - grounded values should not be modified


{-
instance SymCoercable sym1 sym2 a => SymCoercable sym1 sym2 (SymSequence sym1 a) where
  type SymCoerceTo sym2 (SymSequence sym1 a) = SymSequence sym2 (SymCoerceTo sym2 a)
-}