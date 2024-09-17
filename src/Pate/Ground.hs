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

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Ground 
  ( IsGroundSym
  , Grounded
  , GroundData
  , GroundInfo(..)
  , withGroundSym
  , traverseWithGroundSym
  , ground
  , groundValue
  , groundPartial
  , groundInfo
  , groundInfoNat
  , groundNat
  , isStackRegion
  , groundMacawEndCase
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

import qualified SemMC.Util as SU

import qualified Pate.Panic as PP
import qualified Control.Monad.IO.Class as IO

-- | This module allows a model from What4 to be captured with respect to
-- some expression-containing type. This is used to ground concrete counter-examples
-- from the verifier which prove inequivalence of block slices.
-- A 'Grounded' value contains a binding
-- environment which is sufficient to ground any of the inner expressions of
-- the type via 'groundValue'. Here an "inner" expression is defined by the
-- traversal of the type according to 'PEM.ExprMappable'.


-- | A value wrapped with a grounding environment, sufficient to
-- concretely evaluate its inner expressions.
-- The 'sym' parameter for the type is existentially quantified, and exposed
-- through 'withGroundSym', indicating that any expressions parameterized over
-- this new 'sym' parameter can necessarily be grounded with 'groundValue'.
data Grounded (a :: sym -> DK.Type) where
  Grounded ::
    { _grndVal :: a sym
    , _grndData :: GroundData sym
    } -> Grounded a

-- | Interpret the given 'Grounded' by establishing 'IsGroundSym' for its 'sym' type
-- parameter, which implicitly binds the grounding environment used by
-- 'groundValue', 'groundInfo', etc.
withGroundSym ::
  Grounded tp ->
  (forall grnd. IsGroundSym grnd => tp grnd -> a) ->
  a
withGroundSym (Grounded v d@(GroundData{})) f = let ?grndData = d in f v

-- | Traverse the given 'Grounded' by establishing 'IsGroundSym' for its 'sym' type
-- parameter, which implicitly binds the grounding environment used by
-- 'groundValue', 'groundInfo', etc.
traverseWithGroundSym ::
  Applicative m =>
  Grounded a ->
  (forall grnd. IsGroundSym grnd => a grnd -> m (b grnd)) ->
  m (Grounded b)
traverseWithGroundSym (Grounded v d@(GroundData{})) f =
  let ?grndData = d
  in Grounded <$> f v <*> pure d

-- | Storage for the ground value of a term, including metadata.
data GroundInfo (tp :: W4.BaseType) where
  GroundInfo ::
    { -- | This can only be computed from the symbolic term with respect to
      -- a specific model (see 'Pate.CounterExample.getPointerTags'),
      -- and so it needs to be captured in the ground environment.
      groundPtrTag :: MT.UndefPtrOpTags
    , groundVal :: W4G.GroundValue tp
    } -> GroundInfo tp

-- | A binding environment representing the ground values for the inner expressions
-- of some datatype.
data GroundData sym where
  GroundData :: PS.ValidSym sym =>
    { grndSym :: sym
    -- | This map is intended to be total with respect to every inner expression present
    -- in the outer 'Grounded'
    , grndInfoMap :: MapF.MapF (W4.SymExpr sym) GroundInfo
    , grndStackRegion :: Natural
    } -> GroundData sym

type HasGroundData sym = (?grndData :: GroundData sym)

-- | We weaken the external constraint to only establish 'W4.IsExpr' in order
-- to prevent functions executed in 'traverseWithGroundSym' from creating
-- fresh terms (which would not have ground values in the environment)
type IsGroundSym sym = (HasGroundData sym, W4.IsExpr (W4.SymExpr sym))

withGroundData :: 
  IsGroundSym grnd =>
  (PS.ValidSym grnd => GroundData grnd -> a) ->
  a
withGroundData f = let grnd = ?grndData in case grnd of GroundData{} -> f grnd

-- | Retrieve the ground information of a symbolic expression with respect to the
-- grounding environment bound by 'IsGroundSym'
groundInfo :: forall sym tp. IsGroundSym sym => W4.SymExpr sym tp -> GroundInfo tp
groundInfo e = withGroundData $ \grnd -> case SU.exprToGroundVal @sym (W4.exprType e) e of
  Just gv ->  GroundInfo mempty gv
  Nothing -> case MapF.lookup e (grndInfoMap grnd) of
    Just info -> info
    Nothing -> PP.panic PP.ProofConstruction "groundInfo" ["Unexpected symbolic value:", show $ W4.printSymExpr e]

-- | Retrieve the ground information of a symbolic natural with respect to the
-- grounding environment bound by 'IsGroundSym'
groundInfoNat :: IsGroundSym sym => W4.SymNat sym -> (MT.UndefPtrOpTags, Natural)
groundInfoNat e = withGroundData $ \_grnd ->
  let info = groundInfo $ W4.natToIntegerPure e
  in (groundPtrTag info, integerToNat (groundVal info))

-- TODO: this breaks the abstraction boundary for block ends
-- (see: https://github.com/GaloisInc/pate/issues/196)

-- | Retrieve the concrete 'MS.MacawBlockEndCase' of
-- a symbolic 'MS.MacawBlockEndType' with respect to the
-- grounding environment bound by 'IsGroundSym'
groundMacawEndCase ::
  forall sym arch.
  IsGroundSym sym =>
  Proxy arch ->
  CS.RegValue sym (MCS.MacawBlockEndType arch) ->
  MCS.MacawBlockEndCase
groundMacawEndCase _ (_ Ctx.:> CS.RV blend Ctx.:> _) =
  toEnum $ fromIntegral $ BV.asUnsigned $ groundValue blend

-- | Retrieve the concrete value of a symbolic expression with respect to the
-- grounding environment bound by 'IsGroundSym'
groundValue :: IsGroundSym sym => W4.SymExpr sym tp -> W4G.GroundValue tp
groundValue e = groundVal $ groundInfo e 

-- | Ground the predicate in a 'W4P.PartExpr' with respect to the grounding environment
-- bound by 'IsGroundSym' and return the inner value if it evaluates to True.
groundPartial :: IsGroundSym sym => W4P.PartExpr (W4.Pred sym) a -> Maybe a
groundPartial = \case
  W4P.Unassigned -> Nothing
  W4P.PE p v -> case groundValue p of
    True -> Just v
    False -> Nothing

-- | Retrieve the concrete value of a symbolic natural with respect to the
-- grounding environment bound by 'IsGroundSym'
groundNat :: IsGroundSym sym => W4.SymNat sym -> Natural
groundNat e = snd $ groundInfoNat e

-- | True if the concrete value of the given symbolic natural is equivalent
-- to the "stack" memory region.
isStackRegion :: IsGroundSym sym => W4.SymNat sym -> Bool
isStackRegion e = grndStackRegion ?grndData == groundNat e

-- | Clamp an integer to be a positive natural (reflecting the semantics of
-- 'W4.integerToNat' for a concrete value).
integerToNat :: Integer -> Natural
integerToNat i
  | i >= 0 = fromIntegral i
  | otherwise = 0

-- | Compute a grounding environment for a 'PEM.ExprMappable' value by evaluating
-- each inner expression according to the given function. The value is unmodified
-- in the resulting 'Grounded', but is paired with a grounding environment that is
-- now necessarily sufficient to ground any of its inner expressions.
ground ::
  forall sym a.
  PS.ValidSym sym =>
  PEM.ExprFoldableIO sym (a sym) =>
  sym ->
  -- | stack region
  W4.SymNat sym ->
  -- | Grounding inner expressions
  (forall tp. W4.SymExpr sym tp -> IO (GroundInfo tp)) ->
  a sym ->
  IO (Grounded a)
ground sym stackRegion mkinfo a = do
  stackRegionC <- (integerToNat . groundVal) <$> (W4.natToInteger sym stackRegion >>= mkinfo)
  let
    initGround = GroundData
      { grndSym = sym
      , grndInfoMap = MapF.empty
      , grndStackRegion = stackRegionC
      }
  let
    f' :: forall tp. W4.SymExpr sym tp -> GroundData sym -> IO (GroundData sym)
    f' e gdata = case SU.exprToGroundVal @sym (W4.exprType e) e of
      Just _ -> return gdata
      Nothing -> do
        upd <- MapF.updatedValue <$> MapF.updateAtKey e (Just <$> mkinfo e) (\_ -> return $ MapF.Keep) (grndInfoMap gdata)
        return $ gdata { grndInfoMap = upd }
  gdata <- PEM.foldExprIO sym f' a initGround
  return $ Grounded a gdata

-- trivial instance - grounded values should not be modified
-- by expression maps
instance PEM.ExprMappable sym (Grounded a) where
  mapExpr _sym _f = return
