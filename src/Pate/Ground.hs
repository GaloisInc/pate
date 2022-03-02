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
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Numeric.Natural ( Natural )
import qualified Data.Kind as DK
import qualified Control.Monad.IO.Class as IO
import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.Context (EmptyCtx, (::>), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.Symbolic as MS

import qualified Lang.Crucible.Simulator as CS

import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Solver as PS

import qualified What4.Concrete as W4C
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Partial as W4P
import qualified What4.ExprHelpers as WEH

import qualified Pate.Panic as PP

-- | This module provides the 'Grounded' datatype as a simple wrapper which
-- existentially quantifies the 'sym' parameter for another type. This inner type
-- may contain symbolic what4 expressions internally, but with the intention that
-- they are all fully concrete values (i.e. asConcrete should be a total function for
-- any inner expression)

-- | A wrapper indicating that the inner expressions of
-- a datatype are fully concrete values
data Grounded (a :: sym -> DK.Type) where
  Grounded ::
    { _grndVal :: a sym
    , _grndData :: GroundData sym
    } -> Grounded a

withGroundSym ::
  Grounded tp ->
  (forall grnd. IsGroundSym grnd => tp grnd -> a) ->
  a
withGroundSym (Grounded v d@(GroundData{})) f = let ?grndData = d in f v

-- Functions that can be defined for an arbitrary 'sym' are safe transformations
-- for a grounded value, since they can't modify the inner expressions

instance TF.FunctorF Grounded where
  fmapF f (Grounded v d) = Grounded (f v) d

instance TF.FoldableF Grounded where
  foldMapF f (Grounded v _) = f v

instance TF.TraversableF Grounded where
  traverseF f (Grounded v d) = Grounded <$> f v <*> pure d

-- | Ground values may be 'tagged' with additional metadata that may be lost
-- when grounding. Currently this tracks when a value may have been derived from
-- "undefined" pointer operations, which is lost during grounding, as those undefined
-- operations are represented as uninterpreted functions (which are necessarily concretely
-- defined when grounding).
data GroundInfo (tp :: W4.BaseType) where
  GroundInfo ::
    { groundPtrTag :: MT.UndefPtrOpTags
    , groundVal :: W4G.GroundValue tp
    } -> GroundInfo tp


data GroundData sym where
  GroundData :: PS.ValidSym sym =>
    { grndSym :: sym
    , grndInfoMap :: MapF.MapF (W4.SymExpr sym) GroundInfo
    , grndStackRegion :: Natural
    } -> GroundData sym

type HasGroundData sym = (?grndData :: GroundData sym)

type IsGroundSym sym = (HasGroundData sym, PS.ValidSym sym)

groundInfo :: IsGroundSym sym => W4.SymExpr sym tp -> GroundInfo tp
groundInfo e = 
  let grnd = ?grndData
  in case MapF.lookup e (grndInfoMap grnd) of
    Just info -> info
    Nothing -> PP.panic PP.ProofConstruction "groundInfo" ["Unexpected symbolic value:", show $ W4.printSymExpr e]

groundInfoNat :: IsGroundSym sym => W4.SymNat sym -> GroundInfo W4.BaseIntegerType
groundInfoNat e =
  let grnd = ?grndData
  in groundInfo $ WEH.natToIntegerPure (grndSym grnd) e

-- TODO: this breaks the abstraction boundary for block ends
groundMacawEndCase ::
  forall sym arch.
  IsGroundSym sym =>
  Proxy arch ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  MS.MacawBlockEndCase
groundMacawEndCase _ (_ Ctx.:> CS.RV blend Ctx.:> _) =
  (toEnum (fromIntegral (BV.asUnsigned (groundValue blend))))

groundValue :: IsGroundSym sym => W4.SymExpr sym tp -> W4G.GroundValue tp
groundValue e = groundVal $ groundInfo e 

groundPartial :: IsGroundSym sym => W4P.PartExpr (W4.Pred sym) a -> Maybe a
groundPartial = \case
  W4P.Unassigned -> Nothing
  W4P.PE p v -> case groundValue p of
    True -> Just v
    False -> Nothing

groundNat :: IsGroundSym sym => W4.SymNat sym -> Natural
groundNat e = case W4.asNat e of
  Just n -> n
  Nothing -> PP.panic PP.ProofConstruction "groundNat" ["Unexpected symbolic value:", show $ W4.printSymNat e]

isStackRegion :: IsGroundSym sym => W4.SymNat sym -> Bool
isStackRegion e = grndStackRegion ?grndData == groundNat e

ground ::
  forall sym a.
  PS.ValidSym sym =>
  PEM.ExprMappable sym (a sym) =>
  sym ->
  -- | stack region
  W4.SymNat sym ->
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
    f' e gdata = do
      upd <- MapF.updatedValue <$> MapF.updateAtKey e (Just <$> mkinfo e) (\_ -> return $ MapF.Keep) (grndInfoMap gdata)
      return $ gdata { grndInfoMap = upd }
  gdata <- PEM.foldExpr sym f' a initGround
  return $ Grounded a gdata
  where
    integerToNat :: Integer -> Natural
    integerToNat i
      | i >= 0 = fromIntegral i
      | otherwise = 0
-- trivial instance - grounded values should not be modified
-- by expression maps
instance PEM.ExprMappable sym (Grounded a) where
  mapExpr _sym _f = return


-- concrete representations f
