{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Pate.TraceConstraint
  (
    TraceConstraint
  , constraintToPred
  , constraintListToPred
  , TraceConstraintMap(..)
  , readConstraintMap
  ) where

import           Prelude hiding (EQ)

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad ( forM, foldM )
import           Control.Monad.Except
import           Control.Monad.Trans
import qualified Data.Aeson as JSON
import qualified Data.Aeson.Types as JSON

import qualified Data.Text.Lazy.Encoding as Text
import qualified Data.Text.Encoding.Error as Text
import qualified Data.Kind as DK
import           Data.String
import           Data.Map ( Map )
import qualified Data.Map as Map

import qualified Prettyprinter as PP

import qualified What4.Interface as W4
import qualified What4.Concrete as W4

import qualified Pate.Arch as PA
import qualified Pate.PatchPair as PPa
import           Pate.Verification.PairGraph.Node
import           Pate.TraceTree
import qualified What4.JSON as W4S
import           What4.JSON ( (.:) )
import           Data.Parameterized.Some (Some(..))
import qualified Data.BitVector.Sized as BVS
import qualified Numeric as Num

newtype TraceIdentifier = TraceIdentifier String
  deriving (Eq, Ord, IsString)

data ConstraintOp = LTs | LTu | GTs | GTu | LEs | LEu | GEs | GEu | NEQ | EQ
  deriving (Show, Read)

data TraceConstraint sym = forall tp. TraceConstraint 
  { tcVar :: W4.SymExpr sym tp
  , tcOp :: ConstraintOp
  , tcConst :: W4.ConcreteVal tp 
  }

instance forall sym. W4S.W4Deserializable sym (TraceConstraint sym) where
  w4Deserialize_ v | W4S.SymDeserializable{} <- W4S.symDeserializable @sym  = do
    JSON.Object o <- return v
    (Some (var :: W4.SymExpr sym tp)) <- o .: "var"
    (opJSON :: JSON.Value) <- o .: "op"
    (op :: ConstraintOp) <- W4S.readJSON opJSON
    case W4.exprType var of
      W4.BaseBVRepr w -> do
        (cS :: String) <- o .: "const"
        ((c :: Integer),""):_ <- return $ Num.readDec cS
        case (BVS.mkBVUnsigned w c) of
          Just bv -> return $ TraceConstraint var op (W4.ConcreteBV w bv)
          Nothing -> fail "Unexpected integer size"
      _ -> fail ("Unsupported expression type:" ++ show (W4.exprType var))

constraintToPred ::
  forall sym.
  W4.IsExprBuilder sym =>
  sym ->
  TraceConstraint sym -> 
  IO (W4.Pred sym)
constraintToPred sym (TraceConstraint var op c) = case W4.exprType var of
  W4.BaseBVRepr w -> do
    let W4.ConcreteBV _ bv = c
    bvSym <- W4.bvLit sym w bv
    let go :: (forall w. 1 W4.<= w => sym -> W4.SymBV sym w -> W4.SymBV sym w -> IO (W4.Pred sym)) -> IO (W4.Pred sym)
        go f = f sym var bvSym
    let goNot :: (forall w. 1 W4.<= w => sym -> W4.SymBV sym w -> W4.SymBV sym w -> IO (W4.Pred sym)) -> IO (W4.Pred sym)
        goNot f = f sym var bvSym >>= W4.notPred sym
    case op of
      LTs -> go W4.bvSlt
      LTu -> go W4.bvUlt
      LEs -> go W4.bvSle
      LEu -> go W4.bvUle
      EQ -> go W4.isEq
      GTs -> goNot W4.bvSle
      GTu -> goNot W4.bvUle
      GEs -> goNot W4.bvSlt
      GEu -> goNot W4.bvUlt
      NEQ -> goNot W4.isEq
  W4.BaseIntegerRepr -> do
    let W4.ConcreteInteger i = c
    intSym <- W4.intLit sym i
    let go :: (sym -> W4.SymExpr sym W4.BaseIntegerType -> W4.SymExpr sym W4.BaseIntegerType -> IO (W4.Pred sym)) -> IO (W4.Pred sym)
        go f = f sym var intSym
    let goNot :: (sym -> W4.SymExpr sym W4.BaseIntegerType -> W4.SymExpr sym W4.BaseIntegerType -> IO (W4.Pred sym)) -> IO (W4.Pred sym)
        goNot f = f sym var intSym >>= W4.notPred sym
    case op of
      LTs -> go W4.intLt
      LTu -> fail "LTu: unsigned int comparison not supported"
      LEs -> go W4.intLe
      LEu -> fail "LEu: unsigned int comparison not supported"
      EQ -> go W4.isEq
      GTs -> goNot W4.intLe
      GTu -> fail "GTu: unsigned int comparison not supported"
      GEs -> goNot W4.intLt
      GEu -> fail "GEu: unsigned int comparison not supported"
      NEQ -> goNot W4.isEq
  _ -> fail "Unexpected constraint "

constraintListToPred ::
  forall sym.
  W4.IsExprBuilder sym =>
  sym ->
  [TraceConstraint sym] -> 
  IO (W4.Pred sym)
constraintListToPred sym trs = foldM (\p tc -> constraintToPred sym tc >>= W4.andPred sym p) (W4.truePred sym) trs

newtype TraceConstraintMap sym arch = 
  TraceConstraintMap (Map (GraphNode arch) [TraceConstraint sym])


instance forall sym arch. IsTraceNode '(sym :: DK.Type,arch :: DK.Type) "trace_constraint_map" where
  type TraceNodeType '(sym,arch) "trace_constraint_map" = TraceConstraintMap sym arch
  prettyNode _ _ = PP.pretty ("TODO" :: String)
  nodeTags = []

readConstraintMap ::
  W4.IsExprBuilder sym =>
  IsTreeBuilder '(sym,arch) e m =>
  IO.MonadUnliftIO m =>
  PA.ValidArch arch =>
  sym ->
  String {- ^ input prompt -} ->
  [(GraphNode arch,W4S.ExprEnv sym)] ->
  m (TraceConstraintMap sym arch)
readConstraintMap sym msg ndEnvs = do
  let parse s = case JSON.eitherDecode (fromString s) of
        Left err -> return $ Left $ InputChoiceError "Failed to decode JSON" [err]
        Right (v :: JSON.Value) -> runExceptT $ do
          (nodes :: [[JSON.Value]]) <- runJSON $ JSON.parseJSON v
          let nds = zip ndEnvs nodes
          constraints <- forM nds $ \((nd, env), constraints_json) -> forM constraints_json $ \constraint_json ->
                (lift $ W4S.jsonToW4 sym env constraint_json) >>= \case
                  Left err -> throwError $ InputChoiceError "Failed to parse value" [err]
                  Right a -> return (nd, a)
          return $ TraceConstraintMap $ foldl (\m (k,a) -> Map.insertWith (++) k [a] m) Map.empty (concat constraints)
  chooseInput_ @"trace_constraint_map" msg parse >>= \case
    Nothing -> IO.liftIO $ fail "Unexpected trace map read"
    Just a -> return a


runJSON :: JSON.Parser a -> ExceptT InputChoiceError IO a
runJSON p = ExceptT $ case JSON.parse (\() -> p) () of
  JSON.Success a -> return $ Right a
  JSON.Error err -> return $ Left $ InputChoiceError "Failed to parse value" [err]