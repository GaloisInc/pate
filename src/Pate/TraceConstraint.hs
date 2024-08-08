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
    TraceConstraint(..)
  , readDeserializable
  , constraintToPred
  , TraceConstraintMap(..)
  , readConstraintMap
  ) where

import           Prelude hiding (EQ)

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad ( forM )
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
      _ -> fail "Unsupported expression type"

{-
instance forall sym arch. IsTraceNode '(sym :: DK.Type,arch) "trace_constraint" where
  type TraceNodeType '(sym,arch) "trace_constraint" = TraceConstraint sym
  prettyNode _ _ = PP.pretty ("TODO" :: String)
  nodeTags = mkTags @'(sym,arch) @"trace_constraint" [Summary, Simplified]
-}

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
    case op of
      LTs -> go W4.bvSlt
      LTu -> go W4.bvUlt
      LEs -> go W4.bvSle
      LEu -> go W4.bvUle
      EQ -> go W4.isEq
      _ -> fail "err"

  _ -> fail "Unexpected constraint "



newtype TraceConstraintMap sym arch = 
  TraceConstraintMap (Map (GraphNode arch) (TraceConstraint sym))


instance forall sym arch. IsTraceNode '(sym :: DK.Type,arch :: DK.Type) "trace_constraint_map" where
  type TraceNodeType '(sym,arch) "trace_constraint_map" = TraceConstraintMap sym arch
  prettyNode _ _ = PP.pretty ("TODO" :: String)
  nodeTags = mkTags @'(sym,arch) @"trace_constraint_map" [Summary, Simplified]

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
          nodes <- runJSON $ do
            JSON.Object o <- return v
            (nodes :: [JSON.Value]) <- o JSON..: "trace_constraints"
            return nodes
          let nds = zip ndEnvs nodes
          fmap (TraceConstraintMap . Map.fromList) $ forM nds $ \((nd, env), constraint_json) -> do
             (lift $ W4S.jsonToW4 sym env constraint_json) >>= \case
               Left err -> throwError $ InputChoiceError "Failed to parse value" [err]
               Right a -> return (nd, a)
  chooseInput_ @"trace_constraint_map" msg parse >>= \case
    Nothing -> IO.liftIO $ fail "Unexpected trace map read"
    Just a -> return a


runJSON :: JSON.Parser a -> ExceptT InputChoiceError IO a
runJSON p = ExceptT $ case JSON.parse (\() -> p) () of
  JSON.Success a -> return $ Right a
  JSON.Error err -> return $ Left $ InputChoiceError "Failed to parse value" [err]



-- FIXME: Move
readDeserializable ::
  forall nm_choice sym k e m.
  W4S.W4Deserializable sym (TraceNodeLabel nm_choice, TraceNodeType k nm_choice) =>
  W4.IsExprBuilder sym =>
  IsTreeBuilder k e m =>
  IsTraceNode k nm_choice =>
  IO.MonadUnliftIO m =>
  sym ->
  W4S.ExprEnv sym ->
  String ->
  m (Maybe (TraceNodeLabel nm_choice, TraceNodeType k nm_choice))
readDeserializable sym env msg = do
  let parse s = case JSON.eitherDecode (fromString s) of
        Left err -> return $ Left $ InputChoiceError "Failed to decode JSON" [err]
        Right (v :: JSON.Value) -> W4S.jsonToW4 sym env v >>= \case
          Left err -> return $ Left $ InputChoiceError "Failed to parse value" [err]
          Right a -> return $ Right a
  chooseInput @nm_choice msg parse
