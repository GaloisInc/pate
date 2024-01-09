{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}

module What4.JSON 
  ( W4S
  , W4Serializable(..)
  , W4SerializableF(..)
  , W4SerializableFC
  , SerializableExprs
  , w4ToJSON
  , object
  , w4SerializeString
  , (.=)
  , (.==)
  , (.=~)
  ) where

import           Control.Monad.State (MonadState (..), State, modify, evalState, runState)

import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import           Data.Text (Text)
import           Data.Data (Proxy(..), Typeable)
import qualified Data.Aeson as JSON

import           Data.Parameterized.Some (Some(..))

import qualified What4.Interface as W4

import qualified What4.Serialize.Printer as W4S
import qualified What4.Serialize.Parser as W4D
import qualified What4.Expr.Builder as W4B
import qualified Data.Map as Map
import Control.Monad (forM)
import qualified What4.PredMap as W4P
import Data.Parameterized.HasRepr
import qualified What4.Concrete as W4
import qualified Data.Text as T
import GHC.IO (catch, evaluate, unsafePerformIO)
import GHC.IO.Exception (IOException)
import Control.DeepSeq (force)
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Kind
import qualified Lang.Crucible.Utils.MuxTree as MT
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.SetF as SetF
import Data.Functor.Const


newtype ExprCache sym = ExprCache (Map (Some (W4.SymExpr sym)) JSON.Value)

newtype W4S sym a = W4S (State (ExprCache sym) a)
  deriving (Monad, Applicative, Functor, MonadState (ExprCache sym))

class W4Serializable sym a where
  w4Serialize :: a -> W4S sym JSON.Value

w4SerializeString :: Show a => a -> W4S sym JSON.Value
w4SerializeString s = return $ JSON.String (T.pack (show s))

w4ToJSON :: forall sym a. SerializableExprs sym => W4Serializable sym a => a -> JSON.Value
w4ToJSON a = let W4S f = w4Serialize @sym a in evalState f (ExprCache Map.empty)

class W4SerializableF sym (f :: k -> Type) where
  withSerializable :: Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a

  default withSerializable :: W4Serializable sym (f tp) => Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a
  withSerializable _ _ _ x = x

  w4SerializeF :: forall tp. f tp -> W4S sym JSON.Value
  w4SerializeF x = withSerializable (Proxy :: Proxy sym) (Proxy :: Proxy f) (Proxy :: Proxy tp) (w4Serialize x)

class (forall sym. W4SerializableF sym f) => W4SerializableFC f where

-- | Wrap a serialization step in an error handler that tries to fully evaluate the
--   JSON value.
--   This is needed because the What4 serializer does not return partial results, and simply
--   throws runtime errors for unsupported expressions (e.g. annotated expressions, quantified expressions).
--   We shouldn't be sending these to be serialized regardless, but this allows the serializer to
--   fail gracefully if it does happen.
trySerialize :: W4S sym JSON.Value -> W4S sym (Either String JSON.Value)
trySerialize (W4S f) = do
  st <- get
  r <- return $! unsafePerformIO ((Right <$> (evaluate (runState f st) >>= \(x,st') -> return (force x, st'))) `catch` (\(er :: IOException) -> return $ Left (show er)))
  case r of
    Left err -> return $ Left err
    Right (x,st') -> do
      put st'
      return $ Right x

instance sym ~ W4B.ExprBuilder t fs scope => W4Serializable sym (W4B.Expr t tp) where
  w4Serialize e = do
    ExprCache s <- get
    case Map.lookup (Some e) s of
      Just v -> return $ v
      Nothing -> do
        v <- case W4.asConcrete e of
          Just (W4.ConcreteInteger i) -> return $ JSON.toJSON i
          Just (W4.ConcreteBool b) -> return $ JSON.toJSON b
          Just{} -> return $ JSON.String (T.pack (show (W4.printSymExpr e)))
          _ -> do
            mv <- trySerialize $ do
              let result = W4S.serializeExprWithConfig (W4S.Config True True) e
              let var_env = map (\(Some bv, t) -> (show (W4B.bvarName bv), t)) $ OMap.toAscList $ W4S.resFreeVarEnv result
              let fn_env = map (\(W4S.SomeExprSymFn fn, t) -> (show (W4B.symFnName fn), t)) $ OMap.toAscList $ W4S.resSymFnEnv result
              let sexpr = W4S.resSExpr result
              return $ JSON.object [ "symbolic" JSON..= JSON.String (W4D.printSExpr mempty sexpr), "vars" JSON..= var_env, "fns" JSON..= fn_env ]
            case mv of
              Left er -> return $ JSON.object [ "symbolic_serialize_err" JSON..= er]
              Right v -> return v
        modify $ \(ExprCache s') -> ExprCache (Map.insert (Some e) v s')
        return v

deriving instance Typeable (W4B.ExprBuilder t fs scope)

instance sym ~ W4B.ExprBuilder t fs scope => W4SerializableF sym (W4B.Expr t) where

instance W4SerializableF sym x => W4Serializable sym (Some x) where
  w4Serialize (Some x) = w4SerializeF x

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (x, y) where
  w4Serialize (x,y) = object [ "fst" .= x, "snd" .= y]

instance (W4Serializable sym x) => W4Serializable sym [x] where
  w4Serialize xs = do
    xs_json <- mapM w4Serialize xs
    return $ JSON.toJSON xs_json

instance W4Serializable sym JSON.Value where
  w4Serialize = return

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (Map x y) where
  w4Serialize x = do
    objs <- forM (Map.toList x) $ \(k, v) -> object [ "key" .= k, "val" .= v]
    object [ "map" .= objs ]

type SerializableExprs sym = W4SerializableF sym (W4.SymExpr sym)

instance (SerializableExprs sym, W4Serializable sym x) => W4Serializable sym (W4P.PredMap sym x k) where
  w4Serialize x = do
    objs <- forM (W4P.toList x) $ \(k,p) -> object [ "val" .= k, "pred" .== p]
    let (repr :: Text) = case typeRepr x of
          W4P.PredConjRepr -> "conj"
          W4P.PredDisjRepr -> "disj"
    object [ "predmap" .= objs, "kind" .= repr ]

instance W4Serializable sym Integer where
  w4Serialize i = return $ JSON.toJSON i

instance W4Serializable sym Text where
  w4Serialize i = return $ JSON.toJSON i

instance W4Serializable sym a => W4Serializable sym (Maybe a) where
  w4Serialize = \case
    Just a -> w4Serialize a
    Nothing -> return $ JSON.Null

instance W4Serializable sym (W4.NatRepr n) where
  w4Serialize nr = w4Serialize $ W4.intValue nr

instance (W4SerializableF sym x, W4SerializableF sym y) => W4Serializable sym (MapF x y) where
  w4Serialize x = do
    objs <- forM (MapF.toList x) $ \(MapF.Pair k v) -> object [ "key" .== k, "val" .== v]
    object [ "map" .= objs ]

instance (W4Serializable sym tp, SerializableExprs sym) => W4Serializable sym (MT.MuxTree sym tp) where
  w4Serialize mt = case MT.viewMuxTree mt of
    [] -> error "Serialize: Invalid Muxtree"
    [(e,_)] -> w4Serialize e
    es -> do
      body <- forM es $ \(e,p) ->
        object [ "val" .= e, "pred" .== p]
      object ["muxtree" .= body]

instance W4SerializableF sym f => W4Serializable sym (Ctx.Assignment f ctx) where
  w4Serialize x = w4Serialize $ TFC.toListFC Some x

data W4KeyValue sym = forall a. W4Serializable sym a => W4KeyValue JSON.Key a

(.=) :: W4Serializable sym v => JSON.Key -> v -> W4KeyValue sym
(.=) = W4KeyValue

(.==) :: forall sym v tp. W4SerializableF sym v => JSON.Key -> v tp -> W4KeyValue sym
(.==) = \k v -> withSerializable (Proxy @sym) (Proxy @v) (Proxy @tp) $ W4KeyValue k v

(.=~) :: Show v => JSON.Key -> v -> W4KeyValue sym
(.=~) = \k v -> W4KeyValue k (T.pack (show v))

object :: [W4KeyValue sym] -> W4S sym JSON.Value
object kvs = fmap JSON.object $ forM kvs $ \(W4KeyValue k v) -> do
    v_json <- w4Serialize v
    return $ k JSON..= v_json

instance forall sym e tp. (W4Serializable sym (e tp)) => W4Serializable sym (SetF.SetF e tp) where
  w4Serialize mt = w4Serialize (SetF.toList mt)

instance forall sym e. (W4SerializableF sym e) => W4SerializableF sym (SetF.SetF e) where
  withSerializable sym _a (b :: q tp)  f = withSerializable sym (Proxy @e) b $ f

instance forall sym f tp. (W4Serializable sym f) => W4Serializable sym (Const f tp) where
  w4Serialize (Const f) = w4Serialize f

instance forall sym f. (W4Serializable sym f) => W4SerializableF sym (Const f)