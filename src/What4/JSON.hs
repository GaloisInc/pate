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
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module What4.JSON 
  ( W4S
  , W4Serializable(..)
  , W4SerializableF(..)
  , W4SerializableFC
  , SerializableExprs
  , w4ToJSON
  , w4ToJSONWithEnv
  , W4D
  , w4DeserializeWithEnv
  , W4Deserializable(..)
  ) where

import           Control.Monad.Except (MonadError (..), liftEither)
import           Control.Monad.Reader (ReaderT (..), MonadReader (..), asks)
import           Control.Monad.State (StateT (..), MonadState (..), State, evalState, runState)

import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import           Data.Data (Proxy(..))
import qualified Data.Aeson.KeyMap as JSON
import qualified Data.Aeson as JSON
import           Data.Aeson ( (.=) )

import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.Context as Ctx

import qualified What4.Interface as W4

import           What4.Serialize.Parser (SomeSymFn(..))
import qualified What4.Serialize.Printer as W4S
import qualified What4.Serialize.Parser as W4D
import qualified What4.Expr.Builder as W4B
import qualified Data.Map as Map
import Control.Monad (forM)
import qualified What4.PredMap as W4P
import Data.Parameterized.HasRepr
import qualified What4.Concrete as W4
import qualified Data.Text as T
import qualified Data.BitVector.Sized as BVS
import Control.Monad.Trans.Except

import Data.Parameterized.SetCtx (SetCtx)
import qualified Data.Parameterized.SetCtx as SetCtx
import Control.Monad.IO.Class
import Control.Monad.Trans (lift)
import Control.Applicative ((<|>), Alternative(..))

-- FIXME: should be in What4?
instance HasRepr (W4B.Expr t) W4.BaseTypeRepr where
  typeRepr = W4.exprType

data ExprCache sym = 
    forall ctx. ExprCacheIdx (SetCtx (W4.SymExpr sym) ctx)
  | ExprCacheMap (Map (Some (W4.SymExpr sym)) JSON.Value)

newtype W4S sym a = W4S (State (ExprCache sym) a)
  deriving (Monad, Applicative, Functor)

class W4Serializable sym a where
  w4Serialize :: a -> W4S sym JSON.Value

w4ToJSON :: forall sym a. W4Serializable sym a => a -> JSON.Value
w4ToJSON a = let W4S f = w4Serialize @sym a in evalState f (ExprCacheMap Map.empty)

-- | Serialize an 'ExprMappable' value by flattening into a struct, which is serialized
--   all at once, in order to get a single binding environment for all sub expressions.
--   The given value is then serialized according to 'W4Serializable', where symbolic'
--   
w4ToJSONWithEnv :: forall sym t st fs a. 
  ( sym ~ W4B.ExprBuilder t st fs
  , W4Serializable sym a
  , W4.IsSymExprBuilder sym
  ) => 
  sym ->
  (forall tp. W4.BoundVar sym tp -> JSON.Value) ->
  (forall args ret. W4.SymFn sym args ret -> JSON.Value) ->
  a -> 
  IO JSON.Value
w4ToJSONWithEnv sym ser_var ser_fn a = do
  let (json, cache) = let W4S f = w4Serialize @sym a in runState f (ExprCacheIdx SetCtx.empty)
  ExprCacheIdx sub_exprs_set <- return cache
  let sub_exprs = SetCtx.toAssignment sub_exprs_set
  sub_exprs_struct <- W4.mkStruct sym sub_exprs
  let r = W4S.serializeExprWithConfig (W4S.Config True True) sub_exprs_struct

  let ser_var_env = JSON.toJSON $ map (\(Some bv, nm) -> (ser_var bv, nm)) (OMap.toAscList (W4S.resFreeVarEnv r))
  let ser_fn_env = JSON.toJSON $ map (\(W4S.SomeExprSymFn fn, nm) -> (ser_fn fn, nm)) (OMap.toAscList (W4S.resSymFnEnv r))
  let index_json = JSON.String $ W4D.printSExpr mempty (W4S.resSExpr r)

  return $ JSON.object [ "index" .= index_json, "body" .= json, "var_env" .= ser_var_env, "fn_env" .= ser_fn_env ]

class W4SerializableF sym f where
  withSerializable :: Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a

  default withSerializable :: W4Serializable sym (f tp) => Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a
  withSerializable _ _ _ x = x

  w4SerializeF :: forall tp. f tp -> W4S sym JSON.Value
  w4SerializeF x = withSerializable (Proxy :: Proxy sym) (Proxy :: Proxy f) (Proxy :: Proxy tp) (w4Serialize x)

class (forall sym. W4SerializableF sym f) => W4SerializableFC f where

bvToJSON :: W4.NatRepr w -> BVS.BV w -> JSON.Value
bvToJSON w bv = JSON.object [ "sz" .= W4.intValue w, "bv" .= BVS.asUnsigned bv]

instance sym ~ W4B.ExprBuilder t fs scope => W4Serializable sym (W4B.Expr t tp) where
  w4Serialize e = case W4.asConcrete e of
    Just (W4.ConcreteInteger i) -> return $ JSON.toJSON i
    Just (W4.ConcreteBool b) -> return $ JSON.toJSON b
    Just (W4.ConcreteBV w bv) -> return $ bvToJSON w bv
    _ -> (W4S get) >>= \case
      ExprCacheIdx idx_asn -> do
        idx_int <- case SetCtx.insertMaybe e idx_asn of
          Left idx -> return $ Ctx.indexVal idx
          Right idx_asn' -> do
            W4S $ put (ExprCacheIdx idx_asn')
            return $ Ctx.indexVal (SetCtx.lastIndex idx_asn')
        return $ JSON.object [ "ref" .= idx_int ]
      ExprCacheMap m -> case Map.lookup (Some e) m of
        Just v -> return v
        Nothing -> do
          let sexpr = W4S.resSExpr $ W4S.serializeExprWithConfig (W4S.Config True True) e
          let v = JSON.object [ "symbolic" .= JSON.String (W4D.printSExpr mempty sexpr) ]
          W4S $ put (ExprCacheMap (Map.insert (Some e) v m))
          return v

instance sym ~ W4B.ExprBuilder t fs scope => W4SerializableF sym (W4B.Expr t) where

instance W4SerializableF sym x => W4Serializable sym (Some x) where
  w4Serialize (Some x) = w4SerializeF x

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (x, y) where
  w4Serialize (x,y) = do
    x_v <- w4Serialize x
    y_v <- w4Serialize y
    return $ JSON.object [ "fst" .= x_v, "snd" .= y_v]

instance W4Serializable sym Integer where
  w4Serialize i = return $ JSON.toJSON i

instance W4Serializable sym String where
  w4Serialize i = return $ JSON.toJSON i

data JSONCache sym = 
    JSONCacheFn (JSON.Value -> (Either DeserializeError (Some (W4.SymExpr sym))))
  | JSONCacheMap (Map JSON.Value (Some (W4.SymExpr sym)))

data DeserializeError = DeserializeError String

data JSONEnv sym =
  JSONEnv { envSym :: sym, envCfg :: W4D.Config sym }

newtype W4D sym a = W4D (ExceptT DeserializeError (ReaderT (JSONEnv sym) (StateT (JSONCache sym) IO)) a)
  deriving 
    (Monad, Applicative, Functor, MonadIO, MonadState (JSONCache sym), MonadError DeserializeError)

instance Alternative (W4D sym) where
  empty = throwError $ DeserializeError "no alternatives"
  a <|> b = do
    env <- (W4D ask)
    st <- (W4D get)
    a_result <- liftIO $ runExceptT $ runW4D env st a
    case a_result of
      -- just report the last error
      Left{} -> b
      Right a_r -> return a_r

w4DSym :: W4D sym sym
w4DSym = envSym <$> W4D (lift ask)

runW4D :: (MonadError DeserializeError m, MonadIO m) => JSONEnv sym -> JSONCache sym -> W4D sym a -> m a
runW4D env cache (W4D f) = (liftIO $ runStateT (runReaderT (runExceptT f) env) cache) >>= \case
  (Left err,_) -> throwError err
  (Right a, _s) -> return a

instance MonadFail (W4D sym) where
  fail msg = throwError (DeserializeError msg)

class W4Deserializable sym a where
  w4Deserialize :: JSON.Value -> W4D sym a

lookupJSON :: MonadError DeserializeError m => JSON.Key -> JSON.Object -> m JSON.Value
lookupJSON k o = case JSON.lookup k o of
  Just v -> return v
  Nothing -> throwError (DeserializeError $ "missing key:" ++ show k)

asObject :: MonadError DeserializeError m => JSON.Value -> m (JSON.Object)
asObject (JSON.Object o) = return o
asObject _ = throwError (DeserializeError $ "asObject: not object")

fromJSON :: (MonadError DeserializeError m, JSON.FromJSON a) => JSON.Value -> m a
fromJSON v = case JSON.fromJSON v of
  JSON.Error msg -> throwError (DeserializeError ("fromJSON: " ++ msg))
  JSON.Success a -> return a

getField :: (MonadError DeserializeError m, JSON.FromJSON a) => JSON.Key -> JSON.Value -> m a
getField k v = do
  v_obj <- asObject v
  v_k <- lookupJSON k v_obj
  fromJSON v_k

liftMsg :: (Show err, MonadError DeserializeError m) => Either err a -> m a 
liftMsg (Left err) = throwError (DeserializeError (show err))
liftMsg (Right a) = return a

w4DeserializeWithEnv :: forall sym t st fs a. 
  ( sym ~ W4B.ExprBuilder t st fs
  , W4Deserializable sym a
  , W4.IsSymExprBuilder sym
  ) => 
  sym ->
  -- deserializing environment entries (i.e. interpreting free vars)
  (JSON.Value -> Either DeserializeError (Some (W4.SymExpr sym))) ->
  (JSON.Value -> Either DeserializeError (SomeSymFn sym)) ->
  JSON.Value -> 
  IO (Either DeserializeError a)
w4DeserializeWithEnv sym deser_var deser_fn a = runExceptT $ do
  (index_sexpr_raw :: T.Text) <- getField "index" a
  index_sexpr <- liftMsg $ W4D.parseSExpr index_sexpr_raw 
  
  (var_env_raw :: [(JSON.Value, T.Text)]) <- getField "var_env" a
  var_env <- fmap Map.fromList $ forM var_env_raw $ \(v,t) -> do
    v' <- liftEither $ deser_var v
    return $ (t, v')

  (fn_env_raw :: [(JSON.Value, T.Text)]) <- getField "fn_env" a
  fn_env <- fmap Map.fromList $ forM fn_env_raw $ \(v,t) -> do
    v' <- liftEither $ deser_fn v
    return $ (t, v')
  let cfg = W4D.Config (\t -> return $ Map.lookup t fn_env) (\t -> return $ Map.lookup t var_env)
  Some e <- liftMsg =<< (liftIO $ W4D.deserializeExprWithConfig sym cfg index_sexpr)
  Some (asn :: (Ctx.Assignment (W4.SymExpr sym) ctx)) <- case W4.exprType e of
    W4.BaseStructRepr asn -> fmap Some $
      Ctx.generateM (Ctx.size asn) $ \idx -> liftIO $ W4.structField sym e idx
    _ -> throwError (DeserializeError ("unexpected index type"))
  let 
    deser_ref :: JSON.Value -> Either DeserializeError (Some (W4.SymExpr sym))
    deser_ref ref_val = runExcept $ do
      (idx_int :: Int) <- getField "ref" ref_val
      case Ctx.intIndex idx_int (Ctx.size asn) of
        Just (Some idx) -> return $ Some (asn Ctx.! idx)
        Nothing -> throwError (DeserializeError ("index not found: " ++ show idx_int))
  
  (body :: JSON.Value) <- getField "body" a
  runW4D (JSONEnv sym cfg) (JSONCacheFn deser_ref) $ w4Deserialize @sym @a body

instance forall t st fs. W4Deserializable (W4B.ExprBuilder t st fs) (Some (W4B.Expr t)) where
  w4Deserialize v = do
    (sym :: sym) <- w4DSym
    let
      asInt = fmap Some $ do
        (i :: Integer) <- fromJSON v
        liftIO $ W4.intLit sym i
      asBool = fmap Some $ do
        (b :: Bool) <- fromJSON v
        return $ W4.backendPred sym b
      asBV = do
        (sz :: Integer) <- getField "sz" v
        (bv_raw :: Integer) <- getField "bv" v
        Just (Some w) <- return $ W4.someNat sz
        Just W4.LeqProof <- return $ W4.testLeq (BVS.knownNat @1) w
        Just bv <- return $ BVS.mkBVUnsigned w bv_raw
        Some <$> (liftIO $ W4.bvLit sym w bv)
      asSymbolic = do
        JSONCacheMap m <- (W4D get)
        case Map.lookup v m of
          Just e -> return e
          Nothing -> do
            (sexpr_raw :: T.Text) <- getField "symbolic" v
            cfg <- (W4D $ asks envCfg)
            sexpr <- liftMsg $ W4D.parseSExpr sexpr_raw
            e <- liftMsg =<< (liftIO $ W4D.deserializeExprWithConfig sym cfg sexpr)
            W4D $ put $ JSONCacheMap (Map.insert v e m)
            return e
      asIndexed = do
        JSONCacheFn f <- W4D get
        liftEither (f v)

    asInt <|> asBool <|> asBV <|> asSymbolic <|> asIndexed

w4DeserializeSome :: 
  forall repr sym f tp.
  ( W4.TestEquality repr
  , W4Deserializable sym (Some f)
  , HasRepr f repr
  , W4.KnownRepr repr tp) =>
  JSON.Value ->
  W4D sym (f tp)
w4DeserializeSome v = do
  Some (e :: f x) <- w4Deserialize v
  case W4.testEquality (W4.knownRepr @_ @_ @tp) (typeRepr e) of
    Just W4.Refl -> return e
    Nothing -> throwError $ (DeserializeError "type mismatch")  

instance forall tp t st fs. W4.KnownRepr W4.BaseTypeRepr tp => W4Deserializable (W4B.ExprBuilder t st fs) (W4B.Expr t tp) where
  w4Deserialize = w4DeserializeSome

class (W4Deserializable sym (W4.SymExpr sym tp)) => SymDeserializable1 sym tp
instance W4Deserializable sym (W4.SymExpr sym tp) => SymDeserializable1 sym tp

class (W4.IsExprBuilder sym, (forall tp. W4.KnownRepr W4.BaseTypeRepr tp => SymDeserializable1 sym tp)) => SymDeserializable sym 

instance SymDeserializable (W4B.ExprBuilder t st fs)

instance W4Deserializable sym a => W4Deserializable sym [a] where
  w4Deserialize v = do
    (vs :: [JSON.Value]) <- fromJSON v
    mapM w4Deserialize vs

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (Map x y) where
  w4Serialize x = do
    objs <- forM (Map.toList x) $ \(k, v) -> do
      k_v <- w4Serialize k
      v_v <- w4Serialize v
      return $ JSON.object [ "key" .= k_v, "val" .= v_v]
    return $ JSON.object [ "map" .= objs ]

instance (W4Deserializable sym x, W4Deserializable sym y, Ord x) => W4Deserializable sym (Map x y) where
  w4Deserialize json = do
    (objs :: [JSON.Value]) <- getField "map" json
    fmap Map.fromList $ forM objs $ \obj -> do
      k_v <- getField "key" obj
      (k :: x) <- w4Deserialize k_v
      v_v <- getField "val" obj
      (v :: y) <- w4Deserialize v_v
      return (k,v)

type SerializableExprs sym = W4SerializableF sym (W4.SymExpr sym)

instance (SerializableExprs sym, W4Serializable sym x) => W4Serializable sym (W4P.PredMap sym x k) where
  w4Serialize x = do
    objs <- forM (W4P.toList x) $ \(k,p) -> do
      k_v <- w4Serialize k
      p_v <- w4SerializeF p
      return $ JSON.object [ "val" .= k_v, "pred" .= p_v]
    let (repr :: String) = case typeRepr x of
          W4P.PredConjRepr -> "conj"
          W4P.PredDisjRepr -> "disj"
    return $ JSON.object [ "predmap" .= objs, "kind" .= repr ]

instance (SymDeserializable sym, W4Deserializable sym x, Ord x) => W4Deserializable sym (Some (W4P.PredMap sym x)) where
  w4Deserialize json = do
    (objs :: [JSON.Value]) <- getField "predmap" json
    (kind :: String) <- getField "kind" json

    pairs <- forM objs $ \obj -> do
      k_v <- getField "val" obj
      (k :: x) <- w4Deserialize k_v
      p_v <- getField "pred" obj
      (p :: W4.Pred sym) <- w4Deserialize p_v
      return (k,p)
    Some repr <- case kind of
      "conj" -> return $ Some W4P.PredConjRepr
      "disj" -> return $ Some W4P.PredDisjRepr
      _ -> fail "unexpected repr"
    sym <- w4DSym
    Some <$> (liftIO $ W4P.fromList sym repr pairs)

instance (SymDeserializable sym, W4Deserializable sym x, Ord x, W4.KnownRepr W4P.PredOpRepr k) => W4Deserializable sym (W4P.PredMap sym x k) where
  w4Deserialize = w4DeserializeSome