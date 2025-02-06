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
  , w4ToJSONEnv
  , object
  , w4SerializeString
  , (.=)
  , (.==)
  , (.=~)
  , ExprEnv
  , mergeEnvs
  , ExprCache
  , cacheToEnv
  , emptyExprCache
  , w4ToJSONWithCache
  , W4Deserializable(..)
  , jsonToW4
  , readJSON
  , (.:)
  , SymDeserializable(..)
  , symDeserializable
  , serializeExprEnv
  ) where

import           Control.Monad.State (MonadState (..), State, modify, evalState, runState)

import qualified Data.Map.Ordered as OMap
import           Data.List ( stripPrefix )
import           Data.Maybe ( mapMaybe, catMaybes )
import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Merge.Strict as Map
import           Data.Text (Text)
import           Data.Data (Proxy(..), Typeable)
import qualified Data.Aeson as JSON
import qualified Data.Aeson.Types as JSON
import qualified Data.BitVector.Sized as BVS
import qualified Numeric as N
import           Data.List ( intercalate )

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
import qualified Data.Parameterized.SetF as SetF
import           Data.Parameterized.Classes
import Data.Functor.Const
import Control.Monad.Trans.Reader hiding (asks,ask)
import qualified Data.IORef as IO
import Control.Monad.Reader
import Control.Exception (tryJust)
import What4.Utils.Process (filterAsync)
import qualified What4.ExprHelpers as WEH
import Control.Monad.Except
import Control.Applicative
import GHC.Natural
import Unsafe.Coerce (unsafeCoerce)


newtype ExprCache sym = ExprCache (Map (Some (W4.SymExpr sym)) JSON.Value)

data W4SEnv sym = W4SEnv {
    w4sCache :: IO.IORef (ExprCache sym)
  , w4sSym :: sym
  , w4sUseIdents :: Bool
}

newtype W4S sym a = W4S (ReaderT (W4SEnv sym) IO a)
  deriving (Monad, Applicative, Functor, MonadReader (W4SEnv sym), MonadIO)

-- NB: state updates will persist even if IO exceptions are thrown
instance MonadState (ExprCache sym) (W4S sym) where
  get = do
    cache <- asks w4sCache
    liftIO $ IO.readIORef cache
  state f = do
    cache <- asks w4sCache
    liftIO $ IO.atomicModifyIORef' cache (\c -> let (a,c') = f c in (c',a))

class W4Serializable sym a where
  w4Serialize :: a -> W4S sym JSON.Value

  default w4Serialize :: JSON.ToJSON a => a -> W4S sym JSON.Value
  w4Serialize a = return $ JSON.toJSON a

w4SerializeString :: Show a => a -> W4S sym JSON.Value
w4SerializeString s = return $ JSON.String (T.pack (show s))

w4ToJSON :: forall sym a. SerializableExprs sym => W4Serializable sym a => sym -> a -> IO JSON.Value
w4ToJSON sym a = do
  cacheRef <- IO.newIORef (ExprCache Map.empty)
  W4S f <- return $ w4Serialize @sym a
  let env = W4SEnv cacheRef sym False
  runReaderT f env

newtype ExprEnv sym = ExprEnv (Map Integer (Some (W4.SymExpr sym)))

-- | Serialize an expression binding environment
serializeExprEnv :: forall sym. SerializableExprs sym => sym -> ExprEnv sym -> IO JSON.Value
serializeExprEnv sym (ExprEnv env) = JSON.toJSON <$> do
  forM (Map.toList env) $ \(i, Some (e :: W4.SymExpr sym tp)) -> do
    e_json <- withSerializable (Proxy @sym) (Proxy @(W4.SymExpr sym)) (Proxy @tp) $ w4ToJSON sym e
    return $ JSON.object [ "symbolic_ident" JSON..= i, "symbolic_expr" JSON..= e_json]


mergeEnvs :: TestEquality (W4.SymExpr sym) => ExprEnv sym -> ExprEnv sym -> ExprEnv sym
mergeEnvs (ExprEnv env1) (ExprEnv env2) = ExprEnv (
  Map.merge
    Map.preserveMissing
    Map.preserveMissing
    (Map.zipWithMatched (\_ (Some e1) (Some e2) -> (case testEquality e1 e2 of Just Refl -> Some e1; Nothing -> error $ "Unexpected term hash clash")))
    env1
    env2)

-- | Extract expressions with annotations
cacheToEnv :: W4.IsExprBuilder sym => sym -> ExprCache sym -> IO (ExprEnv sym)
cacheToEnv _sym (ExprCache m) = (ExprEnv . Map.fromList . catMaybes) <$> mapM go (Map.keys m)
  where
    go (Some e)
      | Nothing <- W4.asConcrete e
      = do
        ident <- mkIdent e
        return $ Just (ident, Some e)
    go _ = return Nothing

w4ToJSONEnv :: forall sym a. (W4.IsExprBuilder sym, SerializableExprs sym) => W4Serializable sym a => sym -> a -> IO (JSON.Value, ExprEnv sym)
w4ToJSONEnv sym a = do
  cacheRef <- IO.newIORef (ExprCache Map.empty)
  W4S f <- return $ w4Serialize @sym a
  let env = W4SEnv cacheRef sym True
  v <- runReaderT f env
  c <- IO.readIORef cacheRef
  eenv <- cacheToEnv sym c
  return $ (v, eenv)

emptyExprCache :: ExprCache sym
emptyExprCache = ExprCache Map.empty

w4ToJSONWithCache :: forall sym a. (W4.IsExprBuilder sym, SerializableExprs sym) => W4Serializable sym a => sym -> ExprCache sym -> a -> IO (JSON.Value, ExprCache sym)
w4ToJSONWithCache sym init_cache a = do
  cacheRef <- IO.newIORef init_cache
  W4S f <- return $ w4Serialize @sym a
  let env = W4SEnv cacheRef sym True
  v <- runReaderT f env
  c <- IO.readIORef cacheRef
  return $ (v, c)

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
  env <- ask
  r <- liftIO $ tryJust filterAsync $ do
    x <- runReaderT f env
    evaluate $ force x
  case r of
    Left err -> return $ Left (show err)
    Right x -> return $ Right x

firstHashRef :: IO.IORef (Maybe Integer)
firstHashRef = unsafePerformIO (IO.newIORef Nothing)

-- | Makes hashes slightly more stable by fixing the first requested
--   identifier and deriving all subsequent identifiers as offsets from it
mkIdent :: HashableF t => t tp -> IO Integer
mkIdent v = do
  let (ident :: Integer) = fromIntegral $ hashF v
  let f = \case
        Just i -> (Just i, ident - i)
        Nothing -> (Just ident, 0)
  IO.atomicModifyIORef firstHashRef f

instance sym ~ W4B.ExprBuilder t fs scope => W4Serializable sym (W4B.Expr t tp) where
  w4Serialize e' = do
    ExprCache s <- get
    case Map.lookup (Some e') s of
      Just v -> return $ v
      Nothing -> do
        v <- case W4.asConcrete e' of
          Just (W4.ConcreteInteger i) -> return $ JSON.toJSON i
          Just (W4.ConcreteBool b) -> return $ JSON.toJSON b
          Just (W4.ConcreteStruct cs) ->
            let 
              strs = TFC.toListFC (\c -> show (W4.ppConcrete c)) cs
            in return $ JSON.String (T.pack ("(" ++ intercalate ", " strs ++ ")"))
          Just{} -> return $ JSON.String (T.pack (show (W4.printSymExpr e')))
          _ -> do
            sym <- asks w4sSym
            asks w4sUseIdents >>= \case
              True -> do
                let tp_sexpr = W4S.serializeBaseType (W4.exprType e')
                ident <- liftIO $ mkIdent e'
                return $ JSON.object [ "symbolic_ident" JSON..= ident, "type" JSON..= JSON.String (W4D.printSExpr mempty tp_sexpr) ]
              False -> do
                e <- liftIO $ WEH.stripAnnotations sym e'
                mv <- trySerialize $ do
                  let result = W4S.serializeExprWithConfig (W4S.Config True True) e
                  let var_env = map (\(Some bv, t) -> (show (W4B.bvarName bv), t)) $ OMap.toAscList $ W4S.resFreeVarEnv result
                  let fn_env = map (\(W4S.SomeExprSymFn fn, t) -> (show (W4B.symFnName fn), t)) $ OMap.toAscList $ W4S.resSymFnEnv result
                  let sexpr = W4S.resSExpr result
                  return $ JSON.object [ "symbolic" JSON..= JSON.String (W4D.printSExpr mempty sexpr), "vars" JSON..= var_env, "fns" JSON..= fn_env ]
                case mv of
                  Left er -> return $ JSON.object [ "symbolic_serialize_err" JSON..= er]
                  Right v -> return v
        modify $ \(ExprCache s') -> ExprCache (Map.insert (Some e') v s')
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

instance W4Serializable sym JSON.Value

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

instance W4Serializable sym Integer
instance W4Serializable sym Int
instance W4Serializable sym Text
instance W4Serializable sym Bool

instance W4Serializable sym a => W4Serializable sym (Set a) where
  w4Serialize a = w4Serialize (Set.toList a)

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


data W4DSEnv sym where
   W4DSEnv :: W4.IsExprBuilder sym => {
        w4dsEnv :: ExprEnv sym
      , w4dsSym :: sym
    } -> W4DSEnv sym 

newtype W4DS sym a = W4DS (ExceptT String (ReaderT (W4DSEnv sym) IO) a)
  deriving (Monad, Applicative, Functor, MonadReader (W4DSEnv sym), MonadIO, Alternative, MonadError String)

instance MonadFail (W4DS sym) where
  fail msg = throwError msg

class W4Deserializable sym a where
  w4Deserialize_ :: W4.IsExprBuilder sym => JSON.Value -> W4DS sym a

  default w4Deserialize_ :: (W4.IsExprBuilder sym, JSON.FromJSON a) => JSON.Value -> W4DS sym a
  w4Deserialize_ v = fromJSON v

w4Deserialize :: W4Deserializable sym a => JSON.Value -> W4DS sym a
w4Deserialize v = ask >>= \W4DSEnv{} -> w4Deserialize_ v

withSym :: (W4.IsExprBuilder sym => sym -> W4DS sym a) -> W4DS sym a
withSym f = do
  W4DSEnv{} <- ask
  sym <- asks w4dsSym
  f sym

lookupIdent :: Integer -> W4DS sym (Some (W4.SymExpr sym))
lookupIdent ident = withSym $ \_sym -> do
  ExprEnv env <- asks w4dsEnv
  case Map.lookup ident env of
    Just (Some e) -> return $ Some e
    Nothing -> fail $ "lookupIdent: Missing identifier '" 
      ++ show ident 
      ++ "' from environment:\n"
      ++ show (map (\(i, Some e) -> (i, W4.printSymExpr e)) $ Map.toList env)

instance W4Deserializable sym JSON.Value
instance W4Deserializable sym String
instance W4Deserializable sym Integer
instance W4Deserializable sym Bool
instance W4Deserializable sym ()

jsonToW4 :: (W4Deserializable sym a, W4.IsExprBuilder sym) => sym -> ExprEnv sym -> JSON.Value -> IO (Either String a)
jsonToW4 sym env v = do
  let wenv = W4DSEnv env sym
  let W4DS f = (w4Deserialize v)
  runReaderT (runExceptT f) wenv

fromJSON :: JSON.FromJSON a => JSON.Value -> W4DS sym a
fromJSON v = case JSON.fromJSON v of
  JSON.Success a -> return a
  JSON.Error msg -> fail msg

liftParser :: (b -> JSON.Parser a) -> b -> W4DS sym a
liftParser f v = case JSON.parse f v of
  JSON.Success a -> return a
  JSON.Error msg -> fail msg

readJSON :: forall a sym. Read a => JSON.Value -> W4DS sym a
readJSON v = do
  (vS :: String) <- fromJSON v
  (a :: a,""):_ <- return $ readsPrec 0 vS
  return a

(.:) :: W4Deserializable sym a => JSON.Object -> JSON.Key -> W4DS sym a
(.:) o k = do
  (v :: JSON.Value) <- liftParser ((JSON..:) o) k
  w4Deserialize v

instance (W4Deserializable sym a, W4Deserializable sym b) => W4Deserializable sym (a, b) where
  w4Deserialize_ v = do
    JSON.Object o <- return v
    v1 <- o .: "fst"
    v2 <- o .: "snd"
    return (v1,v2)

instance W4Deserializable sym f => W4Deserializable sym (Const f x) where
  w4Deserialize_ v = Const <$> w4Deserialize v

newtype ToDeserializable sym tp = ToDeserializable { _unDS :: W4.SymExpr sym tp }

instance W4Deserializable sym (Some (ToDeserializable sym)) where
  w4Deserialize_ v = fmap (\(Some x) -> Some (ToDeserializable x)) $ asks w4dsSym >>= \sym -> do
      (i :: Integer) <- fromJSON v
      Some <$> (liftIO $ W4.intLit sym i)
    <|> do
      (b :: Bool) <- fromJSON v
      Some <$> (return $ if b then W4.truePred sym else W4.falsePred sym)
    <|> do
      JSON.String s0 <- return v
      Just s1 <- return $ stripPrefix "0x" (T.unpack s0)
      ((i :: Integer,s2):_) <- return $ N.readHex s1
      Just s3 <- return $ stripPrefix ":[" s2
      ((w :: Natural,_s4):_) <- return $ readsPrec 0 s3
      Just (Some repr) <- return $ W4.someNat w
      Just W4.LeqProof <- return $ W4.isPosNat repr
      Some <$> (liftIO $ W4.bvLit sym repr (BVS.mkBV repr i))
    <|> do
      JSON.Object o <- return v
      (ident :: Integer) <- o .: "symbolic_ident"
      lookupIdent ident


instance forall tp sym. KnownRepr W4.BaseTypeRepr tp => W4Deserializable sym (ToDeserializable sym tp) where
  w4Deserialize_ v = do
    Some (ToDeserializable e :: ToDeserializable sym tp') <- w4Deserialize v
    case testEquality (knownRepr @_ @_ @tp) (W4.exprType e) of
      Just Refl -> return $ ToDeserializable e
      Nothing -> fail $ "Unexpected type: " ++ show (W4.exprType e)

-- | Small hack to pretend that W4.SymExpr has a W4Deserializable instance, which haskell's
-- type class mechanism doesn't support because W4.SymExpr is a type family
data SymDeserializable sym f = W4Deserializable sym (Some f) => SymDeserializable

symDeserializable ::
  forall sym.
  SymDeserializable sym (W4.SymExpr sym)
symDeserializable = unsafeCoerce r
  where
    r :: SymDeserializable sym (ToDeserializable sym)
    r = SymDeserializable