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

module What4.JSON 
  ( W4S
  , W4Serializable(..)
  , W4SerializableF(..)
  , W4SerializableFC
  , SerializableExprs
  , w4ToJSON
  ) where

import           Control.Monad.Except (ExceptT, MonadError)
import           Control.Monad.Reader (ReaderT, MonadReader)
import           Control.Monad.IO.Class (MonadIO)
import           Control.Monad.State (StateT, MonadState (..), State, modify, evalState)

import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Data (Proxy(..), Typeable)
import qualified Data.Aeson as JSON
import           Data.Aeson ( (.=) )

import           Data.Parameterized.Some (Some(..))

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


newtype ExprCache sym = ExprCache (Map (Some (W4.SymExpr sym)) JSON.Value)

newtype W4S sym a = W4S (State (ExprCache sym) a)
  deriving (Monad, Applicative, Functor, MonadState (ExprCache sym))

class W4Serializable sym a where
  w4Serialize :: a -> W4S sym JSON.Value


w4ToJSON :: forall sym a. W4Serializable sym a => a -> JSON.Value
w4ToJSON a = let W4S f = w4Serialize @sym a in evalState f (ExprCache Map.empty)

class W4SerializableF sym f where
  withSerializable :: Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a

  default withSerializable :: W4Serializable sym (f tp) => Proxy sym -> p f -> q tp -> (W4Serializable sym (f tp) => a) -> a
  withSerializable _ _ _ x = x

  w4SerializeF :: forall tp. f tp -> W4S sym JSON.Value
  w4SerializeF x = withSerializable (Proxy :: Proxy sym) (Proxy :: Proxy f) (Proxy :: Proxy tp) (w4Serialize x)

class (forall sym. W4SerializableF sym f) => W4SerializableFC f where


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
            let sexpr = W4S.serializeExpr e
            return $ JSON.object [ "symbolic" .= JSON.String (W4D.printSExpr mempty sexpr) ]
        modify $ \(ExprCache s') -> ExprCache (Map.insert (Some e) v s')
        return v

deriving instance Typeable (W4B.ExprBuilder t fs scope)

instance sym ~ W4B.ExprBuilder t fs scope => W4SerializableF sym (W4B.Expr t) where

instance W4SerializableF sym x => W4Serializable sym (Some x) where
  w4Serialize (Some x) = w4SerializeF x

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (x, y) where
  w4Serialize (x,y) = do
    x_v <- w4Serialize x
    y_v <- w4Serialize y
    return $ JSON.object [ "fst" .= x_v, "snd" .= y_v]

instance (W4Serializable sym x, W4Serializable sym y) => W4Serializable sym (Map x y) where
  w4Serialize x = do
    objs <- forM (Map.toList x) $ \(k, v) -> do
      k_v <- w4Serialize k
      v_v <- w4Serialize v
      return $ JSON.object [ "key" .= k_v, "val" .= v_v]
    return $ JSON.object [ "map" .= objs ]

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

instance W4Serializable sym Integer where
  w4Serialize i = return $ JSON.toJSON i

instance W4Serializable sym String where
  w4Serialize i = return $ JSON.toJSON i

