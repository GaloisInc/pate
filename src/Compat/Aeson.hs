{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Compat.Aeson ( lookup, toList, fromList, module Data.HashMap.Strict ) where

import Prelude hiding (lookup)
import qualified Data.Aeson as JSON
import qualified Data.Aeson.KeyMap as AKM
import qualified Data.Aeson.Key as AK
import qualified Data.Text as T
import           Data.Hashable
import qualified Data.HashMap.Strict as HMS
-- for re-export
import           Data.HashMap.Strict hiding (lookup, toList, fromList, map)

class MapLike hm k v | hm -> k, hm -> v where
  lookup :: k -> hm -> Maybe v
  toList :: hm -> [(k, v)]
  fromList :: [(k, v)] -> hm

instance MapLike (AKM.KeyMap (JSON.Value)) T.Text JSON.Value where
  lookup nm km = AKM.lookup (AK.fromText nm) km
  toList km = map (\(k,v) -> (AK.toText k, v)) (AKM.toList km)
  fromList ls = AKM.fromList $ map (\(k,v) -> (AK.fromText k, v)) ls

instance (Eq k, Hashable k) => MapLike (HMS.HashMap k v) k v where
  lookup = HMS.lookup
  toList = HMS.toList
  fromList = HMS.fromList

