{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module Pate.Address (
    ConcreteAddress(..)
  , addressFromMemAddr
  , addressAddOffset
  ) where

import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MM

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)

deriving instance Show (ConcreteAddress arch)

instance PP.Pretty (ConcreteAddress arch) where
  pretty (ConcreteAddress addr) = PP.pretty addr

addressAddOffset :: (MM.MemWidth (MM.ArchAddrWidth arch))
                 => ConcreteAddress arch
                 -> MM.MemWord (MM.ArchAddrWidth arch)
                 -> ConcreteAddress arch
addressAddOffset (ConcreteAddress memAddr) memWord =
  ConcreteAddress (MM.incAddr (fromIntegral memWord) memAddr)

addressFromMemAddr
  :: MM.MemAddr (MM.ArchAddrWidth arch)
  -> ConcreteAddress arch
addressFromMemAddr = ConcreteAddress
