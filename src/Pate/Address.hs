{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module Pate.Address (
    ConcreteAddress
  , segOffToAddr
  , memAddrToAddr
  , addrToMemAddr
  ) where

import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MM

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)

instance Show (ConcreteAddress arch) where
  show (ConcreteAddress addr) = show addr

instance PP.Pretty (ConcreteAddress arch) where
  pretty (ConcreteAddress addr) = PP.pretty addr

memAddrToAddr ::
  MM.MemAddr (MM.ArchAddrWidth arch) ->
  ConcreteAddress arch
memAddrToAddr = ConcreteAddress

segOffToAddr ::
  MM.ArchSegmentOff arch ->
  ConcreteAddress arch
segOffToAddr off = ConcreteAddress (MM.segoffAddr off)

addrToMemAddr ::
  ConcreteAddress arch ->
  MM.MemAddr (MM.ArchAddrWidth arch)
addrToMemAddr (ConcreteAddress a) = a
