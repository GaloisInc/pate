{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Pate.Address (
    ConcreteAddress
  , segOffToAddr
  , memAddrToAddr
  , addrToMemAddr
  , addOffset
  , addrAsSegOff
  ) where

import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MM
import qualified Data.Aeson as JSON

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)

instance Show (ConcreteAddress arch) where
  show (ConcreteAddress addr) = show addr

instance PP.Pretty (ConcreteAddress arch) where
  pretty (ConcreteAddress addr) = PP.pretty addr

instance JSON.ToJSON (ConcreteAddress arch) where
  toJSON (ConcreteAddress addr) = JSON.toJSON addr

instance JSON.ToJSON (MM.MemAddr w) where
  toJSON addr = JSON.object [ "base" JSON..= MM.addrBase addr, "offset" JSON..= show (MM.addrOffset addr)]

instance JSON.ToJSON (MM.MemSegmentOff w) where
  toJSON addr = JSON.toJSON (MM.segoffAddr addr)

addOffset :: MM.MemWidth (MM.ArchAddrWidth arch) => Integer -> ConcreteAddress arch -> ConcreteAddress arch
addOffset i (ConcreteAddress addr) = ConcreteAddress (MM.incAddr i addr)

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

addrAsSegOff ::
  MM.Memory (MM.ArchAddrWidth arch) ->
  ConcreteAddress arch ->
  Maybe (MM.ArchSegmentOff arch)
addrAsSegOff mem (ConcreteAddress (MM.MemAddr base offset)) = 
  MM.resolveRegionOff mem base offset
