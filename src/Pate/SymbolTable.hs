module Pate.SymbolTable (
    SymbolTable
  , emptySymbolTable
  , addSymbolTableEntry
  , lookupSymbol
  ) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import qualified Data.Macaw.CFG as DMC

-- | A map from addresses to symbol names
newtype SymbolTable arch =
  SymbolTable { getSymbolTable :: Map.Map (BVS.BV (DMC.ArchAddrWidth arch)) T.Text }
  deriving (Show)

emptySymbolTable :: SymbolTable arch
emptySymbolTable = SymbolTable Map.empty

-- | Add a mapping to the table
addSymbolTableEntry
  :: BVS.BV (DMC.ArchAddrWidth arch)
  -> T.Text
  -> SymbolTable arch
  -> SymbolTable arch
addSymbolTableEntry addr name (SymbolTable m) =
  SymbolTable (Map.insert addr name m)

lookupSymbol
  :: BVS.BV (DMC.ArchAddrWidth arch)
  -> SymbolTable arch
  -> Maybe T.Text
lookupSymbol addr (SymbolTable m) = Map.lookup addr m
