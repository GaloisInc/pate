module Pate.SymbolTable (
    Symbol(..)
  , SymbolTable
  , emptySymbolTable
  , addSymbolTableEntry
  , lookupSymbol
  ) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import qualified Data.Macaw.CFG as DMC

data Symbol = LocalSymbol !T.Text
            -- ^ Symbols local to the binary
            | PLTSymbol !T.Text
            -- ^ Symbols representing PLT stubs
            --
            -- These don't really have symbols in the binary.  They are often
            -- rendered as @sym\@plt@, but that is not a firm convention or used
            -- by the toolchains at all.  This extra constructor lets us keep
            -- the namespaces separate cleanly without string munging.
            deriving (Eq, Ord, Show)


-- | A map from addresses to symbol names
newtype SymbolTable arch =
  SymbolTable { getSymbolTable :: Map.Map (BVS.BV (DMC.ArchAddrWidth arch)) Symbol }
  deriving (Show)

emptySymbolTable :: SymbolTable arch
emptySymbolTable = SymbolTable Map.empty

-- | Add a mapping to the table
addSymbolTableEntry
  :: BVS.BV (DMC.ArchAddrWidth arch)
  -> Symbol
  -> SymbolTable arch
  -> SymbolTable arch
addSymbolTableEntry addr name (SymbolTable m) =
  SymbolTable (Map.insert addr name m)

lookupSymbol
  :: BVS.BV (DMC.ArchAddrWidth arch)
  -> SymbolTable arch
  -> Maybe Symbol
lookupSymbol addr (SymbolTable m) = Map.lookup addr m
