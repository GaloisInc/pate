{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Pate.Monad.Context (
    BinaryContext(..)
  , EquivalenceContext(..)
  , currentFunc
  ) where

import qualified Control.Lens as L
import qualified Data.Map as Map

import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified What4.Interface as W4

import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Discovery.ParsedFunctions as PDP
import qualified Pate.Hints as PH
import qualified Pate.PatchPair as PPa
import qualified Pate.SymbolTable as PSym


data BinaryContext arch (bin :: PBi.WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))

  , parsedFunctionMap :: PDP.ParsedFunctionMap arch bin

  , binEntry :: PB.FunctionEntry arch bin

  , hints :: PH.VerificationHints

  , functionHintIndex :: Map.Map (PA.ConcreteAddress arch) PH.FunctionDescriptor
  -- ^ An index of the binary hints by function entry point address, used in the
  -- construction of function frames to name parameters

  , binAbortFn :: Maybe (PB.FunctionEntry arch bin)
  -- ^ address of special-purposes "abort" function that represents an abnormal
  -- program exit
  , symbolTable :: PSym.SymbolTable arch
  -- ^ A mapping of addresses to symbols used to match overrides to callees
  -- during symbolic execution in the inline-callee mode
  --
  -- Note that this table has more entries than the 'functionHintIndex', as it
  -- also includes entries from the dynamic symbol table representing the
  -- addresses of PLT stubs that call out to shared library functions
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    { handles :: CFH.HandleAllocator
    , binCtxs :: PPa.PatchPair (BinaryContext arch)
    , stackRegion :: W4.SymNat sym
    , globalRegion :: W4.SymNat sym
      -- NB, currentFunc is misnamed, as it corresponds to a pair of blocks under consideration,
      -- but they might not be function entry points
    , _currentFunc :: PPa.BlockPair arch
    , originalIgnorePtrs :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
    , patchedIgnorePtrs :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
    , equatedFunctions :: [(PA.ConcreteAddress arch, PA.ConcreteAddress arch)]
    , observableMemory :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
    } -> EquivalenceContext sym arch

$(L.makeLenses ''EquivalenceContext)

{- Note [Ignored Functions]

We want to support ignoring parts of a program during verification. This is
unsound, but can be useful for dealing with large binaries and targeted changes
where the user wants to focus their analysis on parts of the program they are
concerned about. This mode of operation enables the user to specify individual
functions they would like to ignore (along with all of the callees of those
functions).

Operationally, we ignore functions by treating them as no-ops, which we
accomplish by returning an empty function from code discovery. This is then
translated into a no-op in the verifier without any additional changes to the
proof engine.

We capture the necessary metadata (from the PatchData) in the ParsedFunctionMap,
which is the core cache for all code discovery activities.

-}
