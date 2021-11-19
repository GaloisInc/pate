{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Pate.Monad.Context (
    ParsedFunctionMap
  , numParsedFunctions
  , numParsedBlocks
  , parsedFunctionEntries
  , parsedFunctionContaining
  , buildParsedFunctionMap
  , buildFunctionEntryMap

  , ParsedBlocks(..)

  , BinaryContext(..)
  , EquivalenceContext(..)
  , currentFunc
  ) where


import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import qualified Data.Map as Map
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified What4.Interface as W4

import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Hints as PH
import qualified Pate.PatchPair as PPa

data ParsedBlocks arch = forall ids. ParsedBlocks [MD.ParsedBlock arch ids]

newtype ParsedFunctionMap arch bin =
  ParsedFunctionMap (Map.Map (PB.FunctionEntry arch bin) (ParsedBlocks arch))

numParsedFunctions :: ParsedFunctionMap arch bin -> Int
numParsedFunctions (ParsedFunctionMap pfm) = Map.size pfm

numParsedBlocks :: ParsedFunctionMap arch bin -> Int
numParsedBlocks (ParsedFunctionMap pfm) =
   sum [ length pbs | ParsedBlocks pbs <- Map.elems pfm ]

-- | Return the list of entry points in the parsed function map
parsedFunctionEntries :: ParsedFunctionMap arch bin -> [PB.FunctionEntry arch bin]
parsedFunctionEntries (ParsedFunctionMap pfm) = Map.keys pfm

buildParsedFunctionMap :: forall arch bin.
  MM.ArchConstraints arch =>
  PBi.KnownBinary bin =>
  MD.DiscoveryState arch ->
  ParsedFunctionMap arch bin
buildParsedFunctionMap ds =
  let fns = Map.assocs (ds ^. MD.funInfo)
      xs = map processDiscoveryFunInfo fns
   in ParsedFunctionMap (Map.fromList xs)
 where
  processDiscoveryFunInfo (_entrySegOff, Some dfi) =
    (funInfoToFunEntry W4.knownRepr dfi, buildParsedBlocks dfi)

buildParsedBlocks :: MD.DiscoveryFunInfo arch ids -> ParsedBlocks arch
buildParsedBlocks dfi = ParsedBlocks (Map.elems (dfi ^. MD.parsedBlocks))

buildFunctionEntryMap ::
  PBi.WhichBinaryRepr bin ->
  Map.Map (MM.ArchSegmentOff arch) (Some (MD.DiscoveryFunInfo arch)) ->
  Map.Map (PA.ConcreteAddress arch) (PB.FunctionEntry arch bin)
buildFunctionEntryMap binRepr disMap = Map.fromList
  [ (PA.segOffToAddr segOff, funInfoToFunEntry binRepr fi)
  | (segOff, Some fi) <- Map.assocs disMap
  ]

funInfoToFunEntry ::
  PBi.WhichBinaryRepr bin ->
  MD.DiscoveryFunInfo arch ids ->
  PB.FunctionEntry arch bin
funInfoToFunEntry binRepr dfi =
  PB.FunctionEntry
  { PB.functionSegAddr = MD.discoveredFunAddr dfi
  , PB.functionSymbol  = MD.discoveredFunSymbol dfi
  , PB.functionBinRepr = binRepr
  }

parsedFunctionContaining ::
  MM.ArchConstraints arch =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  Maybe (ParsedBlocks arch)
parsedFunctionContaining blk (ParsedFunctionMap pfm) =
  Map.lookup (PB.blockFunctionEntry blk) pfm

data BinaryContext arch (bin :: PBi.WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))

  , parsedFunctionMap :: ParsedFunctionMap arch bin

  , binEntry :: PB.FunctionEntry arch bin

  , hints :: PH.VerificationHints

  , functionHintIndex :: Map.Map (PA.ConcreteAddress arch) PH.FunctionDescriptor
  -- ^ An index of the binary hints by function entry point address, used in the
  -- construction of function frames to name parameters

  , binAbortFn :: Maybe (PB.FunctionEntry arch bin)
  -- ^ address of special-purposes "abort" function that represents an abnormal
  -- program exit

  , functionEntryMap :: Map.Map (PA.ConcreteAddress arch) (PB.FunctionEntry arch bin)
  -- ^ A map of all the function entrypoints we know about
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
    } -> EquivalenceContext sym arch

$(L.makeLenses ''EquivalenceContext)
