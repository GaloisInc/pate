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

  , ParsedBlockMap
  , parsedBlocksForward
  , allParsedBlocks

  , BinaryContext(..)
  , EquivalenceContext(..)
  , currentFunc
  ) where


import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
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

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (PA.ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

newtype ParsedFunctionMap arch bin = ParsedFunctionMap
  { getParsedFunctionMap :: Map.Map (PB.FunctionEntry arch bin) (Some (ParsedBlockMap arch))
  }

numParsedFunctions :: ParsedFunctionMap arch bin -> Int
numParsedFunctions (ParsedFunctionMap pfm) = Map.size pfm

numParsedBlocks :: ParsedFunctionMap arch bin -> Int
numParsedBlocks (ParsedFunctionMap pfm) =
   sum [ length (IM.elems pbm)
       | Some (ParsedBlockMap pbm) <- Map.elems pfm
       ]

-- | Return the list of entry points in the parsed function map
parsedFunctionEntries :: ParsedFunctionMap arch bin -> [PB.FunctionEntry arch bin]
parsedFunctionEntries = Map.keys . getParsedFunctionMap

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
  processDiscoveryFunInfo ::
    (MM.ArchSegmentOff arch, Some (MD.DiscoveryFunInfo arch)) ->
    (PB.FunctionEntry arch bin, Some (ParsedBlockMap arch))
  processDiscoveryFunInfo (_entrySegOff, Some dfi) =
    (funInfoToFunEntry W4.knownRepr dfi, Some (buildParsedBlockMap dfi))

buildParsedBlockMap ::
  MM.ArchConstraints arch =>
  MD.DiscoveryFunInfo arch ids ->
  ParsedBlockMap arch ids
buildParsedBlockMap dfi = ParsedBlockMap . IM.fromListWith (++) $
  [ (archSegmentOffToInterval blockSegOff (MD.blockSize pb), [pb])
  | (blockSegOff, pb) <- Map.assocs (dfi ^. MD.parsedBlocks)
  ]

buildFunctionEntryMap ::
  PBi.WhichBinaryRepr bin ->
  Map.Map (MM.ArchSegmentOff arch) (Some (MD.DiscoveryFunInfo arch)) ->
  Map.Map (PA.ConcreteAddress arch) (PB.FunctionEntry arch bin)
buildFunctionEntryMap binRepr disMap = Map.fromList
  [ (segOffToAddr segOff, funInfoToFunEntry binRepr fi)
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

archSegmentOffToInterval ::
  MM.ArchConstraints arch =>
  MM.ArchSegmentOff arch ->
  Int ->
  IM.Interval (PA.ConcreteAddress arch)
archSegmentOffToInterval segOff size =
  let start = segOffToAddr segOff
  in IM.IntervalCO start (start `PA.addressAddOffset` fromIntegral size)


parsedFunctionContaining ::
  MM.ArchConstraints arch =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  Either [MM.ArchSegmentOff arch] (Some (ParsedBlockMap arch))
parsedFunctionContaining blk (ParsedFunctionMap pfm) =
  case Map.lookup (PB.blockFunctionEntry blk) pfm of
    Just pbm -> Right pbm
    Nothing -> Left []

-- | Find all the blocks in a parsed block map with addresses
--   greater or equal to the given address.
parsedBlocksForward ::
  MM.ArchConstraints arch =>
  PA.ConcreteAddress arch ->
  ParsedBlockMap arch ids ->
  [MD.ParsedBlock arch ids]
parsedBlocksForward addr (ParsedBlockMap pbm) =
    concat $ IM.elems $ IM.intersecting pbm i
  where
   start@(PA.ConcreteAddress saddr) = addr
   end = PA.ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
   i = IM.OpenInterval start end

allParsedBlocks ::
  MM.ArchConstraints arch =>
  ParsedBlockMap arch ids ->
  [MD.ParsedBlock arch ids]
allParsedBlocks (ParsedBlockMap pbm) = concat $ IM.elems $ pbm


segOffToAddr ::
  MM.ArchSegmentOff arch ->
  PA.ConcreteAddress arch
segOffToAddr off = PA.addressFromMemAddr (MM.segoffAddr off)



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
