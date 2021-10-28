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
  , parsedBlocksContaining

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

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
newtype ParsedFunctionMap arch = ParsedFunctionMap
  { getParsedFunctionMap :: IntervalMap (PA.ConcreteAddress arch) (Map.Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))
  }

numParsedFunctions :: ParsedFunctionMap arch -> Int
numParsedFunctions (ParsedFunctionMap pfm) = length (IM.keys pfm)

numParsedBlocks :: ParsedFunctionMap arch -> Int
numParsedBlocks (ParsedFunctionMap pfm) =
   sum [ length (IM.elems pbm)
       | bmap <- IM.elems pfm
       , Some (ParsedBlockMap pbm) <- Map.elems bmap
       ]

-- | Return the list of entry points in the parsed function map
parsedFunctionEntries :: ParsedFunctionMap arch -> [MM.ArchSegmentOff arch]
parsedFunctionEntries = concatMap Map.keys . IM.elems . getParsedFunctionMap

buildParsedFunctionMap :: forall arch.
  MM.ArchConstraints arch =>
  MD.DiscoveryState arch ->
  ParsedFunctionMap arch
buildParsedFunctionMap ds =
  let fns = Map.assocs (ds ^. MD.funInfo)
      xs = map processDiscoveryFunInfo fns
   in ParsedFunctionMap (IM.unionsWith Map.union xs)

 where
  processDiscoveryFunInfo ::
    (MM.ArchSegmentOff arch, Some (MD.DiscoveryFunInfo arch)) ->
    IntervalMap (PA.ConcreteAddress arch) (Map.Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))
  processDiscoveryFunInfo (entrySegOff, Some dfi) =
    let blocks = buildParsedBlockMap dfi
     in Map.singleton entrySegOff (Some blocks) <$ getParsedBlockMap blocks

buildParsedBlockMap ::
  MM.ArchConstraints arch =>
  MD.DiscoveryFunInfo arch ids ->
  ParsedBlockMap arch ids
buildParsedBlockMap dfi = ParsedBlockMap . IM.fromListWith (++) $
  [ (archSegmentOffToInterval blockSegOff (MD.blockSize pb), [pb])
  | (blockSegOff, pb) <- Map.assocs (dfi ^. MD.parsedBlocks)
  ]

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
  PA.ConcreteAddress arch ->
  ParsedFunctionMap arch ->
  Either [MM.ArchSegmentOff arch] (MM.ArchSegmentOff arch, PA.ConcreteAddress arch, Some (ParsedBlockMap arch))
parsedFunctionContaining addr (ParsedFunctionMap pfm) =
  let fns = Map.assocs $ Map.unions $ fmap snd $ IM.lookupLE i pfm
      fns' = fmap (\(segOff, pbm) -> (segOff, segOffToAddr segOff, pbm)) fns
  in case reverse $ filter (\(_, addr', _) -> addr' <= start) fns' of
       (x:_) -> Right x
       [] -> Left (fst <$> fns)
 where
  start@(PA.ConcreteAddress saddr) = addr
  end = PA.ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
  i = IM.OpenInterval start end

parsedBlocksContaining ::
  MM.ArchConstraints arch =>
  PA.ConcreteAddress arch ->
  ParsedBlockMap arch ids ->
  [MD.ParsedBlock arch ids]
parsedBlocksContaining addr (ParsedBlockMap pbm) =
    concat $ IM.elems $ IM.intersecting pbm i
  where
   start@(PA.ConcreteAddress saddr) = addr
   end = PA.ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
   i = IM.OpenInterval start end

segOffToAddr ::
  MM.ArchSegmentOff arch ->
  PA.ConcreteAddress arch
segOffToAddr off = PA.addressFromMemAddr (MM.segoffAddr off)


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

data BinaryContext arch (bin :: PBi.WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))

  , parsedFunctionMap :: ParsedFunctionMap arch

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
