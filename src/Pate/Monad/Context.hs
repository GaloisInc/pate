{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
module Pate.Monad.Context (
    ParsedFunctionMap
  , ParsedBlockMap(..)
  , BinaryContext(..)
  , EquivalenceContext(..)
  , currentFunc
  ) where


import qualified Control.Lens as L
import           Data.IntervalMap (IntervalMap)
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
import qualified Pate.Hints as PH
import qualified Pate.PatchPair as PPa

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (PA.ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (PA.ConcreteAddress arch) (Map.Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))

data BinaryContext arch (bin :: PBi.WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , parsedFunctionMap :: ParsedFunctionMap arch
  , binEntry :: MM.ArchSegmentOff arch
  , hints :: PH.VerificationHints
  , functionHintIndex :: Map.Map (PA.ConcreteAddress arch) PH.FunctionDescriptor
  -- ^ An index of the binary hints by function entry point address, used in the
  -- construction of function frames to name parameters
  , binAbortFn :: Maybe (MM.ArchSegmentOff arch)
  -- ^ address of special-purposes "abort" function that represents an abnormal
  -- program exit
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    { handles :: CFH.HandleAllocator
    , binCtxs :: PPa.PatchPair (BinaryContext arch)
    , stackRegion :: W4.SymNat sym
    , globalRegion :: W4.SymNat sym
    , _currentFunc :: PPa.BlockPair arch
    } -> EquivalenceContext sym arch

$(L.makeLenses ''EquivalenceContext)
