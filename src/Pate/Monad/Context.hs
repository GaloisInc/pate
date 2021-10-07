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
import           Data.IntervalMap.Inteval (Interval, subsumes)
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

data BinaryContext sym arch (bin :: PBi.WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , parsedFunctionMap :: ParsedFunctionMap arch
  , binEntry :: MM.ArchSegmentOff arch
  , hints :: PH.VerificationHints
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    { handles :: CFH.HandleAllocator
    , originalCtx :: BinaryContext sym arch PBi.Original
    , rewrittenCtx :: BinaryContext sym arch PBi.Patched
    , stackRegion :: W4.SymNat sym
    , globalRegion :: W4.SymNat sym
    , _currentFunc :: PPa.BlockPair arch
    } -> EquivalenceContext sym arch

$(L.makeLenses ''EquivalenceContext)



innermostInterval :: Ord a => [(Interval a,b)] -> Maybe (Interval a, b)
innermostInterval [] = Nothing
innermostInterval ((i0,x0):is0) = loop i0 x0 is0
 where
   loop i x [] = Just (i,x)
   loop i x ((j,y):is)
     | IM.subsumes i j = loop j y is
     | IM.subsumes j i = loop i x is
     | otherwise       = Nothing -- No interval is completely contained in another
