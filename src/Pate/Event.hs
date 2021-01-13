{-# LANGUAGE GADTs #-}
-- | Events that can be reported from the verifier
module Pate.Event (
  Blocks(..),
  BlocksPair(..),
  EquivalenceResult(..),
  BlockTargetResult(..),
  BranchCompletenessResult(..),
  Event(..)
  ) where

import qualified Data.ElfEdit as DEE
import qualified Data.Macaw.Discovery as MD
import qualified Data.Time as TM

import qualified Pate.Binary as PB
import qualified Pate.Types as PT
import qualified Pate.Equivalence as PE

-- | The macaw blocks relevant for a given code address
data Blocks arch bin where
  Blocks :: PT.ConcreteBlock arch bin -> [MD.ParsedBlock arch ids] -> Blocks arch bin

data BlocksPair arch =
  BlocksPair
    { blocksO :: Blocks arch PT.Original
    , blocksP :: Blocks arch PT.Patched
    }

data EquivalenceResult arch = Equivalent
                            | Inconclusive
                            | Inequivalent (PT.InequivalenceResult arch)

data BlockTargetResult = Reachable
                       | InconclusiveTarget
                       | Unreachable

data BranchCompletenessResult arch = BranchesComplete
                                   | InconclusiveBranches
                                   | BranchesIncomplete (PT.InequivalenceResult arch)

-- | Events that can be reported from the verifier
--
-- This can include traditional logging information, but also statistics about
-- verification successes and failures that can be streamed to the user.
data Event arch where
  ProvenTriple :: BlocksPair arch -> PE.SomeProofBlockSlice arch -> TM.NominalDiffTime -> Event arch
  CheckedBranchCompleteness :: BlocksPair arch -> BranchCompletenessResult arch -> TM.NominalDiffTime -> Event arch
  DiscoverBlockPair :: BlocksPair arch -> PT.BlockTarget arch PT.Original -> PT.BlockTarget arch PT.Patched -> BlockTargetResult -> TM.NominalDiffTime -> Event arch
  ComputedPrecondition :: BlocksPair arch -> TM.NominalDiffTime -> Event arch
  ElfLoaderWarnings :: [DEE.ElfParseError] -> Event arch
  CheckedEquivalence :: BlocksPair arch -> EquivalenceResult arch -> TM.NominalDiffTime -> Event arch
  LoadedBinaries :: (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> Event arch
