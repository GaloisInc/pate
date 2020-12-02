{-# LANGUAGE GADTs #-}
-- | Events that can be reported from the verifier
module Pate.Event (
  Blocks(..),
  EquivalenceResult(..),
  BlockTargetResult(..),
  BranchCompletenessResult(..),
  Event(..)
  ) where

import qualified Data.Macaw.Discovery as MD
import qualified Data.Time as TM

import qualified Pate.Binary as PB
import qualified Pate.Types as PT

-- | The macaw blocks relevant for a given code address
data Blocks arch where
  Blocks :: PT.ConcreteAddress arch -> [MD.ParsedBlock arch ids] -> Blocks arch

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
  CheckedBranchCompleteness :: Blocks arch -> Blocks arch -> BranchCompletenessResult arch -> TM.NominalDiffTime -> Event arch
  DiscoverBlockPair :: Blocks arch -> Blocks arch -> PT.BlockTarget arch PT.Original -> PT.BlockTarget arch PT.Patched -> BlockTargetResult -> TM.NominalDiffTime -> Event arch
  CheckedEquivalence :: Blocks arch -> Blocks arch -> EquivalenceResult arch -> TM.NominalDiffTime -> Event arch
  LoadedBinaries :: (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> Event arch
