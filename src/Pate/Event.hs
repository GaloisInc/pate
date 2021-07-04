{-# LANGUAGE GADTs #-}
-- | Events that can be reported from the verifier
module Pate.Event (
  Blocks(..),
  BlocksPair,
  EquivalenceResult(..),
  BlockTargetResult(..),
  BranchCompletenessResult(..),
  Event(..)
  ) where

import qualified Data.ElfEdit as DEE
import qualified Data.List.NonEmpty as DLN
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Text as T
import qualified Data.Time as TM
import           Data.Word ( Word64 )
import qualified GHC.Stack as GS

import qualified Pate.Binary as PB
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.DWARF as PHD
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI

-- | The macaw blocks relevant for a given code address
data Blocks arch bin where
  Blocks :: PT.ConcreteBlock arch bin -> [MD.ParsedBlock arch ids] -> Blocks arch bin

type BlocksPair arch = PT.PatchPair (Blocks arch)

data EquivalenceResult arch = Equivalent
                            | Inconclusive
                            | Inequivalent (PFI.InequivalenceResult arch)

data BlockTargetResult = Reachable
                       | InconclusiveTarget
                       | Unreachable

data BranchCompletenessResult arch = BranchesComplete
                                   | InconclusiveBranches
                                   | BranchesIncomplete (PFI.InequivalenceResult arch)

-- | Events that can be reported from the verifier
--
-- This can include traditional logging information, but also statistics about
-- verification successes and failures that can be streamed to the user.
data Event arch where
  AnalysisEnd :: PT.EquivalenceStatistics -> TM.NominalDiffTime -> Event arch
  AnalysisStart :: PT.BlockPair arch -> Event arch
  ErrorRaised :: PT.EquivalenceError arch -> Event arch
  Warning :: BlocksPair arch -> PT.EquivalenceError arch -> Event arch
  -- | final top-level result
  ProvenGoal :: BlocksPair arch ->  PFI.SomeProofSym arch PF.ProofBlockSliceType -> TM.NominalDiffTime -> Event arch
  -- | intermediate results
  ProofIntermediate :: BlocksPair arch -> PFI.SomeProofSym arch tp -> TM.NominalDiffTime -> Event arch
  ProofStarted :: BlocksPair arch -> PFI.SomeProofSym arch tp -> TM.NominalDiffTime -> Event arch

  CheckedBranchCompleteness :: BlocksPair arch -> BranchCompletenessResult arch -> TM.NominalDiffTime -> Event arch
  DiscoverBlockPair :: BlocksPair arch -> PT.BlockTarget arch PT.Original -> PT.BlockTarget arch PT.Patched -> BlockTargetResult -> TM.NominalDiffTime -> Event arch
  ComputedPrecondition :: BlocksPair arch -> TM.NominalDiffTime -> Event arch
  ElfLoaderWarnings :: [DEE.ElfParseError] -> Event arch
  CheckedEquivalence :: BlocksPair arch -> EquivalenceResult arch -> TM.NominalDiffTime -> Event arch
  LoadedBinaries :: (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> (PB.LoadedELF arch, PT.ParsedFunctionMap arch) -> Event arch
  -- | Function/block start hints that point to unmapped addresses
  FunctionEntryInvalidHints :: [(T.Text, Word64)] -> Event arch
  -- | A list of functions discovered from provided hints that macaw code
  -- discovery was not able to identify by itself
  FunctionsDiscoveredFromHints :: [MC.ArchSegmentOff arch] -> Event arch
  HintErrorsCSV :: DLN.NonEmpty PHC.CSVParseError -> Event arch
  HintErrorsJSON :: DLN.NonEmpty PHJ.JSONError -> Event arch
  HintErrorsDWARF :: DLN.NonEmpty PHD.DWARFError -> Event arch
  -- | A very low-level event generated during the proof construction or evaluation
  --
  -- It records a pair of block addresses and a message that describes the state
  -- of the proof for that block pair.
  --
  -- This is useful for debugging, but probably should not be shown/collected
  -- unless explicitly asked for.
  ProofTraceEvent :: GS.CallStack -> PT.ConcreteAddress arch -> PT.ConcreteAddress arch -> T.Text -> TM.NominalDiffTime -> Event arch
