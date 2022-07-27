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
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Text as T
import qualified Data.Time as TM
import           Data.Word ( Word64 )
import qualified GHC.Stack as GS
import qualified What4.Expr as WE
import qualified What4.Interface as WI

import qualified Pate.Arch as PArch
import qualified Pate.Address as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.DWARF as PHD
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.PatchPair as PPa
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.Statistics as PES
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification.PairGraph.Node as PVPN
import qualified Pate.Verification.StrongestPosts.CounterExample as PVSC

-- | The macaw blocks relevant for a given code address
data Blocks arch bin where
  Blocks :: PN.NatRepr (DMC.ArchAddrWidth arch) -> PB.ConcreteBlock arch bin -> [MD.ParsedBlock arch ids] -> Blocks arch bin

type BlocksPair arch = PPa.PatchPair (Blocks arch)

data EquivalenceResult arch = Equivalent
                            | Inconclusive
                            | Inequivalent (PF.InequivalenceResult arch)

data BlockTargetResult = Reachable
                       | InconclusiveTarget
                       | Unreachable

data BranchCompletenessResult arch = BranchesComplete
                                   | InconclusiveBranches
                                   | BranchesIncomplete (PF.InequivalenceResult arch)

-- | Events that can be reported from the verifier
--
-- This can include traditional logging information, but also statistics about
-- verification successes and failures that can be streamed to the user.
data Event arch where
  AnalysisEnd :: PES.EquivalenceStatistics -> TM.NominalDiffTime -> Event arch
  AnalysisStart :: PPa.BlockPair arch -> Event arch
  ErrorRaised :: PEE.EquivalenceError arch -> Event arch
  Warning :: PEE.EquivalenceError arch -> Event arch
  -- | final top-level result
  ProvenGoal :: BlocksPair arch ->  PFI.SomeProofNonceExpr arch PF.ProofBlockSliceType -> TM.NominalDiffTime -> Event arch
  -- | intermediate results
  ProofIntermediate :: BlocksPair arch -> PFI.SomeProofNonceExpr arch tp -> TM.NominalDiffTime -> Event arch
  ProofStarted :: BlocksPair arch -> PFI.SomeProofNonceExpr arch tp -> TM.NominalDiffTime -> Event arch

  CheckedBranchCompleteness :: BlocksPair arch -> BranchCompletenessResult arch -> TM.NominalDiffTime -> Event arch
  DiscoverBlockPair :: BlocksPair arch -> PB.BlockTarget arch PB.Original -> PB.BlockTarget arch PB.Patched -> BlockTargetResult -> TM.NominalDiffTime -> Event arch
  ComputedPrecondition :: BlocksPair arch -> TM.NominalDiffTime -> Event arch
  ElfLoaderWarnings :: [DEE.ElfParseError] -> Event arch
  CheckedEquivalence :: BlocksPair arch -> EquivalenceResult arch -> TM.NominalDiffTime -> Event arch
  LoadedBinaries :: PLE.LoadedELF arch -> PLE.LoadedELF arch -> Event arch
  -- | Function/block start hints that point to unmapped addresses
  FunctionEntryInvalidHints :: PB.WhichBinaryRepr bin -> [(T.Text, Word64)] -> Event arch
  -- | A list of functions discovered from provided hints that macaw code
  -- discovery was not able to identify by itself
  FunctionsDiscoveredFromHints :: PB.WhichBinaryRepr bin -> [PB.FunctionEntry arch bin] -> Event arch
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
  ProofTraceEvent :: GS.CallStack -> PA.ConcreteAddress arch -> PA.ConcreteAddress arch -> T.Text -> TM.NominalDiffTime -> Event arch
  -- | A low-level trace event that contains a formula that should be displayed
  -- to the user in some structured way, when possible
  --
  -- This has to save enough constraints to allow us to traverse the term
  ProofTraceFormulaEvent :: (sym ~ WE.ExprBuilder t st fs) => GS.CallStack -> PA.ConcreteAddress arch -> PA.ConcreteAddress arch -> sym -> WI.SymExpr sym tp -> TM.NominalDiffTime -> Event arch


  -- | The strongest postcondition verifier has completed with the given status
  StrongestPostOverallResult :: PE.EquivalenceStatus -> TM.NominalDiffTime -> Event arch
  -- | The strongest postcondition verifier discovered an observable difference in behavior (reported as a counterexample)
  StrongestPostObservable :: (WI.IsExprBuilder sym) => PPa.BlockPair arch -> PVSC.ObservableCounterexample sym (DMC.ArchAddrWidth arch) -> Event arch
  -- | The strongest postcondition verifier has discovered a desynchronization in the control flow of the programs
  StrongestPostDesync :: PPa.BlockPair arch -> PVSC.TotalityCounterexample (DMC.ArchAddrWidth arch) -> Event arch
  -- | The strongest postcondition analysis ran out of gas when analyzing the given pair
  GasExhausted :: (PArch.ValidArch arch) => PVPN.GraphNode arch -> Event arch
  -- | Other errors that can occur inside of the strongest postcondition verifier
  StrongestPostMiscError :: (PArch.ValidArch arch) => PVPN.GraphNode arch -> T.Text -> Event arch
