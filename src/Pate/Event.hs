{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Events that can be reported from the verifier
module Pate.Event (
  Blocks(..),
  BlocksPair,
  BlockTargetResult(..),
  Event(..),
  SolverResultKind(..),
  SolverProofKind(..)
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
import qualified Prettyprinter as PP

import qualified Pate.Arch as PArch
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Address as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.DWARF as PHD
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Hints.BSI as PHB
import qualified Pate.SimState as PS
import qualified Pate.PatchPair as PPa
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.Statistics as PES
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification.PairGraph.Node as PVPN
import qualified Pate.Verification.StrongestPosts.CounterExample as PVSC

import           Pate.TraceTree

-- | The macaw blocks relevant for a given code address
data Blocks arch bin where
  Blocks :: PN.NatRepr (DMC.ArchAddrWidth arch) -> PB.ConcreteBlock arch bin -> [MD.ParsedBlock arch ids] -> Blocks arch bin

type BlocksPair arch = PPa.PatchPair (Blocks arch)

data BlockTargetResult = Reachable
                       | InconclusiveTarget
                       | Unreachable
  deriving (Eq, Ord, Show)

instance IsTraceNode k "blocktargetresult" where
  type TraceNodeType k "blocktargetresult" = BlockTargetResult
  prettyNode () result = PP.pretty (show result)


-- | Events that can be reported from the verifier
--
-- This can include traditional logging information, but also statistics about
-- verification successes and failures that can be streamed to the user.
data Event arch where
  AnalysisEnd :: PES.EquivalenceStatistics -> TM.NominalDiffTime -> Event arch
  AnalysisStart :: PB.BlockPair arch -> Event arch
  ErrorRaised :: PEE.EquivalenceError -> Event arch
  Warning :: PEE.EquivalenceError -> Event arch
  -- | final top-level result
  DiscoverBlockPair :: BlocksPair arch -> PPa.PatchPair (PB.BlockTarget arch) -> BlockTargetResult -> TM.NominalDiffTime -> Event arch
  ComputedPrecondition :: BlocksPair arch -> TM.NominalDiffTime -> Event arch
  ElfLoaderWarnings :: [DEE.ElfParseError] -> Event arch
  LoadedBinaries :: PLE.LoadedELF arch -> PLE.LoadedELF arch -> Event arch
  -- | Function/block start hints that point to unmapped addresses
  FunctionEntryInvalidHints :: PB.WhichBinaryRepr bin -> [(T.Text, Word64)] -> Event arch
  -- | A list of functions discovered from provided hints that macaw code
  -- discovery was not able to identify by itself
  FunctionsDiscoveredFromHints :: PB.WhichBinaryRepr bin -> [PB.FunctionEntry arch bin] -> Event arch
  HintErrorsCSV :: DLN.NonEmpty PHC.CSVParseError -> Event arch
  HintErrorsJSON :: DLN.NonEmpty PHJ.JSONError -> Event arch
  HintErrorsDWARF :: DLN.NonEmpty PHD.DWARFError -> Event arch
  HintErrorsBSI :: DLN.NonEmpty PHB.JSONError -> Event arch
  -- | A very low-level event generated during the proof construction or evaluation
  --
  -- It records a pair of block addresses and a message that describes the state
  -- of the proof for that block pair.
  --
  -- This is useful for debugging, but probably should not be shown/collected
  -- unless explicitly asked for.
  ProofTraceEvent :: GS.CallStack -> PPa.PatchPairC (PA.ConcreteAddress arch) -> T.Text -> TM.NominalDiffTime -> Event arch
  -- | A low-level trace event that contains a formula that should be displayed
  -- to the user in some structured way, when possible
  --
  -- This has to save enough constraints to allow us to traverse the term
  ProofTraceFormulaEvent :: (sym ~ WE.ExprBuilder t st fs) => GS.CallStack -> PA.ConcreteAddress arch -> PA.ConcreteAddress arch -> sym -> WI.SymExpr sym tp -> TM.NominalDiffTime -> Event arch


  -- | The strongest postcondition verifier has completed with the given status
  StrongestPostOverallResult :: PE.EquivalenceStatus -> TM.NominalDiffTime -> Event arch
  -- | The strongest postcondition verifier discovered an observable difference in behavior (reported as a counterexample)
  StrongestPostObservable :: (PArch.ValidArch arch, WI.IsExprBuilder sym) => PVPN.NodeEntry arch -> PVSC.ObservableCounterexample sym arch -> Event arch
  -- | The strongest postcondition verifier has discovered a desynchronization in the control flow of the programs
  StrongestPostDesync :: (PArch.ValidArch arch) => PVPN.NodeEntry arch -> PVSC.TotalityCounterexample (DMC.ArchAddrWidth arch) -> Event arch
  -- | The strongest postcondition analysis ran out of gas when analyzing the given pair
  GasExhausted :: (PArch.ValidArch arch) => PVPN.GraphNode arch -> Event arch
  -- | Other errors that can occur inside of the strongest postcondition verifier
  StrongestPostMiscError :: (PArch.ValidArch arch) => PVPN.GraphNode arch -> PEE.EquivalenceError -> Event arch
  -- | A recoverable error that occurred during verification
  ErrorEmitted :: PEE.EquivalenceError -> TM.NominalDiffTime -> Event arch

  VisitedNode :: (PArch.ValidArch arch) => PVPN.GraphNode arch -> TM.NominalDiffTime -> Event arch
  SolverEvent :: (sym ~ WE.ExprBuilder t st fs) => PB.BlockPair arch -> SolverProofKind -> SolverResultKind -> PAS.AssumptionSet sym -> WI.Pred sym -> TM.NominalDiffTime -> Event arch

  DomainWidened :: (sym ~ WE.ExprBuilder t st fs) => PB.BlockPair arch -> TM.NominalDiffTime -> Event arch

  InitialDomainFound :: (sym ~ WE.ExprBuilder t st fs) => PB.BlockPair arch -> TM.NominalDiffTime -> Event arch

  DomainAbstraction :: (PArch.ValidArch arch) => PB.BlockPair arch -> TM.NominalDiffTime -> Event arch
  ScopeAbstractionResult :: (sym ~ WE.ExprBuilder t st fs) => PB.BlockPair arch -> PS.ScopedExpr sym tp c -> PS.ScopedExpr sym tp v' -> TM.NominalDiffTime -> Event arch

data SolverResultKind =
    SolverStarted
  | SolverSuccess
  | SolverError
  | SolverFailure
  deriving (Eq, Ord)


data SolverProofKind =
    EquivalenceProof
  | TotalityProof
