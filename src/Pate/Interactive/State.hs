{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Pate.Interactive.State (
  SourcePair(..),
  EquivalenceTest(..),
  TraceEvent(..),
  Failure(..),
  State,
  emptyState,
  successful,
  indeterminate,
  failure,
  recentEvents,
  originalBinary,
  patchedBinary,
  sources,
  metrics,
  traceEvents,
  ProofTreeNode(..),
  ProofTree(..),
  proofTree,
  activeProofTree,
  addProofTreeNode,
  snapshotProofTree,
  StateRef(..),
  newState
  ) where

import qualified Control.Lens as L
import qualified Data.IORef as IOR
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as DT
import qualified Data.Time as TM
import qualified Graphics.UI.Threepenny as TP
import qualified Language.C as LC
import qualified What4.Expr as WE
import qualified What4.Interface as WI

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Metrics as PM
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT

data SourcePair f = SourcePair { originalSource :: f
                               , patchedSource :: f
                               }
                  deriving (Eq, Ord, Read, Show)

data EquivalenceTest arch where
  EquivalenceTest :: PE.BlocksPair arch -> TM.NominalDiffTime -> EquivalenceTest arch

data Failure arch where
  Failure :: PFI.InequivalenceResult arch -> EquivalenceTest arch -> Failure arch

data ProofTreeNode arch prf tp where
  ProofTreeNode :: PE.BlocksPair arch
                -> PPr.ProofNonceExpr prf tp
                -> TM.NominalDiffTime
                -> ProofTreeNode arch prf tp

data ProofTree arch where
  ProofTree :: ( prf ~ PFI.ProofSym sym arch
               , WI.IsSymExprBuilder sym
               )
            => PT.Sym sym
            -> MapF.MapF (PPr.ProofNonce prf) (ProofTreeNode arch prf)
            -> Map.Map Int (Some (ProofTreeNode arch prf))
            -> ProofTree arch

-- | Trace events that can be generated for debugging purposes
--
-- These are visualized in a separate window. This data type is intended to
-- provide just enough structure to visualize complex terms when desired
-- (ideally lazily)
data TraceEvent where
  TraceText :: DT.Text -> TraceEvent
  TraceFormula :: (sym ~ WE.ExprBuilder t st fs) => sym -> WI.SymExpr sym tp -> TraceEvent

-- | The state tracks verification successes and failures
--
-- The maps are keyed on the address of the original block being checked (that
-- choice is arbitrary and doesn't matter much)
data State arch =
  State { _successful :: Map.Map (PT.ConcreteAddress arch) (EquivalenceTest arch)
        , _indeterminate :: Map.Map (PT.ConcreteAddress arch) (EquivalenceTest arch)
        , _failure :: Map.Map (PT.ConcreteAddress arch) (Failure arch)
        , _recentEvents :: [PE.Event arch]
        -- ^ The N most recent events (most recent first), to be shown in the console
        , _originalBinary :: Maybe (PB.LoadedELF arch, PT.ParsedFunctionMap arch)
        , _patchedBinary :: Maybe (PB.LoadedELF arch, PT.ParsedFunctionMap arch)
        , _sources :: Maybe (SourcePair LC.CTranslUnit)
        , _proofTree :: Maybe (ProofTree arch)
        -- ^ All of the collected proof nodes received from the verifier
        , _activeProofTree :: Maybe (ProofTree arch)
        -- ^ The snapshot of the proof tree displayed to the user
        --
        -- This is only updated at the user's direction so that they don't lose
        -- their place as new data streams in
        , _metrics :: PM.Metrics
        -- ^ Aggregated metrics for display
        , _traceEvents :: Map.Map (PT.ConcreteAddress arch) (Seq.Seq TraceEvent)
        -- ^ Debug trace events indexed by original (super-)block address
        }

$(L.makeLenses 'State)

addProofTreeNode
  :: PE.BlocksPair arch
  -> PFI.SomeProofSym arch tp
  -> TM.NominalDiffTime
  -> Maybe (ProofTree arch)
  -> Maybe (ProofTree arch)
addProofTreeNode blockPair (PFI.SomeProofSym oldSym@(PT.Sym symNonce0 _ _) expr@(PPr.ProofNonceExpr enonce _ _)) tm mpt =
  case mpt of
    Nothing ->
      let proofNode = ProofTreeNode blockPair expr tm
      in Just (ProofTree oldSym
                         (MapF.singleton enonce proofNode)
                         (Map.singleton (asInt enonce) (Some proofNode)))
    Just (ProofTree sym@(PT.Sym symNonce1 _ _) m idx)
      | Just PC.Refl <- PC.testEquality symNonce0 symNonce1 ->
        let proofNode = ProofTreeNode blockPair expr tm
        in Just (ProofTree sym
                           (MapF.insert enonce proofNode m)
                           (Map.insert (asInt enonce) (Some proofNode) idx))
      | otherwise ->
        -- This shouldn't be possible, as we only ever allocate one 'PT.Sym'
        error "Impossible: there should be only one symbolic backend"
  where
    asInt = fromIntegral . PPr.proofNonceValue

snapshotProofTree :: State arch -> State arch
snapshotProofTree s = s { _activeProofTree = _proofTree s }

emptyState :: Maybe (SourcePair LC.CTranslUnit) -> State arch
emptyState ms = State { _successful = Map.empty
                      , _indeterminate = Map.empty
                      , _failure = Map.empty
                      , _recentEvents = []
                      , _originalBinary = Nothing
                      , _patchedBinary = Nothing
                      , _sources = ms
                      , _proofTree = Nothing
                      , _activeProofTree = Nothing
                      , _metrics = PM.emptyMetrics
                      , _traceEvents = Map.empty
                      }

data StateRef arch =
  StateRef { stateRef :: IOR.IORef (State arch)
           -- ^ An IORef with the current state of the visualization
           , stateChangeEvent :: TP.Event ()
           -- ^ The event indicating that the visualization state has changed
           -- and the UI needs to be redrawn appropriately
           , stateChangeEmitter :: () -> IO ()
           -- ^ The IO action to emit the state change event
           , proofChangeEvent :: TP.Event ()
           -- ^ The event indicating that a proof snapshot has been taken and
           -- that the UI should update to reflect it; this is split into a
           -- separate event because we want to give the user more control as to
           -- when the proof is redrawn (so that they don't lose state)
           , proofChangeEmitter :: () -> IO ()
           -- ^ The IO action to emit the proof change event
           }

newState :: Maybe (SourcePair LC.CTranslUnit) -> IO (StateRef arch)
newState ms = do
  r <- IOR.newIORef (emptyState ms)
  (stateChangeEvt, stateChangeEmit) <- TP.newEvent
  (proofSnapshotEvt, proofSnapshotEmit) <- TP.newEvent
  return StateRef { stateRef = r
                  , stateChangeEvent = stateChangeEvt
                  , stateChangeEmitter = stateChangeEmit
                  , proofChangeEvent = proofSnapshotEvt
                  , proofChangeEmitter = proofSnapshotEmit
                  }
