{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Interactive.State (
  EquivalenceTest(..),
  Failure(..),
  State,
  emptyState,
  successful,
  indeterminate,
  failure,
  recentEvents,
  originalBinary,
  patchedBinary
  ) where

import qualified Control.Lens as L
import qualified Data.Map.Strict as Map
import qualified Data.Time as TM

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Types as PT

data EquivalenceTest arch where
  EquivalenceTest :: PE.Blocks arch -> PE.Blocks arch -> TM.NominalDiffTime -> EquivalenceTest arch

data Failure arch where
  Failure :: PT.InequivalenceResult arch -> EquivalenceTest arch -> Failure arch

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
        }

$(L.makeLenses 'State)

emptyState :: State arch
emptyState = State { _successful = Map.empty
                   , _indeterminate = Map.empty
                   , _failure = Map.empty
                   , _recentEvents = []
                   , _originalBinary = Nothing
                   , _patchedBinary = Nothing
                   }
