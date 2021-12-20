{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Pate.Equivalence.Error (
    InnerEquivalenceError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , equivalenceError
  , equivalenceErrorFor
  ) where

import qualified Control.Exception as X
import           Data.Maybe ( catMaybes )
import           Data.Parameterized.Some ( Some(..) )
import           Data.Typeable ( Typeable )
import           GHC.Stack ( HasCallStack, CallStack, prettyCallStack, callStack )
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Types as CT

import qualified Pate.Arch as PAr
import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.PatchPair as PPa

data InequivalenceReason =
    InequivalentRegisters
  | InequivalentMemory
  | InvalidCallPair
  | InvalidPostState
  deriving (Eq, Ord, Show)

data InnerEquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: PA.ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
  | UnsupportedArchitecture
  | UnsupportedRegisterType (Some CT.TypeRepr)
  | SymbolicExecutionFailed String -- TODO: do something better
  | InconclusiveSAT
  | UnknownFunctionEntry (PA.ConcreteAddress arch)
  | LookupNotAtFunctionStart CallStack (PA.ConcreteAddress arch)
  -- starting address of the block, then a starting and ending address bracketing a range of undiscovered instructions
  | UndiscoveredBlockPart (PA.ConcreteAddress arch) (PA.ConcreteAddress arch) (PA.ConcreteAddress arch)
  | BlockExceedsItsSegment (MM.ArchSegmentOff arch) (MM.ArchAddrWord arch)
  | BlockEndsMidInstruction
  | BlockStartsEarly (MM.ArchAddrWord arch) (MM.ArchAddrWord arch)
  | PrunedBlockIsEmpty
  | MemOpConditionMismatch
  | UnexpectedBlockKind String
  | UnexpectedMultipleEntries [MM.ArchSegmentOff arch] [MM.ArchSegmentOff arch]
  | forall ids. InvalidBlockTerminal (MD.ParsedTermStmt arch ids)
  | MissingPatchPairResult (PPa.BlockPair arch)
  | EquivCheckFailure String -- generic error
  | ImpossibleEquivalence
  | AssumedFalse
  | BlockExitMismatch
  | InvalidSMTModel
  | MismatchedAssumptionsPanic
  | UnexpectedNonBoundVar
  | UnsatisfiableAssumptions
  | MissingCrucibleGlobals
  | UnexpectedUnverifiedTriple
  | MissingTOCEntry (MM.ArchSegmentOff arch)
  | BlockEndClassificationFailure
  | InvalidCallTarget (PA.ConcreteAddress arch) (EquivalenceError arch)
  | IncompatibleDomainPolarities
  | forall tp. UnsupportedGroundType (W4.BaseTypeRepr tp)
  | InconsistentSimplificationResult String String
  | UnhandledLoop
  | MissingExpectedEquivalentFunction (PA.ConcreteAddress arch)

deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)
instance (Typeable arch, MS.SymArchConstraints arch) => X.Exception (InnerEquivalenceError arch)

data EquivalenceError arch where
  EquivalenceError ::
    PAr.ValidArch arch =>
      { errWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
      , errStackTrace :: Maybe CallStack
      , errEquivError :: InnerEquivalenceError arch
      } -> EquivalenceError arch

instance Show (EquivalenceError arch) where
  show e@(EquivalenceError{}) = unlines $ catMaybes $
    [ fmap (\(Some b) -> "For " ++ show b ++ " binary") (errWhichBinary e)
    , fmap (\s -> "At " ++ prettyCallStack s) (errStackTrace e)
    , Just (show (errEquivError e))
    ]

instance (Typeable arch, MS.SymArchConstraints arch) => X.Exception (EquivalenceError arch)

equivalenceError :: (HasCallStack, PAr.ValidArch arch) => InnerEquivalenceError arch -> EquivalenceError arch
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Just callStack
  , errEquivError = err
  }

equivalenceErrorFor
  :: (HasCallStack, PAr.ValidArch arch)
  => PBi.WhichBinaryRepr bin
  -> InnerEquivalenceError arch
  -> EquivalenceError arch
equivalenceErrorFor repr err =
  EquivalenceError { errWhichBinary = Just (Some repr)
                   , errStackTrace = Just callStack
                   , errEquivError = err
                   }
