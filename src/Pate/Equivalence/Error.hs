{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings   #-}

module Pate.Equivalence.Error (
    InnerEquivalenceError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , SimpResult(..)
  , equivalenceError
  , equivalenceErrorFor
  , isRecoverable
  ) where

import qualified Control.Exception as X
import           Data.Maybe ( catMaybes )
import           Data.Parameterized.Some ( Some(..) )
import           Data.Typeable ( Typeable )
import           Data.Proxy
import           GHC.Stack ( HasCallStack, CallStack, prettyCallStack, callStack )
import qualified What4.Interface as W4

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Types as CT

import qualified Pate.Arch as PAr
import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS

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
  | UnexpectedStackValue (PA.ConcreteAddress arch)
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
  | forall sym v. W4.IsExpr (W4.SymExpr sym) => AssumedFalse (PS.AssumptionSet sym v) (PS.AssumptionSet sym v)
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
  | InconsistentSimplificationResult SimpResult
  | UnhandledLoop
  | MissingExpectedEquivalentFunction (PA.ConcreteAddress arch)
  | SolverStackMisalignment
  | LoaderFailure String

-- | Roughly categorizing how catastrophic an error is to the soundness of the verifier
isRecoverable :: InnerEquivalenceError arch -> Bool
isRecoverable e = case e of
  InconsistentSimplificationResult{} -> True
  _ -> False

data SimpResult = forall sym tp. W4.IsExpr (W4.SymExpr sym) =>
  SimpResult (Proxy sym) (W4.SymExpr sym tp) (W4.SymExpr sym tp)

instance PP.Pretty SimpResult where
  pretty (SimpResult _ e1 e2) = W4.printSymExpr e1 <+> W4.printSymExpr e2

instance Show SimpResult where
  show r = show (PP.pretty r)

deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)
instance (Typeable arch, MS.SymArchConstraints arch) => X.Exception (InnerEquivalenceError arch)

data EquivalenceError arch where
  EquivalenceError ::
    PAr.ValidArch arch =>
      { errWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
      , errStackTrace :: Maybe CallStack
      , errEquivError :: InnerEquivalenceError arch
      } -> EquivalenceError arch

instance MS.SymArchConstraints arch => PP.Pretty (InnerEquivalenceError arch) where
  pretty = PP.viaShow

instance PP.Pretty (EquivalenceError arch) where
  pretty e@(EquivalenceError{}) = PP.vsep $ catMaybes $
    [ fmap (\(Some b) -> "For " <+> PP.pretty (show b) <+> " binary") (errWhichBinary e)
    , fmap (\s -> "At " <+> PP.pretty (prettyCallStack s)) (errStackTrace e)
    , Just (PP.pretty (errEquivError e))
    ]

instance Show (EquivalenceError arch) where
  show e = show (PP.pretty e)

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
