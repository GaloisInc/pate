{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}

module Pate.Equivalence.Error (
    InnerEquivalenceError(..)
  , LoadError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , SimpResult(..)
  , equivalenceError
  , equivalenceErrorFor
  , isRecoverable
  , isTracedWhenWarning
  , loaderError
  ) where

import qualified Control.Exception as X
import           Data.Maybe ( catMaybes )
import qualified Data.Binary.Get as DB
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as DEE
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
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Config as PC
import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.SimState as PS
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.DWARF as PHD
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Hints.BSI as PHB
import           Pate.TraceTree

data InequivalenceReason =
    InequivalentRegisters
  | InequivalentMemory
  | InvalidCallPair
  | InvalidPostState
  deriving (Eq, Ord, Show)

data InnerEquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: PA.ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
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
  | MissingPatchPairResult (PB.BlockPair arch)
  | EquivCheckFailure String -- generic error
  | ImpossibleEquivalence
  | forall sym. W4.IsExpr (W4.SymExpr sym) => AssumedFalse (PAS.AssumptionSet sym) (PAS.AssumptionSet sym)
  | BlockExitMismatch
  | InvalidSMTModel
  | MismatchedAssumptionsPanic
  | UnexpectedNonBoundVar
  | UnsatisfiableAssumptions
  | MissingCrucibleGlobals
  | UnexpectedUnverifiedTriple
  | MissingTOCEntry (MM.ArchSegmentOff arch)
  | BlockEndClassificationFailure
  | InvalidCallTarget (PA.ConcreteAddress arch) EquivalenceError
  | IncompatibleDomainPolarities
  | forall tp. UnsupportedGroundType (W4.BaseTypeRepr tp)
  | InconsistentSimplificationResult SimpResult
  | UnhandledLoop
  | MissingExpectedEquivalentFunction (PA.ConcreteAddress arch)
  | SolverStackMisalignment
  | LoaderFailure String
  | WideningError String
  | ObservabilityError String
  | ObservableDifferenceFound -- only raised as an informative warning
  | TotalityError String
  | forall sym tp pre post. W4.IsExpr (W4.SymExpr sym) => RescopingFailure (PAS.AssumptionSet sym) (PS.ScopedExpr sym pre tp) (PS.ScopedExpr sym post tp)
  | UnknownPLTStub BS.ByteString
  | NotImplementedYet String
  | UnexpectedTailCallEntry (PB.FunPair arch)
  | forall w. MissingRegionOffset Int (MM.MemWord w)
  | BlockHasNoExit (PB.BlockPair arch)
  | CallReturnsToFunctionEntry (PB.BlockPair arch)
  | NonTotalBlockExits (PB.BlockPair arch)
  | forall bin. MissingParsedBlockEntry String (PB.ConcreteBlock arch bin)
  | OrphanedFunctionReturns
  | MissingDomainForBlock (PB.BlockPair arch)
  | MissingDomainForFun (PB.FunPair arch)
  | SkippedInequivalentBlocks (PB.BlockPair arch)
  | SymbolicExecutionError String

ppInnerError :: PAr.ValidArch arch => InnerEquivalenceError arch -> PP.Doc a
ppInnerError e = case e of
  RescopingFailure asms src tgt ->
    PP.vsep
      [ "Unable to rescope:"
      , PP.pretty asms
      , "Source Expression"
      , PP.pretty src
      , "Target Expression"
      , PP.pretty tgt
      ]
  _ -> PP.viaShow e

-- | Roughly categorizing how catastrophic an error is to the soundness of the verifier
isRecoverable' :: InnerEquivalenceError arch -> Bool
isRecoverable' e = case e of
  InconsistentSimplificationResult{} -> True
  RescopingFailure{} -> True
  WideningError{} -> True
  NotImplementedYet{} -> True
  MissingRegionOffset{} -> True
  BlockHasNoExit{} -> True
  OrphanedFunctionReturns{} -> True
  CallReturnsToFunctionEntry{} -> True
  _ -> False

-- | When an error is raised as a warning, this determines if it should be displayed
-- in the trace tree
isTracedWhenWarning' :: InnerEquivalenceError arch -> Bool
isTracedWhenWarning' e = case e of
  UnknownPLTStub{} -> False
  _ -> True

isTracedWhenWarning :: EquivalenceError -> Bool
isTracedWhenWarning err = case errEquivError err of
  Left (SomeInnerError innerErr) -> isTracedWhenWarning' innerErr
  _ -> True

isRecoverable :: EquivalenceError -> Bool
isRecoverable err = case errEquivError err of
  Left (SomeInnerError innerErr) -> isRecoverable' innerErr
  _ -> False

data SimpResult = forall sym tp. W4.IsExpr (W4.SymExpr sym) =>
  SimpResult (Proxy sym) (W4.SymExpr sym tp) (W4.SymExpr sym tp)

instance PP.Pretty SimpResult where
  pretty (SimpResult _ e1 e2) = PP.vsep [W4.printSymExpr e1, W4.printSymExpr e2]

instance Show SimpResult where
  show r = show (PP.pretty r)

deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)
instance (Typeable arch, MS.SymArchConstraints arch) => X.Exception (InnerEquivalenceError arch)


data LoadError where
  ElfHeaderParseError :: FilePath -> DB.ByteOffset -> String -> LoadError
  ElfArchitectureMismatch :: FilePath -> FilePath -> LoadError
  UnsupportedArchitecture :: DEE.ElfMachine -> LoadError
  BadPatchInfo :: FilePath -> PC.PatchDataParseError -> LoadError
  JSONParseError :: FilePath -> PHJ.JSONError -> LoadError
  CSVParseError :: FilePath -> PHC.CSVParseError -> LoadError
  DWARFError :: FilePath -> PHD.DWARFError -> LoadError
  BSIParseError :: FilePath -> PHB.JSONError -> LoadError
  ElfParseError :: DEE.ElfParseError -> LoadError
  ConfigError :: String -> LoadError
deriving instance Show LoadError


data SomeInnerError where
  SomeInnerError :: PAr.ValidArch arch => InnerEquivalenceError arch -> SomeInnerError

data EquivalenceError where
  EquivalenceError ::
      { errWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
      , errStackTrace :: Maybe CallStack
      , errEquivError :: Either SomeInnerError LoadError
      } -> EquivalenceError

instance MS.SymArchConstraints arch => PP.Pretty (InnerEquivalenceError arch) where
  pretty = PP.viaShow


ppEitherInnerError :: Either SomeInnerError LoadError -> PP.Doc a
ppEitherInnerError (Left (SomeInnerError e)) = ppInnerError e
ppEitherInnerError (Right e) = PP.pretty (show e)

instance PP.Pretty EquivalenceError where
  pretty e@(EquivalenceError{}) = PP.vsep $ catMaybes $
    [ fmap (\(Some b) -> "For " <+> PP.pretty (show b) <+> " binary") (errWhichBinary e)
    , fmap (\s -> "At " <+> PP.pretty (prettyCallStack s)) (errStackTrace e)
    , Just (ppEitherInnerError (errEquivError e))
    ]

instance Show EquivalenceError where
  show e = show (PP.pretty e)

instance X.Exception EquivalenceError

loaderError :: HasCallStack => LoadError -> EquivalenceError
loaderError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Just callStack
  , errEquivError = Right err
  }

equivalenceError :: (HasCallStack, PAr.ValidArch arch) => InnerEquivalenceError arch -> EquivalenceError
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Just callStack
  , errEquivError = Left (SomeInnerError err)
  }

equivalenceErrorFor
  :: (HasCallStack, PAr.ValidArch arch)
  => PBi.WhichBinaryRepr bin
  -> InnerEquivalenceError arch
  -> EquivalenceError
equivalenceErrorFor repr err =
  EquivalenceError { errWhichBinary = Just (Some repr)
                   , errStackTrace = Just callStack
                   , errEquivError = Left (SomeInnerError err)
                   }

instance IsNodeError EquivalenceError where
  propagateErr _ = True
