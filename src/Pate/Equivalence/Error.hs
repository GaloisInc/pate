{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Pate.Equivalence.Error (
    InnerEquivalenceError(..)
  , InnerSymEquivalenceError(..)
  , pattern InnerSymEquivalenceError
  , SomeExpr(..)
  , printSomeExprTruncated
  , LoadError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , SimpResult(..)
  , SomeInnerError(..)
  , equivalenceError
  , equivalenceErrorFor
  , isRecoverable
  , isTracedWhenWarning
  , loaderError
  , someExpr) where

import qualified Control.Exception as X
import           Data.Maybe ( catMaybes )
import qualified Data.Binary.Get as DB
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as DEE
import           Data.Parameterized.Some ( Some(..) )
import           Data.Typeable ( Typeable, eqT )
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
import Unsafe.Coerce (unsafeCoerce)

data InequivalenceReason =
    InequivalentRegisters
  | InequivalentMemory
  | InvalidCallPair
  | InvalidPostState
  deriving (Eq, Ord, Show)

data InnerSymEquivalenceError sym arch =
  forall tp pre post. RescopingFailure (PAS.AssumptionSet sym) (PS.ScopedExpr sym pre tp) (PS.ScopedExpr sym post tp)
  | AssumedFalse (PAS.AssumptionSet sym) (PAS.AssumptionSet sym)

deriving instance W4.IsExprBuilder sym => Show (InnerSymEquivalenceError sym arch)

pattern InnerSymEquivalenceError :: (sym ~ sym', arch ~ arch', W4.IsExprBuilder sym', PAr.ValidArch arch') => () => InnerSymEquivalenceError sym arch -> InnerEquivalenceError arch'
pattern InnerSymEquivalenceError x <- ((\((InnerSymEquivalenceError_ x)) -> (asAnySymArch x) -> Just x))
  where
    InnerSymEquivalenceError x = InnerSymEquivalenceError_ x

-- FIXME: we can add a more robust test for 'sym' equality, but we need a reference to the actual
-- builder.
asAnySymArch :: forall sym arch sym' arch'. W4.IsExprBuilder sym' => PAr.ValidArch arch' => PAr.ValidArch arch => InnerSymEquivalenceError sym arch -> Maybe (InnerSymEquivalenceError sym' arch')
asAnySymArch x = case eqT @arch @arch' of
  Just CT.Refl -> Just (unsafeCoerce x)
  Nothing -> Nothing

data InnerEquivalenceError arch
  = forall sym. (W4.IsExprBuilder sym) => InnerSymEquivalenceError_ (InnerSymEquivalenceError sym arch)
  | BytesNotConsumed { disassemblyAddr :: PA.ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
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
  | UnsatisfiableEquivalenceCondition (SomeExpr W4.BaseBoolType)
  | InconsistentPatchPairAccess
  | OutOfGas
  | UnsupportedLocation 
  | forall bin. InvalidBlockAddress (PB.ConcreteBlock arch bin)
  | forall bin. MissingBlockAtAddress (MM.ArchSegmentOff arch) [MM.ArchSegmentOff arch] (PBi.WhichBinaryRepr bin) (PB.ConcreteBlock arch bin)
  | UninterpretedInstruction
  | FailedToResolveAddress (MM.MemWord (MM.ArchAddrWidth arch))
  | forall tp. FailedToGroundExpr (SomeExpr tp)
  | OrphanedSingletonAnalysis (PB.FunPair arch)

data SomeExpr tp = forall sym. W4.IsExpr (W4.SymExpr sym) => SomeExpr (W4.SymExpr sym tp)

someExpr :: forall sym tp. W4.IsExpr (W4.SymExpr sym) => sym -> W4.SymExpr sym tp -> SomeExpr tp
someExpr _ e = SomeExpr @_ @sym e

-- Not to be used formally
instance Eq (SomeExpr tp) where
  e1 == e2 = show e1 == show e2

instance Show (SomeExpr tp) where
  show (SomeExpr e) = show (W4.printSymExpr e)

instance PP.Pretty (SomeExpr tp) where
  pretty (SomeExpr e) = W4.printSymExpr e

printSomeExprTruncated ::
  SomeExpr tp ->
  PP.Doc a
printSomeExprTruncated (SomeExpr e) = 
  let ls = lines (show (W4.printSymExpr e))
  in case ls of
    [] -> ""
    [a] -> PP.pretty a
    (a:as) -> PP.pretty a <> ".." <> PP.pretty (last as)


ppInnerError :: (PAr.ValidArch arch) => InnerEquivalenceError arch -> PP.Doc a
ppInnerError e = case e of
  InnerSymEquivalenceError_(RescopingFailure asms src tgt) ->
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
  InnerSymEquivalenceError_(RescopingFailure{}) -> True
  WideningError{} -> True
  NotImplementedYet{} -> True
  MissingRegionOffset{} -> True
  BlockHasNoExit{} -> True
  OrphanedFunctionReturns{} -> True
  CallReturnsToFunctionEntry{} -> True
  OrphanedSingletonAnalysis{} -> True
  UnsatisfiableEquivalenceCondition{} -> True
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

deriving instance (MS.SymArchConstraints arch) => Show (InnerEquivalenceError arch)
instance (Typeable arch, MS.SymArchConstraints arch) => X.Exception (InnerEquivalenceError arch)


data LoadError where
  ElfHeaderParseError :: FilePath -> DB.ByteOffset -> String -> LoadError
  ElfArchitectureMismatch :: FilePath -> FilePath -> LoadError
  UnsupportedArchitecture :: DEE.ElfMachine -> LoadError
  InvalidArchOpts :: [String] -> LoadError
  BadPatchInfo :: FilePath -> PC.PatchDataParseError -> LoadError
  JSONParseError :: FilePath -> PHJ.JSONError -> LoadError
  CSVParseError :: FilePath -> PHC.CSVParseError -> LoadError
  DWARFError :: FilePath -> PHD.DWARFError -> LoadError
  BSIParseError :: FilePath -> PHB.JSONError -> LoadError
  ElfParseError :: DEE.ElfParseError -> LoadError
  ConfigError :: String -> LoadError
deriving instance Show LoadError


data SomeInnerError where
  SomeInnerError :: (PAr.ValidArch arch) => InnerEquivalenceError arch -> SomeInnerError

data EquivalenceError where
  EquivalenceError ::
      { errWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
      , errStackTrace :: Maybe CallStack
      , errEquivError :: Either SomeInnerError LoadError
      } -> EquivalenceError

instance (MS.SymArchConstraints arch) => PP.Pretty (InnerEquivalenceError arch) where
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

equivalenceError :: forall arch. (HasCallStack, PAr.ValidArch arch) => InnerEquivalenceError arch -> EquivalenceError
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Just callStack
  , errEquivError = Left (SomeInnerError err)
  }

equivalenceErrorFor
  :: forall arch bin. (HasCallStack, PAr.ValidArch arch)
  => PBi.WhichBinaryRepr bin
  -> InnerEquivalenceError arch
  -> EquivalenceError
equivalenceErrorFor repr err =
  EquivalenceError { errWhichBinary = Just (Some repr)
                   , errStackTrace = Just callStack
                   , errEquivError = Left (SomeInnerError err)
                   }

instance IsNodeError EquivalenceError where
  propagateErr err = case errEquivError err of
    Left (SomeInnerError InconsistentPatchPairAccess) -> False
    _ -> True