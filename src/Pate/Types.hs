{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Types
  ( PatchPair(..)
  , ConcreteBlock(..)
  , blockSize
  , BlockMapping(..)
  , ConcreteAddress(..)
  , absoluteAddress
  , addressAddOffset
  , concreteFromAbsolute
  , ParsedBlockMap(..)
  , ParsedFunctionMap
  , markEntryPoint

  , WhichBinary(..)
  , RegisterDiff(..)
  , MemOpSpine(..)
  , spineOf
  , ConcreteValue
  , GroundLLVMPointer(..)
  , GroundMemOp(..)
  , SymGroundEvalFn(..)
  , execGroundFnIO
  , MemTraceDiff
  , MemTraceSpine
  , MemOpDiff(..)
  , MacawRegEntry(..)
  , macawRegEntry
  , InnerEquivalenceError(..)
  , EquivalenceError(..)
  , equivalenceError
  --- reporting
  , EquivalenceStatistics(..)
  , equivSuccess
  , EquivalenceResult(..)
  , combineEquivalence
  , ppEquivalenceResult
  , ppEquivalenceStatistics
  , ppBlock
  , ppAbortedResult
  
  
  )
where

import           GHC.Stack

import           Control.Exception

import           Data.Map ( Map )
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import           Data.Sequence (Seq)
import           Data.Typeable
import           Data.Foldable
import           Data.Monoid 
import           Numeric.Natural
import           Numeric

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.MemTraceOps as MT

import qualified What4.Interface as W4
import qualified What4.Symbol as W4S
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G


----------------------------------

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))


markEntryPoint ::
  MM.ArchSegmentOff arch ->
  ParsedBlockMap arch ids ->
  ParsedFunctionMap arch
markEntryPoint segOff blocks = M.singleton segOff (Some blocks) <$ getParsedBlockMap blocks

----------------------------------

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)
deriving instance Show (ConcreteAddress arch)

data PatchPair arch = PatchPair
  { pOrig :: ConcreteBlock arch
  , pPatched :: ConcreteBlock arch
  }

-- | Map from the start of original blocks to patched block addresses
newtype BlockMapping arch = BlockMapping (M.Map (ConcreteAddress arch) (ConcreteAddress arch))


data ConcreteBlock arch =
  ConcreteBlock { concreteAddress :: ConcreteAddress arch
                , concreteBlockSize :: Int
                }

blockSize :: ConcreteBlock arch -> Int
blockSize = concreteBlockSize

absoluteAddress :: (MM.MemWidth (MM.ArchAddrWidth arch)) => ConcreteAddress arch -> MM.MemWord (MM.ArchAddrWidth arch)
absoluteAddress (ConcreteAddress memAddr) = absAddr
  where
    Just absAddr = MM.asAbsoluteAddr memAddr

addressAddOffset :: (MM.MemWidth (MM.ArchAddrWidth arch))
                 => ConcreteAddress arch
                 -> MM.MemWord (MM.ArchAddrWidth arch)
                 -> ConcreteAddress arch
addressAddOffset (ConcreteAddress memAddr) memWord =
  ConcreteAddress (MM.incAddr (fromIntegral memWord) memAddr)

concreteFromAbsolute :: (MM.MemWidth (MM.ArchAddrWidth arch))
                     => MM.MemWord (MM.ArchAddrWidth arch)
                     -> ConcreteAddress arch
concreteFromAbsolute = ConcreteAddress . MM.absoluteAddr

----------------------------------

data GroundLLVMPointer = GroundLLVMPointer
  { ptrWidth :: Natural
  , ptrRegion :: Natural
  , ptrOffset :: Integer
  } deriving (Eq, Ord, Read, Show)

type family ConcreteValue (tp :: CC.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundLLVMPointer

data RegisterDiff arch tp where
  RegisterDiff :: ShowF (MM.ArchReg arch) =>
    { rReg :: MM.ArchReg arch tp
    , rTypeRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , rPre :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostOriginal :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostRewritten :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostEquivalent :: Bool
    } -> RegisterDiff arch tp

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (W4B.ExprBuilder scope solver fs)

execGroundFnIO ::
  SymGroundEvalFn sym -> 
  W4.SymExpr sym tp ->
  IO (W4G.GroundValue tp)
execGroundFnIO (SymGroundEvalFn (W4G.GroundEvalFn fn)) = fn

----------------------------------
data MemOpSpine
  = MemOpSpine MT.MemOpDirection Natural MM.Endianness
  | MergeSpines MemTraceSpine MemTraceSpine

type MemTraceSpine = Seq MemOpSpine

spineOf :: MT.MemTraceImpl sym ptrW -> MemTraceSpine
spineOf = fmap go where
  go (MT.MemOp _addr dir _cond size _val end) = MemOpSpine dir (W4.natValue size) end
  go (MT.MergeOps _cond traceT traceF) = MergeSpines (spineOf traceT) (spineOf traceF)

data GroundMemOp = GroundMemOp
  { gAddress :: GroundLLVMPointer
  , gCondition :: Bool
  , gValue :: GroundLLVMPointer
  } deriving (Eq, Ord, Read, Show)

data MemOpDiff = MemOpDiff
  { mDirection :: MT.MemOpDirection
  , mOpOriginal :: GroundMemOp
  , mOpRewritten :: GroundMemOp
  } deriving (Eq, Ord, Read, Show)

type MemTraceDiff = Seq MemOpDiff

----------------------------------

data MacawRegEntry sym tp where
  MacawRegEntry ::
    { macawRegRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , macawRegValue :: CS.RegValue sym (MS.ToCrucibleType tp)
    } ->
    MacawRegEntry sym tp

macawRegEntry :: CS.RegEntry sym (MS.ToCrucibleType tp) -> MacawRegEntry sym tp
macawRegEntry (CS.RegEntry repr v) = MacawRegEntry repr v

--------------------

data EquivalenceStatistics = EquivalenceStatistics
  { numPairsChecked :: Int
  , numEquivalentPairs :: Int
  , numPairsErrored :: Int
  } deriving (Eq, Ord, Read, Show)

instance Semigroup EquivalenceStatistics where
  EquivalenceStatistics checked total errored <> EquivalenceStatistics checked' total' errored' = EquivalenceStatistics
    (checked + checked')
    (total + total')
    (errored + errored')

instance Monoid EquivalenceStatistics where
  mempty = EquivalenceStatistics 0 0 0


equivSuccess :: EquivalenceStatistics -> Bool
equivSuccess (EquivalenceStatistics checked total errored) = errored == 0 && checked == total

data EquivalenceResult arch
  = Equivalent
  | InequivalentResults MemTraceDiff (MM.RegState (MM.ArchReg arch) (RegisterDiff arch))
  | InequivalentOperations MemTraceSpine MemTraceSpine

combineEquivalence :: Monad m =>
  m (EquivalenceResult arch) ->
  m (EquivalenceResult arch) ->
  m (EquivalenceResult arch)
combineEquivalence act1 act2 = do
  res1 <- act1
  case res1 of
    Equivalent -> act2
    _ -> pure res1

----------------------------------

data WhichBinary = Original | Rewritten deriving (Bounded, Enum, Eq, Ord, Read, Show)

----------------------------------

data InnerEquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
  | AddressOutOfRange { disassemblyAddr :: ConcreteAddress arch }
  | UnsupportedArchitecture
  | InvalidRegisterName String W4S.SolverSymbolError
  | UnsupportedRegisterType (Some CC.TypeRepr)
  | SymbolicExecutionFailed String -- TODO: do something better
  | InconclusiveSAT
  | IllegalIP String (ConcreteAddress arch)
  | BadSolverSymbol String W4S.SolverSymbolError
  | EmptyDisassembly
  | NoUniqueFunctionOwner (IM.Interval (ConcreteAddress arch)) [MM.ArchSegmentOff arch]
  | StrangeBlockAddress (MM.ArchSegmentOff arch)
  -- starting address of the block, then a starting and ending address bracketing a range of undiscovered instructions
  | UndiscoveredBlockPart (ConcreteAddress arch) (ConcreteAddress arch) (ConcreteAddress arch)
  | NonConcreteParsedBlockAddress (MM.ArchSegmentOff arch)
  | BlockExceedsItsSegment (MM.ArchSegmentOff arch) (MM.ArchAddrWord arch)
  | BlockEndsMidInstruction
  | PrunedBlockIsEmpty
  | EquivCheckFailure String -- generic error
deriving instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (InnerEquivalenceError arch)


data EquivalenceError arch =
  EquivalenceError
    { errWhichBinary :: Maybe WhichBinary
    , errStackTrace :: Maybe CallStack
    , errEquivError :: InnerEquivalenceError arch
    }
instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (EquivalenceError arch) where
  show e = unlines $ catMaybes $
    [ fmap (\b -> "For " ++ show b ++ " binary") (errWhichBinary e)
    , fmap (\s -> "At " ++ prettyCallStack s) (errStackTrace e)
    , Just (show (errEquivError e))
    ]

instance (Typeable arch, MM.MemWidth (MM.ArchAddrWidth arch)) => Exception (EquivalenceError arch)

equivalenceError :: InnerEquivalenceError arch -> EquivalenceError arch
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Nothing
  , errEquivError = err
  }
----------------------------------

ppEquivalenceStatistics :: EquivalenceStatistics -> String
ppEquivalenceStatistics (EquivalenceStatistics checked equiv err) = unlines
  [ "Summary of checking " ++ show checked ++ " pairs:"
  , "\t" ++ show equiv ++ " equivalent"
  , "\t" ++ show (checked-equiv-err) ++ " inequivalent"
  , "\t" ++ show err ++ " skipped due to errors"
  ]

ppEquivalenceResult ::
  MM.MemWidth (MM.ArchAddrWidth arch) =>
  ShowF (MM.ArchReg arch) =>
  Either (EquivalenceError arch) (EquivalenceResult arch) -> String
ppEquivalenceResult (Right Equivalent) = "✓\n"
ppEquivalenceResult (Right (InequivalentResults traceDiff regDiffs)) = "x\n" ++ ppPreRegs regDiffs ++ ppMemTraceDiff traceDiff ++ ppDiffs regDiffs
ppEquivalenceResult (Right (InequivalentOperations trace trace')) = concat
  [ "x\n\tMismatched memory operations:\n\t\t"
  , ppMemTraceSpine trace
  , " (original) vs.\n\t\t"
  , ppMemTraceSpine trace'
  , " (rewritten)\n"
  ]
ppEquivalenceResult (Left err) = "-\n\t" ++ show err ++ "\n" -- TODO: pretty-print the error

ppMemTraceDiff :: MemTraceDiff -> String
ppMemTraceDiff diffs = "\tTrace of memory operations:\n" ++ concatMap ppMemOpDiff (toList diffs)

ppMemOpDiff :: MemOpDiff -> String
ppMemOpDiff diff
  =  "\t\t" ++ ppDirectionVerb (mDirection diff) ++ " "
  ++ ppGroundMemOp (mDirection diff) (mOpOriginal diff)
  ++ (if mOpOriginal diff == mOpRewritten diff
      then ""
      else " (original) vs. " ++ ppGroundMemOp (mDirection diff) (mOpRewritten diff) ++ " (rewritten)"
     )
  ++ "\n"

ppGroundMemOp :: MT.MemOpDirection -> GroundMemOp -> String
ppGroundMemOp dir op
  =  ppLLVMPointer (gValue op)
  ++ " " ++ ppDirectionPreposition dir ++ " "
  ++ ppLLVMPointer (gAddress op)
  ++ if gCondition op
     then ""
     else " (skipped)"

ppDirectionVerb :: MT.MemOpDirection -> String
ppDirectionVerb MT.Read = "read"
ppDirectionVerb MT.Write = "wrote"

ppDirectionPreposition :: MT.MemOpDirection -> String
ppDirectionPreposition MT.Read = "from"
ppDirectionPreposition MT.Write = "to"

ppMemTraceSpine :: MemTraceSpine -> String
ppMemTraceSpine = unwords . map ppMemOpSpine . toList

ppMemOpSpine :: MemOpSpine -> String
ppMemOpSpine (MemOpSpine dir size end) = concat
  [ take 1 (ppDirectionVerb dir)
  , ppEndianness end
  , show size
  ]
ppMemOpSpine (MergeSpines spineT spineF) = concat
  [ "("
  , ppMemTraceSpine spineT
  , "/"
  , ppMemTraceSpine spineF
  , ")"
  ]

ppEndianness :: MM.Endianness -> String
ppEndianness MM.BigEndian = "→"
ppEndianness MM.LittleEndian = "←"

ppPreRegs ::
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
  -> String
ppPreRegs diffs = "\tInitial registers of a counterexample:\n" ++ case TF.foldMapF ppPreReg diffs of
  (Sum 0, s) -> s
  (Sum n, s) -> s ++ "\t\t(and " ++ show n ++ " other all-zero slots)\n"

ppPreReg ::
  RegisterDiff arch tp ->
  (Sum Int, String)
ppPreReg diff = case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> case rPre diff of
    GroundLLVMPointer _ 0 0 -> (1, "")
    _ -> (0, ppSlot diff ++ ppLLVMPointer (rPre diff) ++ "\n")
  _ -> (0, ppSlot diff ++ "unsupported register type in precondition pretty-printer\n")

ppDiffs ::
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch) ->
  String
ppDiffs diffs = "\tMismatched resulting registers:\n" ++ TF.foldMapF ppDiff diffs

ppDiff ::
  RegisterDiff arch tp ->
  String
ppDiff diff | rPostEquivalent diff = ""
ppDiff diff = ppSlot diff ++ case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> ""
    ++ ppLLVMPointer (rPostOriginal diff)
    ++ " (original) vs. "
    ++ ppLLVMPointer (rPostRewritten diff)
    ++ " (rewritten)\n"
  _ -> "unsupported register type in postcondition comparison pretty-printer\n"

ppSlot ::
  RegisterDiff arch tp
  -> String
ppSlot (RegisterDiff { rReg = reg })  = "\t\tslot " ++ (pad 4 . showF) reg ++ ": "

ppLLVMPointer :: GroundLLVMPointer -> String
ppLLVMPointer (GroundLLVMPointer bitWidth reg off) = ""
  ++ pad 3 (show reg)
  ++ "+0x"
  ++ padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch -> String
ppBlock b = ""
  -- 100k oughta be enough for anybody
  ++ pad 6 (show (blockSize b))
  ++ " bytes at "
  ++ show (absoluteAddress (concreteAddress b))

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"


padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

pad :: Int -> String -> String
pad = padWith ' '
