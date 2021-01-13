{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Types
  ( DiscoveryConfig(..)
  , defaultDiscoveryCfg
  , PatchPair(..)
  , ExprMappable(..)
  , ConcreteBlock(..)
  , blockMemAddr
  , BlockMapping(..)
  , BlockTarget(..)
  , ConcreteAddress(..)
  , BlockEntryKind(..)
  , absoluteAddress
  , addressAddOffset
  , concreteFromAbsolute
  , ParsedBlockMap(..)
  , ParsedFunctionMap
  , markEntryPoint
  , type WhichBinary
  , KnownBinary
  , Original
  , Patched
  , WhichBinaryRepr(..)
  , RegisterDiff(..)
  , ConcreteValue
  , GroundBV(..)
  , mkGroundBV
  , groundBVAsPointer
  , GroundLLVMPointer(..)
  , GroundMemOp(..)
  , gValue
  , SymGroundEvalFn(..)
  , execGroundFnIO
  , MemTraceDiff
  , MemOpDiff(..)
  , MacawRegEntry(..)
  , macawRegEntry
  , InnerEquivalenceError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , equivalenceError
  , ExitCaseDiff
  --- register helpers
  , RegisterCase(..)
  , registerCase
  , zipRegStates
  --- reporting
  , EquivalenceStatistics(..)
  , equivSuccess
  , InequivalenceResult(..)
  , ppEquivalenceStatistics
  , ppBlock
  , ppLLVMPointer
  , showModelForExpr
  , mapExprPtr
  , freshPtr
  )
where

import           GHC.Stack

import           Control.Exception
import           Control.Lens hiding ( op, pre )
import           Control.Monad.Except

import qualified Data.BitVector.Sized as BVS
import           Data.Map ( Map )
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Typeable
import           Numeric.Natural
import           Numeric

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS

import qualified What4.Partial as PE
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G

import qualified Pate.Memory.MemTrace as MT
import           What4.ExprHelpers

----------------------------------
-- Verification configuration
data DiscoveryConfig =
  DiscoveryConfig
    { cfgPairMain :: Bool
    -- ^ start by pairing the entry points of the binaries
    , cfgDiscoverFuns :: Bool
    -- ^ discover additional functions pairs during analysis
    }

defaultDiscoveryCfg :: DiscoveryConfig
defaultDiscoveryCfg = DiscoveryConfig True True


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
  { pOrig :: ConcreteBlock arch 'Original
  , pPatched :: ConcreteBlock arch 'Patched
  }
  deriving (Eq, Ord)

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (PatchPair arch) where
  show (PatchPair blk1 blk2) = ppBlock blk1 ++ " vs. " ++ ppBlock blk2


data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

-- | Map from the start of original blocks to patched block addresses
newtype BlockMapping arch = BlockMapping (M.Map (ConcreteAddress arch) (ConcreteAddress arch))


-- | The way this block is entered dictates the initial equivalence relation we can assume
data BlockEntryKind arch =
    BlockEntryInitFunction
    -- ^ block starts a new function
  | BlockEntryPostFunction
    -- ^ block is an intermediate point in a function, after a function call
  | BlockEntryPostArch
    -- ^ block is an intermediate point in a function, after an arch function call
  | BlockEntryJump
    -- ^ block was entered by an arbitrary jump
    -- problems
  deriving (Eq, Ord, Show)

data ConcreteBlock arch (bin :: WhichBinary) =
  ConcreteBlock { concreteAddress :: ConcreteAddress arch
                , concreteBlockEntry :: BlockEntryKind arch
                , blockBinRepr :: WhichBinaryRepr bin
                }

blockMemAddr :: ConcreteBlock arch bin -> MM.MemAddr (MM.ArchAddrWidth arch)
blockMemAddr (ConcreteBlock (ConcreteAddress addr) _ _) = addr

instance TestEquality (ConcreteBlock arch) where
  testEquality (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    case testEquality binrepr1 binrepr2 of
      Just Refl | addr1 == addr2 && entry1 == entry2 -> Just Refl
      _ -> Nothing

instance Eq (ConcreteBlock arch bin) where
  blk1 == blk2 | Just Refl <- testEquality blk1 blk2 = True
  _ == _ = False

instance OrdF (ConcreteBlock arch) where
  compareF (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    lexCompareF binrepr1 binrepr2 $ fromOrdering $
      compare addr1 addr2 <>
      compare entry1 entry2

instance Ord (ConcreteBlock arch bin) where
  compare blk1 blk2 = toOrdering $ compareF blk1 blk2

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (ConcreteBlock arch bin) where
  show blk = ppBlock blk

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> String
ppBlock b = show (absoluteAddress (concreteAddress b))

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

data GroundBV n where
  GroundBV :: W4.NatRepr n -> BVS.BV n -> GroundBV n
  GroundLLVMPointer :: GroundLLVMPointer n -> GroundBV n
  deriving Eq

instance Show (GroundBV n) where
  show = ppGroundBV

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

ppGroundBV :: GroundBV w -> String
ppGroundBV gbv = case gbv of
  GroundBV w bv -> BVS.ppHex w bv
  GroundLLVMPointer ptr -> ppLLVMPointer ptr

ppLLVMPointer :: GroundLLVMPointer w -> String
ppLLVMPointer (GroundLLVMPointerC bitWidthRepr reg offBV) = concat
  [ pad 3 (show reg)
  , "+0x"
  , padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")
  ]
  where
    off = BVS.asUnsigned offBV
    bitWidth = W4.natValue bitWidthRepr

groundBVWidth :: GroundBV n -> W4.NatRepr n
groundBVWidth gbv = case gbv of
  GroundBV nr _ -> nr
  GroundLLVMPointer ptr -> ptrWidth ptr

instance TestEquality GroundBV where
  testEquality bv bv' = case testEquality (groundBVWidth bv) (groundBVWidth bv') of
    Just Refl | bv == bv' -> Just Refl
    _ -> Nothing

instance OrdF GroundBV where
  compareF (GroundBV w bv) (GroundBV w' bv') =
    lexCompareF w w' $ fromOrdering $ compare bv bv'
  compareF (GroundLLVMPointer ptr) (GroundLLVMPointer ptr') = compareF ptr ptr'
  compareF (GroundBV _ _) _ = LTF
  compareF (GroundLLVMPointer _) _ = GTF

instance Ord (GroundBV n) where
  compare bv bv' = toOrdering (compareF bv bv')

data GroundLLVMPointer n where
  GroundLLVMPointerC ::
      { ptrWidth :: W4.NatRepr n
      , ptrRegion :: Natural
      , ptrOffset :: BVS.BV n
      } -> GroundLLVMPointer n
  deriving Eq

instance TestEquality GroundLLVMPointer where
  testEquality ptr ptr'
    | Just Refl <- testEquality (ptrWidth ptr) (ptrWidth ptr')
    , ptr == ptr'
    = Just Refl
  testEquality _ _ = Nothing


instance OrdF GroundLLVMPointer where
  compareF (GroundLLVMPointerC w reg off) (GroundLLVMPointerC w' reg' off') =
    lexCompareF w w' $ joinOrderingF (fromOrdering $ compare reg reg') (fromOrdering $ compare off off')

instance Show (GroundLLVMPointer n) where
  show ptr = ppLLVMPointer ptr

mkGroundBV :: forall n.
  W4.NatRepr n ->
  Natural ->
  BVS.BV n ->
  GroundBV n
mkGroundBV nr reg bv = case reg > 0 of
 True -> GroundLLVMPointer $ GroundLLVMPointerC nr reg bv
 False -> GroundBV nr bv

groundBVAsPointer :: GroundBV n -> GroundLLVMPointer n
groundBVAsPointer gbv = case gbv of
  GroundLLVMPointer ptr -> ptr
  GroundBV w bv -> GroundLLVMPointerC w 0 bv

type family ConcreteValue (tp :: CC.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundBV w
type instance ConcreteValue (CC.MaybeType (CLM.LLVMPointerType w)) = Maybe (GroundBV w)

data RegisterDiff arch tp where
  RegisterDiff :: ShowF (MM.ArchReg arch) =>
    { rReg :: MM.ArchReg arch tp
    , rTypeRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , rPreOriginal :: ConcreteValue (MS.ToCrucibleType tp)
    , rPrePatched :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostOriginal :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostPatched :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostEquivalent :: Bool
    , rDiffDescription :: String
    } -> RegisterDiff arch tp

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (W4B.ExprBuilder scope solver fs)

execGroundFnIO ::
  forall sym tp.
  SymGroundEvalFn sym -> 
  W4.SymExpr sym tp ->
  IO (W4G.GroundValue tp)
execGroundFnIO (SymGroundEvalFn (W4G.GroundEvalFn fn)) = fn

----------------------------------
data GroundMemOp arch where
  GroundMemOp :: forall arch w.
    { gAddress :: GroundLLVMPointer (MM.ArchAddrWidth arch)
    , gCondition :: Bool
    , gValue_ :: GroundBV w
    } -> GroundMemOp arch

gValue :: GroundMemOp arch -> Some GroundBV
gValue (GroundMemOp { gValue_ = v}) = Some v

instance Eq (GroundMemOp arch) where
  (GroundMemOp addr cond v) == (GroundMemOp addr' cond' v')
    | Just Refl <- testEquality addr addr'
    , Just Refl <- testEquality v v'
    = cond == cond'
  _ == _ = False
      
instance Ord (GroundMemOp arch) where
  compare (GroundMemOp addr cond v) (GroundMemOp addr' cond' v') =
    case compare cond cond' of
      LT -> LT
      GT -> GT
      EQ -> toOrdering $ lexCompareF addr addr' $ compareF v v'

deriving instance Show (GroundMemOp arch)

data MemOpDiff arch = MemOpDiff
  { mIsRead :: Bool
  , mOpOriginal :: GroundMemOp arch
  , mOpRewritten :: GroundMemOp arch
  , mIsValid :: Bool
  , mDesc :: String
  } deriving (Eq, Ord, Show)

type MemTraceDiff arch = [MemOpDiff arch]

----------------------------------

data MacawRegEntry sym tp where
  MacawRegEntry ::
    { macawRegRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , macawRegValue :: CS.RegValue sym (MS.ToCrucibleType tp)
    } ->
    MacawRegEntry sym tp       




instance CC.ShowF (W4.SymExpr sym) => Show (MacawRegEntry sym tp) where
  show (MacawRegEntry repr v) = case repr of
    CLM.LLVMPointerRepr{} | CLM.LLVMPointer rg bv <- v -> CC.showF rg ++ ":" ++ CC.showF bv
    _ -> "macawRegEntry: unsupported"

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

data InequivalenceReason =
    InequivalentRegisters
  | InequivalentMemory
  | InvalidCallPair
  | InvalidPostState
  | PostRelationUnsat
  deriving (Eq, Ord, Show)

type ExitCaseDiff = (MS.MacawBlockEndCase, MS.MacawBlockEndCase)
type ReturnAddrDiff arch = (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch)), (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch))))

data InequivalenceResult arch =
  InequivalentResults
    { diffMem :: MemTraceDiff arch
    , diffExit :: ExitCaseDiff
    , diffRegs :: MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
    , diffRetAddr :: ReturnAddrDiff arch
    , diffReason :: InequivalenceReason
    }



instance Show (InequivalenceResult arch) where
  show _ = "InequivalenceResult"

----------------------------------

data WhichBinary = Original | Patched deriving (Bounded, Enum, Eq, Ord, Read, Show)

type Original = 'Original
type Patched = 'Patched

data WhichBinaryRepr (bin :: WhichBinary) where
  OriginalRepr :: WhichBinaryRepr 'Original
  PatchedRepr :: WhichBinaryRepr 'Patched

instance TestEquality WhichBinaryRepr where
  testEquality repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> Just Refl
    (PatchedRepr, PatchedRepr) -> Just Refl
    _ -> Nothing

instance OrdF WhichBinaryRepr where
  compareF repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> EQF
    (PatchedRepr, PatchedRepr) -> EQF
    (OriginalRepr, PatchedRepr) -> LTF
    (PatchedRepr, OriginalRepr) -> GTF

instance Show (WhichBinaryRepr bin) where
  show OriginalRepr = "Original"
  show PatchedRepr = "Patched"

instance KnownRepr WhichBinaryRepr Original where
  knownRepr = OriginalRepr

instance KnownRepr WhichBinaryRepr Patched where
  knownRepr = PatchedRepr

type KnownBinary (bin :: WhichBinary) = KnownRepr WhichBinaryRepr bin

----------------------------------
-- Register helpers

-- | Helper for doing a case-analysis on registers
data RegisterCase arch tp where
  -- | instruction pointer
  RegIP :: RegisterCase arch (MM.BVType (MM.ArchAddrWidth arch))
  -- | stack pointer
  RegSP :: RegisterCase arch (MM.BVType (MM.ArchAddrWidth arch))
  -- | non-specific GPR
  RegG :: RegisterCase arch tp

registerCase ::
  forall arch tp.
  MM.RegisterInfo (MM.ArchReg arch) =>
  MM.ArchReg arch tp ->
  RegisterCase arch tp
registerCase r = case testEquality r (MM.ip_reg @(MM.ArchReg arch)) of
  Just Refl -> RegIP
  _ -> case testEquality r (MM.sp_reg @(MM.ArchReg arch)) of
    Just Refl -> RegSP
    _ -> RegG

zipRegStates :: Monad m
             => MM.RegisterInfo r
             => MM.RegState r f
             -> MM.RegState r g
             -> (forall u. r u -> f u -> g u -> m h)
             -> m [h]
zipRegStates regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> Const <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  return $ map (\(MapF.Pair _ (Const v)) -> v) $ MapF.toList $ MM.regStateMap regs'

----------------------------------

-- Expression binding

-- | Declares a type as being expression-containing, where the given traversal
--   occurs shallowly (i.e. not applied recursively to sub-expressions) on all embedded expressions.
class ExprMappable sym f where
  mapExpr ::
    W4.IsSymExprBuilder sym =>
    sym ->
    (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
    f ->
    IO f

instance ExprMappable sym (CS.RegValue' sym (CC.BaseToType bt)) where
  mapExpr _ f (CS.RV x) = CS.RV <$> f x

instance ExprMappable sym (CS.RegValue' sym (CLM.LLVMPointerType w)) where
  mapExpr sym f (CS.RV x) = CS.RV <$> mapExprPtr sym f x

instance ExprMappable sym (CS.RegValue' sym tp) => ExprMappable sym (CS.RegValue' sym (CC.MaybeType tp)) where
  mapExpr sym f (CS.RV pe) = CS.RV <$> case pe of
    PE.PE p e -> do
      p' <- f p
      CS.RV e' <- mapExpr sym f (CS.RV @sym @tp e)
      return $ PE.PE p' e'
    PE.Unassigned -> return PE.Unassigned

instance ExprMappable sym (Ctx.Assignment f Ctx.EmptyCtx) where
  mapExpr _ _ = return

instance
  (ExprMappable sym (Ctx.Assignment f ctx), ExprMappable sym (f tp)) =>
  ExprMappable sym (Ctx.Assignment f (ctx Ctx.::> tp)) where
  mapExpr sym f (asn Ctx.:> x) = do
    asn' <- mapExpr sym f asn
    x' <- mapExpr sym f x
    return $ asn' Ctx.:> x'

instance ExprMappable sym (MT.MemOpCondition sym) where
  mapExpr _sym f = \case
    MT.Conditional p -> MT.Conditional <$> f p
    MT.Unconditional -> return MT.Unconditional

instance ExprMappable sym (MT.MemOp sym w) where
  mapExpr sym f = \case
    MT.MemOp ptr dir cond w val endian -> do
      ptr' <- mapExprPtr sym f ptr
      val' <- mapExprPtr sym f val
      cond' <- mapExpr sym f cond
      return $ MT.MemOp ptr' dir cond' w val' endian
    MT.MergeOps p seq1 seq2 -> do
      p' <- f p
      seq1' <- traverse (mapExpr sym f) seq1
      seq2' <- traverse (mapExpr sym f) seq2
      return $ MT.MergeOps p' seq1' seq2'

instance ExprMappable sym (MT.MemTraceImpl sym w) where
  mapExpr sym f mem = do
    memSeq' <- traverse (mapExpr sym f) $ MT.memSeq mem
    memArr' <- f $ MT.memArr mem
    return $ MT.MemTraceImpl memSeq' memArr'

instance ExprMappable sym (MacawRegEntry sym tp) where
  mapExpr sym f entry = do
    case macawRegRepr entry of
      CLM.LLVMPointerRepr{} -> do
        val' <- mapExprPtr sym f $ macawRegValue entry
        return $ entry { macawRegValue = val' }
      _ -> fail "mapExpr: unsupported macaw type"

instance ExprMappable sym (MT.MemFootprint sym arch) where
  mapExpr sym f (MT.MemFootprint ptr w dir cond end) = do
    ptr' <- mapExprPtr sym f ptr
    cond' <- mapExpr sym f cond
    return $ MT.MemFootprint ptr' w dir cond' end

-----------------------------

data InnerEquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
  | UnsupportedArchitecture
  | UnsupportedRegisterType (Some CC.TypeRepr)
  | SymbolicExecutionFailed String -- TODO: do something better
  | InconclusiveSAT
  | NoUniqueFunctionOwner (IM.Interval (ConcreteAddress arch)) [MM.ArchSegmentOff arch]
  | LookupNotAtFunctionStart (ConcreteAddress arch)
  | StrangeBlockAddress (MM.ArchSegmentOff arch)
  -- starting address of the block, then a starting and ending address bracketing a range of undiscovered instructions
  | UndiscoveredBlockPart (ConcreteAddress arch) (ConcreteAddress arch) (ConcreteAddress arch)
  | NonConcreteParsedBlockAddress (MM.ArchSegmentOff arch)
  | BlockExceedsItsSegment (MM.ArchSegmentOff arch) (MM.ArchAddrWord arch)
  | BlockEndsMidInstruction
  | BlockStartsEarly (MM.ArchAddrWord arch) (MM.ArchAddrWord arch)
  | PrunedBlockIsEmpty
  | MemOpConditionMismatch
  | UnexpectedBlockKind String
  | UnexpectedMultipleEntries [MM.ArchSegmentOff arch] [MM.ArchSegmentOff arch]
  | forall ids. InvalidBlockTerminal (MD.ParsedTermStmt arch ids)
  | MissingPatchPairResult (PatchPair arch)
  | EquivCheckFailure String -- generic error
  | ImpossibleEquivalence
  | AssumedFalse
  | BlockExitMismatch
  | InvalidSMTModel
  | UnexpectedNonBoundVar
  | UnsatisfiableAssumptions
  | InequivalentError (InequivalenceResult arch)
  | MissingCrucibleGlobals
  | UnexpectedUnverifiedTriple
deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)

data EquivalenceError arch =
  EquivalenceError
    { errWhichBinary :: Maybe (Some WhichBinaryRepr)
    , errStackTrace :: Maybe CallStack
    , errEquivError :: InnerEquivalenceError arch
    }
instance MS.SymArchConstraints arch => Show (EquivalenceError arch) where
  show e = unlines $ catMaybes $
    [ fmap (\(Some b) -> "For " ++ show b ++ " binary") (errWhichBinary e)
    , fmap (\s -> "At " ++ prettyCallStack s) (errStackTrace e)
    , Just (show (errEquivError e))
    ]

instance (Typeable arch, MS.SymArchConstraints arch) => Exception (EquivalenceError arch)

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

--------------------------------

freeExprTerms :: forall sym t st fs tp.
  sym ~ W4B.ExprBuilder t st fs =>
  W4.SymExpr sym tp ->
  IO (Set (Some (W4.SymExpr sym)))
freeExprTerms expr = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (Const (Set (Some (W4.SymExpr sym))) tp')
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> return $ Const $ S.singleton (Some e)
      W4B.AppExpr appExpr -> do
        TFC.foldrMFC (collect @tp') mempty $ W4B.appExprApp appExpr
      W4B.NonceAppExpr naeE | W4B.FnApp fn args <- W4B.nonceExprApp naeE ->
        case W4B.symFnInfo fn of
          W4B.UninterpFnInfo _ _ -> TFC.foldrMFC (collect @tp') mempty args
          -- FIXME : collect terms from function body as well?
          W4B.DefinedFnInfo _ _ _ -> TFC.foldrMFC (collect @tp') mempty args
          _ -> return $ mempty
      _ -> return $ mempty
    collect ::
      forall tp'' tp'.
      W4.SymExpr sym tp' ->
      Const (Set (Some (W4.SymExpr sym))) tp'' ->
      IO (Const (Set (Some (W4.SymExpr sym))) tp'')
    collect e (Const s) = do
      Const s' <- go e
      return $ Const $ S.union s s'
  getConst <$> go expr


showModelForExpr :: forall sym tp.
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  IO String
showModelForExpr fn@(SymGroundEvalFn _) expr = do
  freeTerms <- freeExprTerms expr
  v <- execGroundFnIO fn expr
  let
    s = "Expression: " ++ show expr ++ "\n" ++
        "Value: " ++ showGroundValue (W4.exprType expr) v ++ "\n" ++
        "Environment:"

  foldM go s freeTerms
  where
    go :: String -> Some (W4.SymExpr sym)  -> IO String
    go s (Some e) = do
      gv <- execGroundFnIO fn e
      return $ s ++ "\n" ++ show e ++ " :== " ++ showGroundValue (W4.exprType e) gv

showGroundValue ::
  W4.BaseTypeRepr tp ->
  W4G.GroundValue tp ->
  String
showGroundValue repr gv = case repr of
  W4.BaseBoolRepr -> show gv
  W4.BaseBVRepr w -> BVS.ppHex w gv
  W4.BaseNatRepr -> show gv
  _ -> "Unsupported ground value"

