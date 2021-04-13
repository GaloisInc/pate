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
{-# LANGUAGE DeriveTraversable #-}


-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Types
  ( PatchPair(..)
  , PatchPairEq(..)
  , ppPatchPair
  , PatchPairC(..)
  , toPatchPairC
  , mergePatchPairCs
  , ppPatchPairCEq
  , ppPatchPairEq
  , ppPatchPairC
  , zipMPatchPairC
  , BlockPair
  , ConcreteBlock(..)
  , equivBlocks
  , getConcreteBlock
  , blockMemAddr
  , BlockMapping(..)
  , BlockTarget(..)
  , ConcreteAddress(..)
  , BlockEntryKind(..)
  , ppBlockEntry
  , absoluteAddress
  , addressAddOffset
  , concreteFromAbsolute
  , ParsedBlockMap(..)
  , ParsedFunctionMap
  , parsedFunctionEntries
  , markEntryPoint
  , type WhichBinary
  , KnownBinary
  , Original
  , Patched
  , WhichBinaryRepr(..)
  , ValidSym
  , Sym(..)
  , SymGroundEvalFn(..)
  , execGroundFnIO
  , InnerEquivalenceError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , equivalenceError
  --- register helpers
  , RegisterCase(..)
  , registerCase
  , zipRegStates
  , zipRegStatesPar
  , zipWithRegStatesM
  --- reporting
  , EquivalenceStatistics(..)
  , equivSuccess
  , ppEquivalenceStatistics
  , ppBlock
  , showModelForExpr
  , mapExprPtr
  , freshPtr
  , ptrEquality
  )
where

import           GHC.Stack

import           Control.Exception
import           Control.Lens hiding ( op, pre )
import           Control.Monad.Except

import qualified Data.BitVector.Sized as BVS
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import qualified Data.Kind as DK
import           Data.Map ( Map )
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Typeable
import qualified Prettyprinter as PP

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Solver as WS

import qualified Pate.Parallel as PP
import qualified Pate.Arch as PA
import           What4.ExprHelpers
import qualified Pate.ExprMappable as PEM

----------------------------------

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))

-- | Return the list of entry points in the parsed function map
parsedFunctionEntries :: ParsedFunctionMap arch -> [MM.ArchSegmentOff arch]
parsedFunctionEntries = concatMap M.keys . IM.elems

markEntryPoint ::
  MM.ArchSegmentOff arch ->
  ParsedBlockMap arch ids ->
  ParsedFunctionMap arch
markEntryPoint segOff blocks = M.singleton segOff (Some blocks) <$ getParsedBlockMap blocks

----------------------------------

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)
deriving instance Show (ConcreteAddress arch)

data PatchPair (tp :: WhichBinary -> DK.Type) = PatchPair
  { pOriginal :: tp 'Original
  , pPatched :: tp 'Patched
  }

class PatchPairEq tp where
  ppEq :: tp Original -> tp Patched -> Bool


data PatchPairC tp = PatchPairC
  { pcOriginal :: tp
  , pcPatched :: tp
  }
  deriving (Eq, Ord, Functor, Foldable, Traversable)

toPatchPairC ::
  PatchPair (Const f) ->
  PatchPairC f
toPatchPairC (PatchPair (Const v1) (Const v2)) = PatchPairC v1 v2

mergePatchPairCs ::
  PatchPairC a ->
  PatchPairC b ->
  PatchPairC (a, b)
mergePatchPairCs (PatchPairC o1 p1) (PatchPairC o2 p2) = PatchPairC (o1, o2) (p1, p2)

zipMPatchPairC ::
  Applicative m =>
  PatchPairC a ->
  PatchPairC b ->
  (a -> b -> m c) ->
  m (PatchPairC c)
zipMPatchPairC (PatchPairC a1 a2) (PatchPairC b1 b2) f = PatchPairC
  <$> f a1 b1
  <*> f a2 b2

instance TestEquality tp => Eq (PatchPair tp) where
  PatchPair o1 p1 == PatchPair o2 p2
    | Just Refl <- testEquality o1 o2
    , Just Refl <- testEquality p1 p2
    = True
  _ == _ = False

instance (TestEquality tp, OrdF tp) => Ord (PatchPair tp) where
  compare (PatchPair o1 p1) (PatchPair o2 p2) = toOrdering $ (lexCompareF o1 o2 (compareF p1 p2))

instance TF.FunctorF PatchPair where
  fmapF = TF.fmapFDefault

instance TF.FoldableF PatchPair where
  foldMapF = TF.foldMapFDefault

instance (forall bin. PEM.ExprMappable sym (f bin)) => PEM.ExprMappable sym (PatchPair f) where
  mapExpr sym f (PatchPair o p) = PatchPair <$> PEM.mapExpr sym f o <*> PEM.mapExpr sym f p

instance TF.TraversableF PatchPair where
  traverseF f (PatchPair o p) = PatchPair <$> f o <*> f p

type BlockPair arch = PatchPair (ConcreteBlock arch)


  

instance ShowF tp => Show (PatchPair tp) where
  show (PatchPair a1 a2) = showF a1 ++ " vs. " ++ showF a2

instance (PatchPairEq f, (forall bin. PP.Pretty (f bin))) => PP.Pretty (PatchPair f) where
  pretty = ppPatchPairEq ppEq PP.pretty 


ppPatchPair :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair f (PatchPair a1 a2) = f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"


ppPatchPairEq ::
  (tp Original -> tp Patched -> Bool) ->
  (forall bin. tp bin -> PP.Doc a) ->
  PatchPair tp ->
  PP.Doc a
ppPatchPairEq test f (PatchPair a1 a2) = case test a1 a2 of
  True -> f a1
  False -> f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"

ppPatchPairC ::
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairC f (PatchPairC o p) = ppPatchPair (\(Const v) -> f v) (PatchPair (Const o) (Const p))

ppPatchPairCEq ::
  Eq tp =>
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairCEq f ppair@(PatchPairC o p) = case o == p of
  True -> f o
  False -> ppPatchPairC f ppair

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

ppBlockEntry :: BlockEntryKind arch -> String
ppBlockEntry be = case be of
  BlockEntryInitFunction -> "function entry point"
  BlockEntryPostFunction -> "intermediate function point"
  BlockEntryPostArch -> "intermediate function point (after syscall)"
  BlockEntryJump -> "unknown program point"

data ConcreteBlock arch (bin :: WhichBinary) =
  ConcreteBlock { concreteAddress :: ConcreteAddress arch
                , concreteBlockEntry :: BlockEntryKind arch
                , blockBinRepr :: WhichBinaryRepr bin
                }

equivBlocks :: ConcreteBlock arch Original -> ConcreteBlock arch Patched -> Bool
equivBlocks blkO blkP =
  concreteAddress blkO == concreteAddress blkP &&
  concreteBlockEntry blkO == concreteBlockEntry blkP

instance PatchPairEq (ConcreteBlock arch) where
  ppEq = equivBlocks

getConcreteBlock ::
  MM.MemWidth (MM.ArchAddrWidth arch) =>
  MM.ArchSegmentOff arch ->
  BlockEntryKind arch ->
  WhichBinaryRepr bin ->
  Maybe (ConcreteBlock arch bin)
getConcreteBlock off k bin = case MM.segoffAsAbsoluteAddr off of
  Just addr -> Just $ ConcreteBlock (ConcreteAddress (MM.absoluteAddr addr)) k bin
  _ -> Nothing

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

instance MM.MemWidth (MM.ArchAddrWidth arch) => ShowF (ConcreteBlock arch) where
  showF blk = show blk

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

concreteFromAbsolute :: MM.MemWord (MM.ArchAddrWidth arch)
                     -> ConcreteAddress arch
concreteFromAbsolute = ConcreteAddress . MM.absoluteAddr

----------------------------------

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (W4B.ExprBuilder scope solver fs)

execGroundFnIO ::
  forall sym tp.
  SymGroundEvalFn sym -> 
  W4.SymExpr sym tp ->
  IO (W4G.GroundValue tp)
execGroundFnIO (SymGroundEvalFn (W4G.GroundEvalFn fn)) = fn

----------------------------------


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
  RegIP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | stack pointer
  RegSP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | table of contents register (if defined)
  RegTOC :: PA.HasTOCReg arch => RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | non-specific bitvector (zero-region pointer) register
  RegBV :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific pointer register
  RegGPtr :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific non-pointer reguster
  RegElse :: RegisterCase arch tp
  
registerCase ::
  forall arch tp.
  PA.ValidArch arch =>
  CC.TypeRepr (MS.ToCrucibleType tp) ->
  MM.ArchReg arch tp ->
  RegisterCase arch (MS.ToCrucibleType tp)
registerCase repr r = case testEquality r (MM.ip_reg @(MM.ArchReg arch)) of
  Just Refl -> RegIP
  _ -> case testEquality r (MM.sp_reg @(MM.ArchReg arch)) of
    Just Refl -> RegSP
    _ -> PA.withTOCCases (Proxy @arch) nontoc $
      case testEquality r (PA.toc_reg @arch) of
        Just Refl -> RegTOC
        _ -> nontoc
  where
    nontoc :: RegisterCase arch (MS.ToCrucibleType tp)
    nontoc = case repr of
      CLM.LLVMPointerRepr{} -> case PA.rawBVReg r of
        True -> RegBV
        False -> RegGPtr
      _ -> RegElse

zipRegStatesPar :: PP.IsFuture m future
                => MM.RegisterInfo r
                => MM.RegState r f
                -> MM.RegState r g
                -> (forall u. r u -> f u -> g u -> m (future h))
                -> m (future [h])
zipRegStatesPar regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> Const <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  PP.promise $ mapM (\(MapF.Pair _ (Const v)) -> PP.joinFuture v) $ MapF.toList $ MM.regStateMap regs'

zipRegStates :: Monad m
             => MM.RegisterInfo r
             => MM.RegState r f
             -> MM.RegState r g
             -> (forall u. r u -> f u -> g u -> m h)
             -> m [h]
zipRegStates regs1 regs2 f = join $ zipRegStatesPar regs1 regs2 (\r e1 e2 -> return $ f r e1 e2)

zipWithRegStatesM :: Monad m
                  => MM.RegisterInfo r
                  => MM.RegState r f
                  -> MM.RegState r g
                  -> (forall u. r u -> f u -> g u -> m (h u))
                  -> m (MM.RegState r h)
zipWithRegStatesM regs1 regs2 f = MM.mkRegStateM (\r -> f r (regs1 ^. MM.boundValue r) (regs2 ^. MM.boundValue r))

----------------------------------

type ValidSym sym =
  ( W4.IsExprBuilder sym
  , CB.IsSymInterface sym
  , ShowF (W4.SymExpr sym)
  )

data Sym sym where
  Sym :: (sym ~ (W4B.ExprBuilder t st fs), ValidSym sym) => sym -> WS.SolverAdapter st -> Sym sym

----------------------------------

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
  | MissingPatchPairResult (BlockPair arch)
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
  | InvalidCallTarget (ConcreteAddress arch)
  | IncompatibleDomainPolarities
deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)

data EquivalenceError arch where
  EquivalenceError ::
    PA.ValidArch arch =>
      { errWhichBinary :: Maybe (Some WhichBinaryRepr)
      , errStackTrace :: Maybe CallStack
      , errEquivError :: InnerEquivalenceError arch
      } -> EquivalenceError arch
instance Show (EquivalenceError arch) where
  show e@(EquivalenceError{}) = unlines $ catMaybes $
    [ fmap (\(Some b) -> "For " ++ show b ++ " binary") (errWhichBinary e)
    , fmap (\s -> "At " ++ prettyCallStack s) (errStackTrace e)
    , Just (show (errEquivError e))
    ]

instance (Typeable arch, MS.SymArchConstraints arch) => Exception (EquivalenceError arch)

equivalenceError :: PA.ValidArch arch => InnerEquivalenceError arch -> EquivalenceError arch
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Nothing
  , errEquivError = err
  }
----------------------------------


ptrEquality ::
  TestEquality (W4B.SymExpr sym) =>
  CLM.LLVMPtr sym w1 ->
  CLM.LLVMPtr sym w2 ->
  Maybe (w1 :~: w2)
ptrEquality (CLM.LLVMPointer reg1 off1) (CLM.LLVMPointer reg2 off2)
  | reg1 == reg2, Just Refl <- testEquality off1 off2 = Just Refl
ptrEquality _ _ = Nothing

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
  W4.BaseIntegerRepr -> show gv
  _ -> "Unsupported ground value"

