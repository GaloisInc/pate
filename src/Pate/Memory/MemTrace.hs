{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ConstraintKinds #-}


#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Memory.MemTrace
( MemTraceImpl(..)
, MemTraceState
, MemTrace
, MemTraceSeq
, llvmPtrEq
, readMemState
, writeMemState
, MemFootprint(..)
, MemOpDirection(..)
, getCond
, MemTraceK
, traceFootprint
, getReadOps
, observableEvents
, UndefPtrOpTag
, UndefPtrOpTags
, UndefinedPtrOps(..)
, MemOpCondition(..)
, MemOp(..)
, MemEvent(..)
, MacawSyscallModel(..)
, memTraceIntrinsicTypes
, initMemTrace
, classifyExpr
, mkMemTraceVar
, mkMemoryBinding
, mkUndefinedPtrOps
, macawTraceExtensions
, memEqOutsideRegion
, memEqAtRegion
, memEqExact
, prettyMemOp
, prettyMemEvent
, prettyMemTraceSeq
) where

import Unsafe.Coerce
import           Control.Applicative
import           Control.Lens ((%~), (&), (^.), (.~))
import           Control.Monad.State
import qualified Data.BitVector.Sized as BV
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Vector as V
import           Data.IORef
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.TypeNats (KnownNat, type Nat)
import           Prettyprinter

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.Types as MT
import Data.Macaw.CFG.AssignRhs (ArchAddrWidth, MemRepr(..))
import Data.Macaw.Memory
           (AddrWidthRepr(..), Endianness(..), MemWidth
           , addrWidthClass, addrWidthRepr, addrWidthNatRepr
           , incSegmentOff, memWordToUnsigned, MemSegmentOff )
import Data.Macaw.Symbolic.Backend (MacawEvalStmtFunc, MacawArchEvalFn(..))
import Data.Macaw.Symbolic ( MacawStmtExtension(..), MacawExprExtension(..), MacawExt
                           , GlobalMap
                           , IsMemoryModel(..)
                           , SymArchConstraints
                           , evalMacawExprExtension
                           )
import qualified Data.Macaw.Symbolic as MS

import Data.Macaw.Symbolic.MemOps ( doGetGlobal )

import Data.Parameterized.Context (pattern (:>), pattern Empty, Assignment)
import qualified Data.Parameterized.Map as MapF
import Data.Text (Text, pack)
import Lang.Crucible.Backend (IsSymInterface, IsSymBackend, HasSymInterface(..), assert)
import Lang.Crucible.CFG.Common (GlobalVar, freshGlobalVar)
import Lang.Crucible.FunctionHandle (HandleAllocator, mkHandle',insertHandleMap)
import Lang.Crucible.LLVM.MemModel (LLVMPointerType, LLVMPtr, pattern LLVMPointer, pattern LLVMPointerRepr, ppPtr)
import Lang.Crucible.Simulator.ExecutionTree
         ( CrucibleState, ExtensionImpl(..), actFrame, gpGlobals
         , stateSymInterface, stateTree, withBackend, stateContext
         , simHandleAllocator, functionBindings, FunctionBindings(..)
         , FnState(..)
         )
import Lang.Crucible.Simulator.GlobalState (insertGlobal, lookupGlobal)
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass(..), IntrinsicMuxFn(..), IntrinsicTypes)
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap (RegEntry(..), FnVal, RegMap(..))
import Lang.Crucible.Simulator.RegValue (RegValue, FnVal(..), RegValue'(..) )
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Simulator.SymSequence
import Lang.Crucible.Types
import Lang.Crucible.Utils.MuxTree
import What4.Expr.Builder (ExprBuilder)
import What4.Interface


import           Pate.Panic
import qualified Pate.ExprMappable as PEM
import qualified What4.ExprHelpers as WEH

------
-- * Undefined pointers

-- | Wrapping undefined pointer operations with uninterpreted functions.
-- Pointer operations are generally partial due to potential incompatibilities in their regions.
-- In cases where the result of an operating is undefined, rather than yielding a fresh constant, we
-- instead yield an uninterpreted function that takes the original operands as arguments.
-- This allows us to prove, for example, that a = x, b = y ==> a + b == x + y, without necessarily
-- proving that this operation is defined. i.e. if it is not defined then we end up with undefPtrAdd(a, b) == undefPtrAdd(x, y).
--
-- To ensure that this is still true, we need to make sure that we only generate fresh uninterpreted
-- functions when necessary, which is complicated by the fact that unintepreted functions must be monomorphic. We therefore lazily generate and cache each monomorphic variant of the uninterpreted function as they are needed.

-- | A collection of functions used to produce undefined values for each pointer operation.
data UndefinedPtrOps sym =
  UndefinedPtrOps
    { undefPtrOff :: (forall w. sym -> LLVMPtr sym w -> IO (SymBV sym w))
    , undefPtrLt :: UndefinedPtrPredOp sym
    , undefPtrLeq :: UndefinedPtrPredOp sym
    , undefPtrAdd :: UndefinedPtrBinOp sym
    , undefPtrSub :: UndefinedPtrBinOp sym
    , undefPtrAnd :: UndefinedPtrBinOp sym
    , undefPtrXor :: UndefinedPtrBinOp sym
    , undefPtrClassify :: UndefPtrClassify sym
    }

data UndefPtrOpTag =
    UndefPtrOff
  | UndefPtrLt
  | UndefPtrLeq
  | UndefPtrAdd
  | UndefPtrSub
  | UndefPtrAnd
  | UndefPtrXor
  deriving (Show, Eq, Ord)

type UndefPtrOpTags = Set UndefPtrOpTag

-- | Classify an expression as representing an undefined pointer.
newtype UndefPtrClassify sym =
  UndefPtrClassify
    { classifyExpr :: forall tp. SymExpr sym tp -> IO UndefPtrOpTags }

instance Semigroup (UndefPtrClassify sym) where
  f1 <> f2 = UndefPtrClassify $ \e -> do
    class1 <- classifyExpr f1 e
    class2 <- classifyExpr f2 e
    return $ class1 <> class2

instance Monoid (UndefPtrClassify sym) where
  mempty = UndefPtrClassify $ \_ -> return mempty

-- | Wraps a function which is used to produce an "undefined" pointer that
-- may result from a binary pointer operation.
-- The given predicate is true when the operation is defined. i.e if this predicate
-- is true then this undefined value is unused. The two other arguments are the original inputs to the binary pointer operation.
newtype UndefinedPtrBinOp sym =
  UndefinedPtrBinOp
    { mkUndefPtr ::
        forall w.
        sym ->
        LLVMPtr sym w ->
        LLVMPtr sym w ->
        IO (LLVMPtr sym w)
    }

-- | Wraps a function which is used to produce an "undefined" predicate that
-- may result from a binary pointer operation.
-- The given predicate is true when the operation is defined. i.e if this predicate
-- is true then this undefined value is unused. The two other arguments are the original inputs to the binary pointer operation.
newtype UndefinedPtrPredOp sym =
  UndefinedPtrPredOp
    { mkUndefPred ::
        forall w.
        sym ->
        LLVMPtr sym w ->
        LLVMPtr sym w ->
        IO (Pred sym)
    }

-- | Wrapping a pointer as a struct, so that it may be represented as the
-- result of an uninterpreted function.
type BasePtrType w = BaseStructType (EmptyCtx ::> BaseIntegerType ::> BaseBVType w)
type SymPtr sym w = SymExpr sym (BasePtrType w)

asSymPtr ::
  IsSymExprBuilder sym =>
  sym ->
  LLVMPtr sym w ->
  IO (SymPtr sym w)
asSymPtr sym (LLVMPointer reg off) = do
  ireg <- natToInteger sym reg
  mkStruct sym (Empty :> ireg :> off)

fromSymPtr ::
  IsSymExprBuilder sym =>
  sym ->
  SymPtr sym w ->
  IO (LLVMPtr sym w )
fromSymPtr sym sptr = do
  reg <- structField sym sptr Ctx.i1of2
  off <- structField sym sptr Ctx.i2of2
  nreg <- integerToNat sym reg
  return $ LLVMPointer nreg off

polySymbol ::
  UndefPtrOpTag ->
  NatRepr w ->
  SolverSymbol
polySymbol tag w = safeSymbol $ (show tag) ++ "_" ++ (show w)

type AnyNat = 0
-- | Defines how a given type can be concretized to a specific type-level nat.
-- This allows us to easily describe a type that is polymorphic in one natural,
-- using existing type constructors.
type family NatAbs tp (w :: Nat) :: BaseType where
  NatAbs (BasePtrType AnyNat) w' = BasePtrType w'
  NatAbs (BasePtrType w) _ = BasePtrType w
  NatAbs (BaseBVType AnyNat) w' = BaseBVType w'
  NatAbs (BaseBVType w) _ = BaseBVType w
  NatAbs BaseBoolType _ = BaseBoolType
  NatAbs BaseIntegerType _ = BaseIntegerType

type family NatAbsCtx tp (w :: Nat) :: Ctx.Ctx BaseType where
  NatAbsCtx EmptyCtx w = EmptyCtx
  NatAbsCtx (ctx Ctx.::> tp) w' = NatAbsCtx ctx w' Ctx.::> NatAbs tp w'

{-
natAbsBVFixed :: 1 <= w => NatRepr w -> NatRepr w' -> (NatAbs (BaseBVType w) w' :~: BaseBVType w)
natAbsBVFixed _ _ = unsafeCoerce Refl
-}

data PolyFun sym args ret (w :: Nat) where
  PolyFun ::
    { polyFunClassify :: UndefPtrClassify sym
    , applyPolyFun :: Ctx.Assignment (SymExpr sym) (NatAbsCtx args w) -> IO (SymExpr sym (NatAbs ret w))
    }
    -> PolyFun sym args ret w

newtype PolyFunMaker sym args ret =
  PolyFunMaker (forall w. 1 <= w => sym -> NatRepr w -> IO (PolyFun sym args ret w))

-- avoiding struct-indexed arrays, which are unsupported by ground evaluation
type family FlatStructs tp :: Ctx.Ctx BaseType where
  FlatStructs (BaseStructType ctx) = FlatStructsCtx ctx
  FlatStructs (BaseBVType w) = EmptyCtx ::> (BaseBVType w)
  FlatStructs BaseIntegerType = EmptyCtx ::> BaseIntegerType
  FlatStructs BaseBoolType = EmptyCtx ::> BaseBVType 1

type family FlatStructsCtx ctx :: Ctx.Ctx BaseType where
  FlatStructsCtx EmptyCtx = EmptyCtx
  FlatStructsCtx (ctx ::> tp) = FlatStructsCtx ctx Ctx.<+> FlatStructs tp

flattenStructRepr :: Ctx.Assignment BaseTypeRepr ctx -> Ctx.Assignment BaseTypeRepr (FlatStructsCtx ctx)
flattenStructRepr Ctx.Empty = Ctx.Empty
flattenStructRepr (ctx :> BaseStructRepr ctx') = flattenStructRepr ctx Ctx.<++> flattenStructRepr ctx'
flattenStructRepr (ctx :> (BaseBVRepr w)) = flattenStructRepr ctx :> (BaseBVRepr w)
flattenStructRepr (ctx :> BaseIntegerRepr) = flattenStructRepr ctx :> BaseIntegerRepr
flattenStructRepr (ctx :> BaseBoolRepr) = flattenStructRepr ctx :> BaseBVRepr (knownNat @1)
flattenStructRepr tp = error $ "flattenStructRepr: unsupported type:" ++ show tp

flattenStructs ::
  IsSymInterface sym =>
  sym ->
  Ctx.Assignment (SymExpr sym) ctx ->
  IO (Ctx.Assignment (SymExpr sym) (FlatStructsCtx ctx))
flattenStructs sym (ctx :> e) = do
  ctx_flat <- flattenStructs sym ctx
  case exprType e of
    BaseStructRepr ctx' -> do
      fields <- Ctx.traverseWithIndex (\idx _ -> structField sym e idx) ctx'
      ctx'_flat <- flattenStructs sym fields
      return $ ctx_flat Ctx.<++> ctx'_flat
    BaseBVRepr _ -> return $ ctx_flat Ctx.:> e
    BaseIntegerRepr -> return $ ctx_flat Ctx.:> e
    BaseBoolRepr -> do
      bv <- predToBV sym e (knownNat @1)
      return $ ctx_flat Ctx.:> bv
    tp -> fail $ "flattenStructs: unsupported type:" ++ show tp
flattenStructs _sym Ctx.Empty = return Ctx.empty


mkClassify ::
  forall sym tp1.
  IsSymInterface sym =>
  UndefPtrOpTag ->
  SymExpr sym tp1 ->
  UndefPtrClassify sym
mkClassify tag e1 = UndefPtrClassify $ \e2 -> case testEquality e1 e2 of
  Just Refl -> return $ Set.singleton tag
  _ -> return mempty

mkBinUF ::
  IsSymInterface sym =>
  UndefPtrOpTag ->
  PolyFunMaker sym (EmptyCtx ::> BasePtrType AnyNat ::> BasePtrType AnyNat) (BasePtrType AnyNat)
mkBinUF tag  = PolyFunMaker $ \sym w -> do
  let
    ptrRepr = BaseStructRepr (Empty :> BaseIntegerRepr :> BaseBVRepr w)
    repr = Empty :> ptrRepr :> ptrRepr
  c <- freshConstant sym (polySymbol tag w) (BaseArrayRepr (flattenStructRepr repr) ptrRepr)
  return $ PolyFun (mkClassify tag c) $ \args -> arrayLookup sym c =<< flattenStructs sym args

mkPredUF ::
  forall sym.
  IsSymInterface sym =>
  UndefPtrOpTag ->
  PolyFunMaker sym (EmptyCtx ::> BasePtrType AnyNat Ctx.::> BasePtrType AnyNat) BaseBoolType
mkPredUF tag = PolyFunMaker $ \sym w -> do
  let
    repr = Empty :> BaseIntegerRepr :> BaseBVRepr w :> BaseIntegerRepr :> BaseBVRepr w
  c <- freshConstant sym (polySymbol tag w) (BaseArrayRepr (flattenStructRepr repr) BaseBoolRepr)
  return $ PolyFun (mkClassify tag c) $ \args -> arrayLookup sym c =<< flattenStructs sym args

mkOffUF ::
  forall sym.
  IsSymInterface sym =>
  UndefPtrOpTag ->
  PolyFunMaker sym (EmptyCtx ::> BasePtrType AnyNat) (BaseBVType AnyNat)
mkOffUF tag = PolyFunMaker $ \sym w -> do
  let
    ptrRepr = BaseStructRepr (Empty :> BaseIntegerRepr :> BaseBVRepr w)
    repr = Empty :> ptrRepr
  c <- freshConstant sym (polySymbol tag w) (BaseArrayRepr (flattenStructRepr repr) (BaseBVRepr w))
  return $ PolyFun (mkClassify tag c) $ \args -> arrayLookup sym c =<< flattenStructs sym args

cachedPolyFun ::
  forall sym f g.
  sym ->
  PolyFunMaker sym f g ->
  IO (PolyFunMaker sym f g, UndefPtrClassify sym)
cachedPolyFun _sym (PolyFunMaker f) = do
  ref <- newIORef (MapF.empty :: MapF.MapF NatRepr (PolyFun sym f g))
  let
    mker' = PolyFunMaker $ \sym' nr -> do
      m <- readIORef ref
      case MapF.lookup nr m of
        Just a -> return a
        Nothing -> do
          result <- f sym' nr
          let m' = MapF.insert nr result m
          writeIORef ref m'
          return result
    classify = UndefPtrClassify $ \e -> do
      m <- readIORef ref
      let classifier = mconcat (map (\(Some pf) -> polyFunClassify pf) (MapF.elems m))
      classifyExpr classifier e
  return (mker', classify)


withPtrWidth :: IsExprBuilder sym => LLVMPtr sym w -> (1 <= w => NatRepr w -> a) -> a
withPtrWidth (LLVMPointer _blk bv) f | BaseBVRepr w <- exprType bv = f w
--withPtrWidth _ _ = error "impossible"

mkBinOp ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  UndefPtrOpTag ->
  IO (UndefinedPtrBinOp sym, UndefPtrClassify sym)
mkBinOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkBinUF tag
  let binop =
        UndefinedPtrBinOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          sptrResult <- applyPolyFun resultfn (Empty :> sptr1 :> sptr2)
          fromSymPtr sym' sptrResult
  return (binop, classifier)

mkPredOp ::
  IsSymInterface sym =>
  sym ->
  UndefPtrOpTag ->
  IO (UndefinedPtrPredOp sym, UndefPtrClassify sym)
mkPredOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkPredUF tag
  let binop =
        UndefinedPtrPredOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          applyPolyFun resultfn (Empty :> sptr1 :> sptr2)
  return (binop, classifier)

mkUndefinedPtrOps ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  IO (UndefinedPtrOps sym)
mkUndefinedPtrOps sym = do
  (PolyFunMaker offFn, classOff) <- cachedPolyFun sym $ mkOffUF UndefPtrOff
  let
    offPtrFn :: forall w. sym -> LLVMPtr sym w -> IO (SymBV sym w)
    offPtrFn sym'  ptr = withPtrWidth ptr $ \w -> do
      sptr <- asSymPtr sym' ptr
      resultfn <- offFn sym' w
      applyPolyFun resultfn (Empty :> sptr)

  (undefPtrLt', classLt) <- mkPredOp sym UndefPtrLt
  (undefPtrLeq', classLeq) <- mkPredOp sym UndefPtrLeq
  (undefPtrAdd', classAdd) <- mkBinOp sym UndefPtrAdd
  (undefPtrSub', classSub) <- mkBinOp sym UndefPtrSub
  (undefPtrAnd', classAnd) <- mkBinOp sym UndefPtrAnd
  (undefPtrXor', classXor) <- mkBinOp sym UndefPtrXor
  return $
    UndefinedPtrOps
      { undefPtrOff = offPtrFn
      , undefPtrLt = undefPtrLt'
      , undefPtrLeq = undefPtrLeq'
      , undefPtrAdd = undefPtrAdd'
      , undefPtrSub = undefPtrSub'
      , undefPtrAnd = undefPtrAnd'
      , undefPtrXor = undefPtrXor'
      , undefPtrClassify = mconcat [classOff, classLt, classLeq, classAdd, classSub, classAnd, classXor]
      }

-- * Memory trace model

-- | Like 'macawExtensions', but with an alternative memory model that records
-- memory operations without trying to carefully guess the results of
-- performing them.
macawTraceExtensions ::
  (IsSymInterface sym, SymArchConstraints arch, sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn p sym (MemTrace arch) arch ->
  MacawSyscallModel sym arch ->
  GlobalVar (MemTrace arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  UndefinedPtrOps sym ->
  ExtensionImpl p sym (MacawExt arch)
macawTraceExtensions archStmtFn syscallModel mvar globs undefptr =
  ExtensionImpl
    { extensionEval = \bak iTypes logFn cst g -> evalMacawExprExtensionTrace undefptr bak iTypes logFn cst g
    , extensionExec = execMacawStmtExtension archStmtFn undefptr syscallModel mvar globs
    }


data MemOpCondition sym
  = Unconditional
  | Conditional (Pred sym)


deriving instance Show (Pred sym) => Show (MemOpCondition sym)

data MemOpDirection =
    Read
  | Write
  deriving (Eq, Ord, Show)


data MemOp sym ptrW where
  MemOp ::
    1 <= w =>
    -- The address of the operation
    LLVMPtr sym ptrW ->
    MemOpDirection ->
    MemOpCondition sym ->
    -- The size of the operation in bytes
    NatRepr w ->
    -- The value read or written during the operation
    LLVMPtr sym (8*w) ->
    Endianness ->
    MemOp sym ptrW

prettyMemOp :: IsExpr (SymExpr sym) => MemOp sym ptrW -> Doc ann
prettyMemOp (MemOp ptr dir cond _sz val _end) =
  viaShow dir <+>
  ppPtr ptr <+>
  (case dir of Read -> "->" ; Write -> "<-") <+>
  ppPtr val <+>
  case cond of
    Unconditional -> mempty
    Conditional p -> "when" <+> printSymExpr p

instance TestEquality (SymExpr sym) => Eq (MemOpCondition sym) where
  Unconditional == Unconditional = True
  Conditional p == Conditional p' | Just Refl <- testEquality p p' = True
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemOpCondition sym) where
  compare Unconditional Unconditional = EQ
  compare (Conditional p) (Conditional p') = toOrdering $ compareF p p'
  compare Unconditional _ = GT
  compare _ Unconditional = LT

instance TestEquality (SymExpr sym) => Eq (MemOp sym ptrW) where
  MemOp (LLVMPointer addrR addrO) dir cond repr (LLVMPointer valR valO) end
    == MemOp (LLVMPointer addrR' addrO') dir' cond' repr' (LLVMPointer valR' valO') end'
     | Just Refl <- testEquality repr repr'
     , addrR == addrR'
     , Just Refl <- testEquality addrO addrO'
     , valR == valR'
     , Just Refl <- testEquality valO valO'
    = cond == cond' && dir == dir' && end == end'

  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemOp sym ptrW) where
  compare (MemOp (LLVMPointer reg1 off1) dir1 cond1 sz1 (LLVMPointer vr1 vo1) end1)
          (MemOp (LLVMPointer reg2 off2) dir2 cond2 sz2 (LLVMPointer vr2 vo2) end2) =
    case compareF sz1 sz2 of
      LTF -> LT
      GTF -> GT
      EQF ->
        (compare reg1 reg2) <>
        (toOrdering $ compareF off1 off2) <>
        compare dir1 dir2 <>
        (compare cond1 cond2) <>
        (compare vr1 vr2) <>
        (toOrdering $ compareF vo1 vo2) <>
        compare end1 end2

data MemEvent sym ptrW where
  MemOpEvent :: MemOp sym ptrW -> MemEvent sym ptrW
  SyscallEvent :: forall sym ptrW w.
    (1 <= w) =>
    MuxTree sym (Maybe (MemSegmentOff ptrW, Text))
      {- ^ location and dissassembly of the instruction generating this system call -} ->
    SymExpr sym (BaseBVType w)
      {- ^ The value of R0 when this system call occurred -} -> 
    MemEvent sym ptrW

prettyMemEvent :: (MemWidth ptrW, IsExpr (SymExpr sym)) => MemEvent sym ptrW -> Doc ann
prettyMemEvent (MemOpEvent op) = prettyMemOp op
prettyMemEvent (SyscallEvent i v) =
  case viewMuxTree i of
    [(Just (addr, dis), _)] -> "Syscall At:" <+> viaShow addr <+> pretty dis <> line <> printSymExpr v
    _ -> "Syscall" <+> printSymExpr v

prettyMemTraceSeq :: (MemWidth ptrW, IsExpr (SymExpr sym)) => MemTraceSeq sym ptrW -> Doc ann
prettyMemTraceSeq = prettySymSequence prettyMemEvent

data MemTraceImpl sym ptrW = MemTraceImpl
  { memSeq :: MemTraceSeq sym ptrW
  -- ^ The sequence of memory operations in reverse execution order;
  --   later events appear closer to the front of the sequence.
  , memState :: MemTraceState sym ptrW
  -- ^ the logical contents of memory
  , memCurrentInstr :: MuxTree sym (Maybe (MemSegmentOff ptrW, Text))
  -- ^ the most recent program instruction we encountered (address, dissassembly)
  }

data MemTraceState sym ptrW = MemTraceState
  { memArr :: MemTraceArr sym ptrW }

type MemTraceSeq sym ptrW = SymSequence sym (MemEvent sym ptrW)
type MemTraceArr sym ptrW = MemArrBase sym ptrW (BaseBVType 8)

type MemArrBase sym ptrW tp = RegValue sym (SymbolicArrayType (EmptyCtx ::> BaseIntegerType) (BaseArrayType (EmptyCtx ::> BaseBVType ptrW) tp))

type MemTrace arch = IntrinsicType "memory_trace" (EmptyCtx ::> BVType (ArchAddrWidth arch))

data MemTraceK

instance IsMemoryModel MemTraceK where
  type MemModelType MemTraceK arch = MemTrace arch
  type MemModelConstraint MemTraceK sym = ()

mkMemTraceVar ::
  forall arch.
  (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) =>
  HandleAllocator ->
  IO (GlobalVar (MemTrace arch))
mkMemTraceVar ha = freshGlobalVar ha (pack "llvm_memory_trace") knownRepr

initMemTrace ::
  forall sym ptrW.
  IsSymExprBuilder sym =>
  sym ->
  AddrWidthRepr ptrW ->
  IO (MemTraceImpl sym ptrW)
initMemTrace sym Addr32 = do
  arr <- ioFreshConstant sym "InitMem" knownRepr
  sq <- nilSymSequence sym
  return $ MemTraceImpl sq (MemTraceState arr) (toMuxTree sym Nothing)
initMemTrace sym Addr64 = do
  arr <- ioFreshConstant sym "InitMem" knownRepr
  sq <- nilSymSequence sym
  return $ MemTraceImpl sq (MemTraceState arr) (toMuxTree sym Nothing)


mkMemoryBinding ::
  forall sym ptrW.
  -- | initial memory state (appears in the the given expression when the binding is applied)
  MemTraceState sym ptrW ->
  -- | target memory state (to appear in the resulting expression when the binding is applied)
  MemTraceState sym ptrW ->
  WEH.ExprBindings sym
mkMemoryBinding memSrc memTgt =
  let
    MemTraceState memSrcArr = memSrc
    MemTraceState memTgtArr = memTgt
  in MapF.singleton memSrcArr memTgtArr


instance IsExprBuilder sym => IntrinsicClass sym "memory_trace" where
  -- TODO: cover other cases with a TypeError
  type Intrinsic sym "memory_trace" (EmptyCtx ::> BVType ptrW) = MemTraceImpl sym ptrW
  muxIntrinsic sym _ _ (Empty :> BVRepr _) p t f = do
    memSeq'   <- muxSymSequence sym p (memSeq t) (memSeq f)
    memArr'   <- baseTypeIte sym p (memArr $ memState t) (memArr $ memState f)
    memInstr' <- mergeMuxTree sym p (memCurrentInstr t) (memCurrentInstr f)
    return $ MemTraceImpl memSeq' (MemTraceState memArr') memInstr'

  muxIntrinsic _ _ _ _ _ _ _ = error "Unexpected operands in memory_trace mux"

memTraceIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
memTraceIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "memory_trace") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn
  $ MapF.empty

type MacawTraceEvalStmtFunc p sym arch = MacawEvalStmtFunc (MacawStmtExtension arch) p sym (MacawExt arch)

execMacawStmtExtension ::
  forall p sym arch t st fs. (IsSymInterface sym, SymArchConstraints arch, sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn p sym (MemTrace arch) arch ->
  UndefinedPtrOps sym ->
  MacawSyscallModel sym arch ->
  GlobalVar (MemTrace arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  MacawTraceEvalStmtFunc p sym arch
execMacawStmtExtension (MacawArchEvalFn archStmtFn) mkundef syscallModel mvar globs stmt
  = case stmt of
    MacawReadMem addrWidth memRepr addr
      -> liftToCrucibleState mvar $ \sym ->
        doReadMem sym addrWidth (regValue addr) memRepr

    MacawCondReadMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondReadMem sym (regValue cond) (regValue def) addrWidth (regValue addr) memRepr

    MacawWriteMem addrWidth memRepr addr val
      -> liftToCrucibleState mvar $ \sym ->
        doWriteMem sym addrWidth (regValue addr) (regValue val) memRepr

    MacawCondWriteMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondWriteMem sym (regValue cond) addrWidth (regValue addr) (regValue def) memRepr

    MacawGlobalPtr w addr -> \cst -> addrWidthClass w $ doGetGlobal cst mvar globs addr
    MacawFreshSymbolic t -> liftToCrucibleState mvar $ \sym -> case t of
       MT.BoolTypeRepr -> liftIO $ freshConstant sym (safeSymbol "macawFresh") BaseBoolRepr
       MT.BVTypeRepr n -> liftIO $ do
         regI <- freshConstant sym (safeSymbol "macawFresh") BaseIntegerRepr
         reg <- integerToNat sym regI
         off <- freshConstant sym (safeSymbol "macawFresh") (BaseBVRepr n)
         return $ LLVMPointer reg off
       _ -> error ( "MacawFreshSymbolic is unsupported in the trace memory model: " ++ show t)
    MacawLookupFunctionHandle _typeReps _registers ->
      error "MacawLookupFunctionHandle is unsupported in the trace memory model"

    MacawLookupSyscallHandle argTys retTys _args ->
      installMacawSyscallHandler argTys retTys syscallModel mvar

    MacawArchStmtExtension archStmt -> archStmtFn mvar globs archStmt

    MacawArchStateUpdate{} -> \cst -> pure ((), cst)
    MacawInstructionStart baddr iaddr dis ->
      case incSegmentOff baddr (memWordToUnsigned iaddr) of
        Just off -> 
          liftToCrucibleState mvar $ \sym ->
            modify (\mem -> mem{ memCurrentInstr = toMuxTree sym (Just (off,dis)) })
        Nothing ->
          panic Verifier "execMacawExteions: MacawInstructionStart"
                    [ "MemorySegmentOff out of range"
                    , show baddr
                    , show iaddr
                    ]

    PtrEq w x y -> ptrOp w x y $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak
      regEq <- natEq sym reg reg'
      offEq <- bvEq sym off off'
      andPred sym regEq offEq

    PtrLeq w x y -> ptrOp w x y $ ptrPredOp (undefPtrLeq mkundef) natEqConstraint $ \sym _reg off _reg' off' -> bvUle sym off off'


    PtrLt w x y -> ptrOp w x y $ ptrPredOp (undefPtrLt mkundef) natEqConstraint $ \sym _reg off _reg' off' -> bvUlt sym off off'

    PtrMux w (RegEntry _ p) x y -> ptrOp w x y $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak
      reg'' <- natIte sym p reg reg'
      off'' <- bvIte sym p off off'
      pure (LLVMPointer reg'' off'')

    PtrAdd w x y -> ptrOpNR w x y $ ptrBinOp (undefPtrAdd mkundef) someZero $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak

      regZero <- isZero sym reg

      reg'' <- natIte sym regZero reg' reg
      off'' <- bvAdd sym off off'
      pure (LLVMPointer reg'' off'')

    PtrSub w x y -> ptrOp w x y $ ptrBinOp (undefPtrSub mkundef) compatSub $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak
      regEq <- natEq sym reg reg'
      zero <- natLit sym 0

      reg'' <- natIte sym regEq zero reg
      off'' <- bvSub sym off off'
      pure (LLVMPointer reg'' off'')

    PtrAnd w x y -> ptrOp w x y $ ptrBinOp (undefPtrAnd mkundef) someZero $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak
      regZero <- isZero sym reg

      reg'' <- natIte sym regZero reg' reg
      off'' <- bvAndBits sym off off'
      pure (LLVMPointer reg'' off'')

    PtrXor w x y -> ptrOp w x y $ ptrBinOp (undefPtrXor mkundef) someZero $ \bak reg off reg' off' -> do
      let sym = backendGetSym bak
      regZero <- isZero sym reg

      reg'' <- natIte sym regZero reg' reg
      off'' <- bvXorBits sym off off'
      pure (LLVMPointer reg'' off'')

    PtrTrunc w (RegEntry _ (LLVMPointer region offset)) -> readOnlyWithSym $ \sym -> do
      off' <- bvTrunc sym w offset
      pure (LLVMPointer region off')

    PtrUExt w (RegEntry _ (LLVMPointer region offset)) -> readOnlyWithSym $ \sym -> do
      off' <- bvZext sym w offset
      pure (LLVMPointer region off')

-- | Currently this is only a dummy value, but the idea is that
--   eventually this will specify the runtime behvior
--   of system calls.  At a minimum, it should know how
--   to transform the collection of intput registers into
--   a collection of output registers and produce an
--   observable event in the trace model (at whatever level of
--   detail we deem appropriate). We should also
--   have some approprate way to specify conservative
--   assumptions about memory effects. The appropriate
--   thing to do here may be architecture and platform
--   dependent, which is why it is a parameter.
--
--   If we get more ambituous, the system call model may
--   actually provide precise behavior modeling the action of
--   the system call.
newtype MacawSyscallModel sym arch = MacawSyscallModel ()

installMacawSyscallHandler ::
  IsSymInterface sym =>
  Assignment TypeRepr atps ->
  Assignment TypeRepr rtps ->
  MacawSyscallModel sym arch ->
  GlobalVar (MemTrace arch) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (FnVal sym atps (StructType rtps), CrucibleState p sym ext rtp blocks r ctx)
installMacawSyscallHandler atps rtps syscallModel mvar cst =
  do let simCtx = cst^.stateContext
     let halloc = simHandleAllocator simCtx
     let nm = "MacawSyscall"
     fnh <- mkHandle' halloc nm atps (StructRepr rtps)
     let FnBindings fns = simCtx ^. functionBindings
     let ovr  = mkOverride' nm (StructRepr rtps) $
                  do RegMap args <- getOverrideArgs
                     applySyscallModel rtps args syscallModel mvar
     let fns' = FnBindings (insertHandleMap fnh (UseOverride ovr) fns)
     return (HandleFnVal fnh, cst & stateContext . functionBindings .~ fns')

applySyscallModel ::
  IsSymInterface sym =>
  Assignment TypeRepr rtps ->
  Assignment (RegEntry sym) atps ->
  MacawSyscallModel sym arch ->
  GlobalVar (MemTrace arch) ->
  OverrideSim p sym ext r args (StructType rtps) (RegValue sym (StructType rtps))

applySyscallModel
  -- TODO, overspecialzed to ARM32, this should really be using the @MacawSyscallModel@,
  -- when we figure out what those should look like.
  (Ctx.Empty :> LLVMPointerRepr w0 :>
                LLVMPointerRepr w1)
  (Ctx.Empty :> r0 :> r1 :> _r2 :> _r3 :> _r4 :> _r5 :> _r6 :> _r7)
  _syscallModel
  mvar
   | Just Refl <- testEquality (regType r0) (LLVMPointerRepr w0)
   , Just Refl <- testEquality (regType r1) (LLVMPointerRepr w1)
   = do let (LLVMPointer _blk off) = regValue r0
        sym <- getSymInterface
        do -- emit a syscall event that just captures the offset value of the r0 register
           mem <- readGlobal mvar
           let i = memCurrentInstr mem
           seq' <- liftIO (consSymSequence sym (SyscallEvent i off) (memSeq mem))
           writeGlobal mvar mem{ memSeq = seq' }

        -- return the registers r0 and r1 unchanged, assume we have no memory effects (!)
        return (Ctx.Empty :> RV (regValue r0) :> RV (regValue r1))


applySyscallModel _rtps _args _syscallModel _mvar =
  fail "applySyscallModel: TODO"


evalMacawExprExtensionTrace :: forall sym bak arch f tp p rtp blocks r ctx ext
                       .  IsSymBackend sym bak
                       => UndefinedPtrOps sym
                       -> bak
                       -> IntrinsicTypes sym
                       -> (Int -> String -> IO ())
                       -> CrucibleState p sym ext rtp blocks r ctx
                       -> (forall utp . f utp -> IO (RegValue sym utp))
                       -> MacawExprExtension arch f tp
                       -> IO (RegValue sym tp)
evalMacawExprExtensionTrace undefptr bak iTypes logFn cst f e0 =
  case e0 of
    PtrToBits _w x  -> doPtrToBits bak undefptr =<< f x
    _ -> evalMacawExprExtension bak iTypes logFn cst f e0

doPtrToBits ::
  (IsSymBackend sym bak, 1 <= w) =>
  bak ->
  UndefinedPtrOps sym ->
  LLVMPtr sym w ->
  IO (SymBV sym w)
doPtrToBits bak mkundef ptr@(LLVMPointer base off) = do
  let sym = backendGetSym bak
  case asNat base of
    Just 0 -> return off
    _ -> do
      cond <- natEq sym base =<< natLit sym 0
      case asConstantPred cond of
        Just True -> return off
        _ -> do
          assert bak cond $ AssertFailureSimError "doPtrToBits" "doPtrToBits"
          undef <- undefPtrOff mkundef sym ptr
          bvIte sym cond off undef

liftToCrucibleState ::
  GlobalVar mem ->
  (sym -> StateT (RegValue sym mem) IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
liftToCrucibleState mvar f cst = do
  mem <- getGlobalVar cst mvar
  (a, mem') <- runStateT (f (cst ^. stateSymInterface)) mem
  pure (a, setGlobalVar cst mvar mem')

readOnlyWithSym ::
  (sym -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
readOnlyWithSym f cst = flip (,) cst <$> f (cst ^. stateSymInterface)

readOnlyWithBak ::
  (forall bak. IsSymBackend sym bak => bak -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
readOnlyWithBak f cst =
  withBackend (cst ^. stateContext) $ \bak ->
    do a <- f bak
       pure (a, cst)

getGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> IO (RegValue sym mem)
getGlobalVar cst gv = case lookupGlobal gv (cst ^. stateTree . actFrame . gpGlobals) of
  Just val -> return val
  Nothing -> fail ("Global variable not initialized: " ++ show gv)

setGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> RegValue sym mem -> CrucibleState s sym ext rtp blocks r ctx
setGlobalVar cst gv val = cst & stateTree . actFrame . gpGlobals %~ insertGlobal gv val

-- | A wrapped function that produces a predicate indicating that two pointer regions are
-- compatible for some pointer operation. If this predicate is false, then the
-- operation is undefined and yields an uninterpreted function.
data RegionConstraint sym =
  RegionConstraint
    {
      regConstraintMsg :: String
    , regConstraintEval :: (sym -> SymNat sym -> SymNat sym  -> IO (Pred sym))
    }

-- | A 'RegionConstraint' that permits pointers from any two regions.
natEqConstraint ::
  IsSymInterface sym =>
  RegionConstraint sym
natEqConstraint = RegionConstraint "both regions must be equal" $ natEq

-- | A 'RegionConstraint' that requires one of the regions to be zero.
someZero ::
  IsSymInterface sym =>
  RegionConstraint sym
someZero = RegionConstraint "one pointer region must be zero" $ \sym reg1 reg2 -> do
  regZero1 <- isZero sym reg1
  regZero2 <- isZero sym reg2
  orPred sym regZero1 regZero2

-- | A 'RegionConstraint' that defines when regions are compatible for subtraction:
-- either the regions are equal or the first region is zero.
compatSub ::
  IsSymInterface sym =>
  RegionConstraint sym
compatSub = RegionConstraint msg $ \sym reg1 reg2 -> do
  regZero1 <- isZero sym reg1
  regEq <- natEq sym reg1 reg2
  orPred sym regZero1 regEq
  where
    msg = "first pointer region must be zero, or both regions must be equal"

ptrOpNR ::
  (1 <= w) =>
  NatRepr w ->
  RegEntry sym (LLVMPointerType w) ->
  RegEntry sym (LLVMPointerType w) ->
  (forall bak. (1 <= w, IsSymBackend sym bak) => bak -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
ptrOpNR _w (RegEntry _ (LLVMPointer region offset)) (RegEntry _ (LLVMPointer region' offset')) f =
  readOnlyWithBak $ \bak ->
    f bak region offset region' offset'

ptrOp ::
  AddrWidthRepr w ->
  RegEntry sym (LLVMPointerType w) ->
  RegEntry sym (LLVMPointerType w) ->
  (forall bak. (1 <= w, IsSymBackend sym bak) => bak -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
ptrOp w (RegEntry _ (LLVMPointer region offset)) (RegEntry _ (LLVMPointer region' offset')) f =
  addrWidthsArePositive w $ readOnlyWithBak $ \bak -> do
    f bak region offset region' offset'

ptrPredOp ::
  IsSymBackend sym bak =>
  UndefinedPtrPredOp sym ->
  RegionConstraint sym ->
  (sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (Pred sym)) ->
  bak -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (Pred sym)
ptrPredOp mkundef regconstraint f bak reg1 off1 reg2 off2  = do
  let sym = backendGetSym bak
  cond <- regConstraintEval regconstraint sym reg1 reg2
  result <- f sym reg1 off1 reg2 off2
  case asConstantPred cond of
    Just True -> return result
    _ -> do
      assert bak cond $ AssertFailureSimError "ptrPredOp" $ "ptrPredOp: " ++ regConstraintMsg regconstraint
      undef <- mkUndefPred mkundef sym (LLVMPointer reg1 off1) (LLVMPointer reg2 off2)
      itePred sym cond result undef

muxPtr ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  IO (LLVMPtr sym w)
muxPtr sym p (LLVMPointer region offset) (LLVMPointer region' offset') = do
  BaseBVRepr _ <- return $ exprType offset
  reg'' <- natIte sym p region region'
  off'' <- bvIte sym p offset offset'
  return $ LLVMPointer reg'' off''

ptrBinOp ::
  IsSymBackend sym bak =>
  UndefinedPtrBinOp sym ->
  RegionConstraint sym ->
  (bak -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (LLVMPtr sym w)) ->
  bak -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (LLVMPtr sym w)
ptrBinOp mkundef regconstraint f bak reg1 off1 reg2 off2 = do
  let sym = backendGetSym bak
  cond <- regConstraintEval regconstraint sym reg1 reg2
  result <- f bak reg1 off1 reg2 off2
  case asConstantPred cond of
    Just True -> return result
    _ -> do
      assert bak cond $ AssertFailureSimError "ptrBinOp" $ "ptrBinOp: " ++ regConstraintMsg regconstraint
      undef <- mkUndefPtr mkundef sym (LLVMPointer reg1 off1) (LLVMPointer reg2 off2)
      muxPtr sym cond result undef

isZero :: IsExprBuilder sym => sym -> SymNat sym -> IO (Pred sym)
isZero sym reg = do
  zero <- natLit sym 0
  natEq sym reg zero

doReadMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (MS.ToCrucibleType ty))
doReadMem sym ptrW ptr memRepr = addrWidthClass ptrW $ do
  mem <- get
  val <- liftIO $ readMemState sym (memState mem) ptr memRepr
  doMemOpInternal sym Read Unconditional ptrW ptr val memRepr
  pure val

doCondReadMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  RegValue sym (MS.ToCrucibleType ty) ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (MS.ToCrucibleType ty))
doCondReadMem sym cond def ptrW ptr memRepr = addrWidthClass ptrW $ do
  mem <- get
  val <- liftIO $ readMemState sym (memState mem) ptr memRepr
  doMemOpInternal sym Read (Conditional cond) ptrW ptr val memRepr
  liftIO $ iteDeep sym cond val def memRepr

doWriteMem ::
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doWriteMem sym = doMemOpInternal sym Write Unconditional

doCondWriteMem ::
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  RegValue sym BoolType ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doCondWriteMem sym cond = doMemOpInternal sym Write (Conditional cond)

ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

-- | Calculate an index into the memory array from a pointer
arrayIdx ::
  1 <= ptrW =>
  IsExprBuilder sym =>
  sym ->
  LLVMPtr sym ptrW ->
  Integer ->
  IO (Assignment (SymExpr sym) (EmptyCtx ::> BaseIntegerType ::> BaseBVType ptrW))
arrayIdx sym ptr@(LLVMPointer reg off) off' = do
  let w = ptrWidth ptr
  offBV <- bvLit sym w $ BV.mkBV w off'
  bvIdx <- bvAdd sym off offBV
  ireg <- natToInteger sym reg
  return $ Empty :> ireg :> bvIdx

concatPtrs ::
  1 <= w1 =>
  1 <= w2 =>
  IsExprBuilder sym =>
  sym ->
  Endianness ->
  LLVMPtr sym w1 ->
  LLVMPtr sym w2 ->
  IO (LLVMPtr sym (w1 + w2))
concatPtrs sym endianness (LLVMPointer reg1 off1) (LLVMPointer _ off2) = do
  bv <- case endianness of
    BigEndian -> bvConcat sym off1 off2
    LittleEndian -> do
      Refl <- return $ plusComm (bvWidth off1) (bvWidth off2)
      bvConcat sym off2 off1
  return $ LLVMPointer reg1 bv

-- | Annotate nat proofs with the associated inequality that
-- is being proven to provide documentation about
-- each proof step.
proveLeq :: forall c n m. c ~ (n <= m) => LeqProof n m -> LeqProof n m
proveLeq prf@LeqProof = prf

-- | Take 1 byte from either the front or back of the
-- given bitvector, according to the given endianness
chunkBV :: forall sym w.
  1 <= w =>
  2 <= w =>
  IsExprBuilder sym =>
  sym ->
  Endianness ->
  NatRepr w ->
  SymBV sym (8 * w) ->
  IO (SymBV sym 8, SymBV sym (8 * (w-1)))
chunkBV sym endianness w bv
  | LeqProof <- proveLeq @(1 <= (w-1))
      $ leqSub2 (leqProof (knownNat @2) w) (leqRefl (knownNat @1))
  , sz' <- natMultiply (knownNat @8) (decNat w)
  , LeqProof <- proveLeq @(1 <= (8 * (w-1)))
      $ mulMono (knownNat @8) (decNat w)
  , _1_le_w <- leqProof (knownNat @1) w
  , _8_le_8 <- leqRefl (knownNat @8)
  , LeqProof  <- proveLeq @(8 <= (w * 8))
      $ leqMulCongr _1_le_w _8_le_8
  , Refl <- mulComm (knownNat @8) w
  , Refl <- mulComm (knownNat @8) (decNat w)
  , Refl <- lemmaMul (knownNat @8) w
  , Refl <- plusComm (knownNat @8) sz' = do
    case endianness of
      -- take from the least significant bits
      LittleEndian -> do
        hd <- bvSelect sym (knownNat @0) (knownNat @8) bv
        tl <- bvSelect sym (knownNat @8) sz' bv
        return (hd, tl)
      -- take from the most significant bits
      BigEndian
        | _w_1_le_w <- leqSub (leqRefl w) _1_le_w
        , LeqProof <- proveLeq @(8 * (w-1) <= (8 * w))
            $ leqMulCongr _w_1_le_w _8_le_8  -> do
        hd <- bvSelect sym sz' (knownNat @8) bv
        tl <- bvSelect sym (knownNat @0) sz' bv
        return (hd, tl)

-- | Read a packed value from the underlying array (without adding to the read trace)
readMemState :: forall sym ptrW ty.
  1 <= ptrW =>
  IsExprBuilder sym =>
  sym ->
  MemTraceState sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (MS.ToCrucibleType ty))
readMemState sym mem ptr repr = go 0 repr
  where
  go :: Integer -> MemRepr ty' -> IO (RegValue sym (MS.ToCrucibleType ty'))
  go n (BVMemRepr byteWidth endianness) =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl
        | Refl <- zeroSubEq byteWidth (knownNat @1) -> do
          (_ Ctx.:> reg Ctx.:> off) <- arrayIdx sym ptr n
          regArray <- arrayLookup sym (memArr mem) (Ctx.singleton reg)
          content <- arrayLookup sym regArray (Ctx.singleton off)
          blk0 <- natLit sym 0
          return $ LLVMPointer blk0 content
      Right LeqProof
        | byteWidth' <- decNat byteWidth
        , tailRepr <- BVMemRepr byteWidth' endianness
        , headRepr <- BVMemRepr (knownNat @1) endianness
        , Refl <- lemmaMul (knownNat @8) byteWidth
        , Refl <- mulComm (knownNat @8) byteWidth'
        , Refl <- mulComm (knownNat @8) byteWidth
        , LeqProof <- mulMono (knownNat @8) byteWidth' -> do
          hd <- go n headRepr
          tl <- go (n + 1) tailRepr
          concatPtrs sym endianness hd tl

  go _n (FloatMemRepr _infoRepr _endianness) = fail "creating fresh float values not supported in freshRegValue"

  go n (PackedVecMemRepr countRepr recRepr) = V.generateM (fromInteger (intValue countRepr)) $ \i ->
      go (n + memReprByteSize recRepr * fromIntegral i) recRepr

-- | Compute the updated memory state resulting from writing a value to the given address, without
-- accumulating any trace information.
writeMemState ::
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  RegValue sym BoolType ->
  MemTraceState sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  RegValue sym (MS.ToCrucibleType ty) ->
  IO (MemTraceState sym ptrW)
writeMemState sym cond memSt ptr repr val = do
  sq <- nilSymSequence sym
  let mem = MemTraceImpl sq memSt (toMuxTree sym Nothing)
  MemTraceImpl _ memSt' _ <- execStateT (doMemOpInternal sym Write (Conditional cond) (addrWidthRepr mem) ptr val repr) mem
  return memSt'

-- | Write to the memory array and set the dirty bits on
-- any written addresses
writeMemBV :: forall sym ptrW w.
  1 <= ptrW =>
  IsExprBuilder sym =>
  sym ->
  MemTraceState sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr (MT.BVType w) ->
  SymBV sym w ->
  IO (MemTraceState sym ptrW)
writeMemBV sym mem_init ptr repr val = go 0 repr val mem_init
  where
  go ::
    Integer ->
    MemRepr (MT.BVType w') ->
    SymBV sym w' ->
    MemTraceState sym ptrW ->
    IO (MemTraceState sym ptrW)
  go n (BVMemRepr byteWidth endianness) bv mem =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl -> do
        (_ Ctx.:> reg Ctx.:> off) <- arrayIdx sym ptr n
        Refl <- return $ zeroSubEq byteWidth (knownNat @1)
        regArray <- arrayLookup sym (memArr mem) (Ctx.singleton reg)
        regArray' <- arrayUpdate sym regArray (Ctx.singleton off) bv
        arr <- arrayUpdate sym (memArr mem) (Ctx.singleton reg) regArray'
        return $ mem { memArr = arr }
      Right LeqProof -> do
        let
          byteWidth' = decNat byteWidth
          repr' = BVMemRepr byteWidth' endianness
          reprHead = BVMemRepr (knownNat @1) endianness
        LeqProof <- return $ oneSubEq byteWidth
        (hd, tl) <- chunkBV sym endianness byteWidth bv
        mem1 <- go n reprHead hd mem
        go (n + 1) repr' tl mem1

ifCond ::
  IsSymInterface sym =>
  sym ->
  MemOpCondition sym ->
  SymExpr sym tp ->
  SymExpr sym tp ->
  IO (SymExpr sym tp)
ifCond _ Unconditional eT _ = return eT
ifCond sym (Conditional p) eT eF = baseTypeIte sym p eT eF

doMemOpInternal :: forall sym ptrW ty.
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  MemOpDirection ->
  MemOpCondition sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doMemOpInternal sym dir cond ptrW = go where
  go :: LLVMPtr sym ptrW -> RegValue sym (MS.ToCrucibleType ty') -> MemRepr ty' -> StateT (MemTraceImpl sym ptrW) IO ()
  go ptr@(LLVMPointer reg off) regVal = \case
    repr@(BVMemRepr byteWidth endianness)
      | LeqProof <- mulMono (knownNat @8) byteWidth
      -> addrWidthsArePositive ptrW $ do

      do mem <- get
         seq' <- liftIO (consSymSequence sym (MemOpEvent (MemOp ptr dir cond byteWidth regVal endianness)) (memSeq mem))
         put mem{ memSeq = seq' }

      case dir of
        Read -> return ()
        Write -> do
          LLVMPointer _ rawBv <- return regVal
          mem <- get
          memSt' <- liftIO $ writeMemBV sym (memState mem) ptr repr rawBv
          arr <- liftIO $ ifCond sym cond (memArr $ memSt') (memArr $ memState mem)
          put $ mem { memState = MemTraceState arr }
    FloatMemRepr _infoRepr _endianness -> fail "reading floats not supported in doMemOpInternal"
    PackedVecMemRepr _countRepr recRepr -> addrWidthsArePositive ptrW $ do
      elemSize <- liftIO $ bvLit sym ptrWidthNatRepr (BV.mkBV ptrWidthNatRepr (memReprByteSize recRepr))
      flip V.imapM_ regVal $ \i recRegVal -> do
        off' <- liftIO $ do
          symbolicI <- bvLit sym ptrWidthNatRepr (BV.mkBV ptrWidthNatRepr (toInteger i))
          dOff <- bvMul sym symbolicI elemSize
          bvAdd sym off dOff
        go (LLVMPointer reg off') recRegVal recRepr

  ptrWidthNatRepr = addrWidthNatRepr ptrW

iteDeep ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  RegValue sym (MS.ToCrucibleType ty) ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  IO (RegValue sym (MS.ToCrucibleType ty))
iteDeep sym cond t f = \case
  BVMemRepr byteWidth _endianness -> let
    bitWidth = natMultiply (knownNat @8) byteWidth
    LLVMPointer treg toff = t
    LLVMPointer freg foff = f
    in multiplicationIsMonotonic @8 bitWidth
    $ liftA2 LLVMPointer (natIte sym cond treg freg) (bvIte sym cond toff foff)
  FloatMemRepr _infoRepr _endianness -> fail "ite on floats not supported in iteDeep"
  PackedVecMemRepr countRepr recRepr -> V.generateM (fromInteger (intValue countRepr)) $ \i ->
    iteDeep sym cond (t V.! i) (f V.! i) recRepr

addrWidthsArePositive :: AddrWidthRepr w -> (1 <= w => a) -> a
addrWidthsArePositive Addr32 a = a
addrWidthsArePositive Addr64 a = a


multiplicationIsMonotonic :: forall x w a. (1 <= x, 1 <= w) => NatRepr (x*w) -> (1 <= x*w => a) -> a
multiplicationIsMonotonic xw a = case compareNat (knownNat @0) xw of
  NatLT _ -> a
  _ -> error $ "The impossible happened: 1 <= x and 1 <= w, but x*w = " ++ show (natValue xw) ++ " and 1 > x*w"

memReprByteSize :: MemRepr ty -> Integer
memReprByteSize (BVMemRepr byteWidth _) = intValue byteWidth
memReprByteSize (FloatMemRepr _ _) = error "byte size of floats not supported in memReprByteSize"
memReprByteSize (PackedVecMemRepr countRepr recRepr) = intValue countRepr * memReprByteSize recRepr

ioSolverSymbol :: String -> IO SolverSymbol
ioSolverSymbol = either (fail . show) pure . userSymbol

ioFreshConstant :: IsSymExprBuilder sym => sym -> String -> BaseTypeRepr tp -> IO (SymExpr sym tp)
ioFreshConstant sym nm ty = do
  symbol <- ioSolverSymbol nm
  freshConstant sym symbol ty

--------------------------------------------------------
-- Axioms on type-level naturals

mulMono :: forall p q x w. (1 <= x, 1 <= w) => p x -> q w -> LeqProof 1 (x*w)
mulMono _x w = unsafeCoerce (leqRefl w)

zeroSubEq :: forall p q w n. 0 ~ (w - n) => p w -> q n -> w :~: n
zeroSubEq _w _n = unsafeCoerce Refl

oneSubEq :: forall p w. 1 <= w => 1 <= (w - 1) => p w -> LeqProof 2 w
oneSubEq w = unsafeCoerce (leqRefl w)

--------------------------------------------------------
-- Equivalence check


-- | A wrapped value indicating that the given memory address has been modified
-- by a given write sequence, with a given word size (in bytes)
data MemFootprint sym ptrW where
  MemFootprint ::
    1 <= w =>
    LLVMPtr sym ptrW ->
    NatRepr w ->
    MemOpDirection ->
    MemOpCondition sym ->
    Endianness ->
    MemFootprint sym ptrW


instance TestEquality (SymExpr sym) => Eq (MemFootprint sym ptrW) where
  (MemFootprint (LLVMPointer reg1 off1) sz1 dir1 cond1 end1) == (MemFootprint (LLVMPointer reg2 off2) sz2 dir2 cond2 end2)
   | reg1 == reg2
   , Just Refl <- testEquality off1 off2
   , Just Refl <- testEquality sz1 sz2
   = cond1 == cond2 && dir1 == dir2 && end1 == end2
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemFootprint sym ptrW) where
  compare (MemFootprint (LLVMPointer reg1 off1) sz1 dir1 cond1 end1) (MemFootprint (LLVMPointer reg2 off2) sz2 dir2 cond2 end2) =
    compare dir1 dir2 <>
    (compare reg1 reg2) <>
    (toOrdering $ compareF off1 off2) <>
    (toOrdering $ compareF sz1 sz2) <>
    compare cond1 cond2 <>
    compare end1 end2


memOpFootprint ::
  IsExprBuilder sym =>
  sym ->
  MemOp sym ptrW ->
  (MemFootprint sym ptrW, Pred sym)
memOpFootprint sym (MemOp ptr dir cond w _ end) =
  (MemFootprint ptr w dir Unconditional end, getCond sym cond)

unionFootprintMap ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  Map (MemFootprint sym ptrW) (Pred sym) ->
  Map (MemFootprint sym ptrW) (Pred sym) ->
  IO (Map (MemFootprint sym ptrW) (Pred sym))
unionFootprintMap sym =
  Map.mergeA
    Map.preserveMissing
    Map.preserveMissing
    (Map.zipWithAMatched (\_k p1 p2 -> orPred sym p1 p2))

muxFootprintMap ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  Pred sym ->
  Map (MemFootprint sym ptrW) (Pred sym) ->
  Map (MemFootprint sym ptrW) (Pred sym) ->
  IO (Map (MemFootprint sym ptrW) (Pred sym))
muxFootprintMap sym p =
  Map.mergeA
    (Map.traverseMissing (\_k x -> andPred sym x p))
    (Map.traverseMissing (\_k y -> andPred sym y =<< notPred sym p))
    (Map.zipWithAMatched (\_k x y -> itePred sym p x y))

-- This is basically an internal function called
-- from "trace footprint", but is broken out here.
-- The "Const" in the return type is an artifact
-- of how the evalWithFreshCache operator works,
-- as it requires an applicative functor over
-- the sequence type.
--
-- We compute on the intermediate Map type because
-- it is more convenient for computing mux and union
-- operations than @Set Footprint@ type that is eventually
-- returned by `traceFootprint`.
traceFootprintMap ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  MemTraceSeq sym ptrW ->
  IO (Const (Map (MemFootprint sym ptrW) (Pred sym)) (MemEvent sym ptrW))
traceFootprintMap sym =
  evalWithFreshCache $ \rec -> \case
    SymSequenceNil -> return (Const mempty)

    SymSequenceCons _ (MemOpEvent x) xs ->
      do let (fp,p) = memOpFootprint sym x
         let m1 = Map.insert fp p mempty
         Const m2 <- rec xs
         Const <$> unionFootprintMap sym m1 m2
    SymSequenceCons _ _ xs -> rec xs

    SymSequenceAppend _ xs ys ->
      do Const m1 <- rec xs
         Const m2 <- rec ys
         Const <$> unionFootprintMap sym m1 m2

    SymSequenceMerge _ p xs ys ->
      do Const m1 <- rec xs
         Const m2 <- rec ys
         Const <$> muxFootprintMap sym p m1 m2


-- | Compute the set of "footprint" values
--   that correspond to the reads and writes
--   generated by this trace memory.
traceFootprint ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  MemTraceImpl sym ptrW ->
  IO (Set (MemFootprint sym ptrW))
traceFootprint sym mem = do
   do Const m <- traceFootprintMap sym (memSeq mem)
      let xs = do (MemFootprint ptr w dir _ end, cond) <- Map.toList m
                  case asConstantPred cond of
                    Nothing    -> [MemFootprint ptr w dir (Conditional cond) end]
                    Just True  -> [MemFootprint ptr w dir Unconditional end]
                    Just False -> []
      return $ Set.fromList xs


-- | Filter the memory event traces to leave just the observable
--   events.  This currently includes all system call events,
--   and includes memory operations that are deemed observable
--   by the given filtering predicate.
observableEvents ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  (MemOp sym ptrW -> IO (Pred sym)) ->
  MemTraceImpl sym ptrW ->
  IO (SymSequence sym (MemEvent sym ptrW))
observableEvents sym opIsObservable mem = evalWithFreshCache f (memSeq mem)
  where
   filterEvent x xs =
     case x of
       -- always include system call events
       SyscallEvent{} -> consSymSequence sym x xs

       -- Include memory operations only if they acutally
       -- happen (their condition is true) and if they are
       -- deemed observable by the given filtering function.
       MemOpEvent op@(MemOp ptr dir cond w val end) ->
         do opObservable <- opIsObservable op
            p <- andPred sym opObservable (getCond sym cond)
            let x' = MemOpEvent (MemOp ptr dir Unconditional w val end)
            iteM muxSymSequence sym p (consSymSequence sym x' xs) (return xs)

   f _rec SymSequenceNil = nilSymSequence sym

   f rec (SymSequenceCons _ x xs) =
     do xs' <- rec xs
        filterEvent x xs'

   f rec (SymSequenceAppend _ xs ys) =
     do xs' <- rec xs
        ys' <- rec ys
        appendSymSequence sym xs' ys'

   f rec (SymSequenceMerge _ p xs ys) =
     do xs' <- rec xs
        ys' <- rec ys
        muxSymSequence sym p xs' ys'


-- | Get an unordered collection of all the read memory operations
--   that occurred in this trace memory. Control-flow conditions are
--   dropped while constructing this set, so the conditions included
--   on these `MemOp` values may not be accurate.
--
--   Note: We could modify this so that it correctly incorporates
--   merge conditions, but doing so is a bit tricky, and the only
--   current use site (validConcreteReads) ignores the conditions
--   anyway.  I would have preferred to migrate validConcreteReads
--   into this module, but that is difficult because it creates
--   a module import cycle, and I wasn't prepared to relocate
--   things enough to fix it.
getReadOps ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  MemTraceImpl sym ptrW ->
  IO (Set (MemOp sym ptrW))
getReadOps _sym mem =
  getConst <$> evalWithFreshCache (\rec -> \case
    SymSequenceNil -> return (Const mempty)
    SymSequenceCons _ x xs ->
      do Const s <- rec xs
         case x of
           MemOpEvent op@(MemOp _ptr Read _ _ _ _) -> return (Const (Set.insert op s))
           _ -> return (Const s)
    SymSequenceAppend _ xs ys ->
      do Const s1 <- rec xs
         Const s2 <- rec ys
         return (Const (Set.union s1 s2))
    SymSequenceMerge _ _p xs ys ->
      do Const s1 <- rec xs
         Const s2 <- rec ys
         return (Const (Set.union s1 s2)))
   (memSeq mem)

llvmPtrEq ::
  IsExprBuilder sym =>
  sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  IO (Pred sym)
llvmPtrEq sym (LLVMPointer region offset) (LLVMPointer region' offset') = do
  regionsEq <- natEq sym region region'
  offsetsEq <- isEq sym offset offset'
  andPred sym regionsEq offsetsEq

getCond ::
  IsExprBuilder sym =>
  sym ->
  MemOpCondition sym ->
  Pred sym
getCond sym Unconditional = truePred sym
getCond _sym (Conditional p) = p


-- | Memory states are equivalent everywhere but the given region.
memEqOutsideRegion ::
  forall sym ptrW.
  IsExprBuilder sym =>
  sym ->
  SymNat sym ->
  MemTraceState sym ptrW ->
  MemTraceState sym ptrW ->
  IO (Pred sym)
memEqOutsideRegion sym region mem1 mem2 = do
  iRegion <- natToInteger sym region
  mem1Stack <- arrayLookup sym (memArr mem1) (Ctx.singleton iRegion)
  mem2' <- arrayUpdate sym (memArr mem2) (Ctx.singleton iRegion) mem1Stack
  isEq sym (memArr mem1) mem2'


-- | Memory states are equivalent in the given region.
memEqAtRegion ::
  forall sym ptrW.
  IsExprBuilder sym =>
  sym ->
  -- | stack memory region
  SymNat sym ->
  MemTraceState sym ptrW ->
  MemTraceState sym ptrW ->
  IO (Pred sym)
memEqAtRegion sym stackRegion mem1 mem2 = do
  iStackRegion <- natToInteger sym stackRegion
  mem1Stack <- arrayLookup sym (memArr mem1) (Ctx.singleton iStackRegion)
  mem2Stack <- arrayLookup sym (memArr mem2) (Ctx.singleton iStackRegion)
  isEq sym mem1Stack mem2Stack


-- | Memory states are exactly equivalent.
memEqExact ::
  forall sym ptrW.
  IsExprBuilder sym =>
  sym ->
  MemTraceState sym ptrW ->
  MemTraceState sym ptrW ->
  IO (Pred sym)
memEqExact sym mem1 mem2 = isEq sym (memArr mem1) (memArr mem2)

instance PEM.ExprMappable sym (MemOpCondition sym) where
  mapExpr _sym f = \case
    Conditional p -> Conditional <$> f p
    Unconditional -> return Unconditional

instance PEM.ExprMappable sym (MemOp sym w) where
  mapExpr sym f = \case
    MemOp ptr dir cond w val endian -> do
      ptr' <- WEH.mapExprPtr sym f ptr
      val' <- WEH.mapExprPtr sym f val
      cond' <- PEM.mapExpr sym f cond
      return $ MemOp ptr' dir cond' w val' endian

instance PEM.ExprMappable sym (MemEvent sym w) where
  mapExpr sym f = \case
    MemOpEvent op -> MemOpEvent <$> PEM.mapExpr sym f op
    SyscallEvent i arg -> SyscallEvent i <$> f arg -- TODO? rewrite the mux tree?

instance PEM.ExprMappable sym a => PEM.ExprMappable sym (SymSequence sym a) where
  mapExpr sym f = evalWithFreshCache $ \rec -> \case
    SymSequenceNil -> nilSymSequence sym
    SymSequenceCons _ x xs ->
      do x'  <- PEM.mapExpr sym f x
         xs' <- rec xs
         consSymSequence sym x' xs'
    SymSequenceAppend _ xs ys ->
     do xs' <- rec xs
        ys' <- rec ys
        appendSymSequence sym xs' ys'
    SymSequenceMerge _ p xs ys ->
     do p' <- f p
        iteM muxSymSequence sym p' (rec xs) (rec ys)

instance PEM.ExprMappable sym (MemTraceImpl sym w) where
  mapExpr sym f mem = do
    memSeq' <- PEM.mapExpr sym f (memSeq mem)
    memState' <- PEM.mapExpr sym f $ memState mem
    let memInstr' =  memCurrentInstr mem -- TODO? rewrite the mux tree?
                                         -- I expect it to basically never be interesting
                                         -- to do this...
    return $ MemTraceImpl memSeq' memState' memInstr'

instance PEM.ExprMappable sym (MemTraceState sym w) where
  mapExpr _sym f memSt = do
    memArr' <- f $ memArr memSt
    return $ MemTraceState memArr'
  foldExpr _sym f memSt b = f (memArr memSt) b

instance PEM.ExprMappable sym (MemFootprint sym arch) where
  mapExpr sym f (MemFootprint ptr w dir cond end) = do
    ptr' <- WEH.mapExprPtr sym f ptr
    cond' <- PEM.mapExpr sym f cond
    return $ MemFootprint ptr' w dir cond' end
