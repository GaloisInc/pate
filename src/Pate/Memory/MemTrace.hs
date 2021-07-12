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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyCase #-}


#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}



module Pate.Memory.MemTrace where

import Unsafe.Coerce
import           Data.Foldable
import           Control.Applicative
import           Control.Lens ((%~), (&), (^.))
import           Control.Monad.State
import qualified Data.BitVector.Sized as BV
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import           Data.IORef
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.TypeNats (KnownNat, type Nat)

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as VF

import qualified Data.Macaw.Types as MT
import Data.Macaw.CFG.AssignRhs (ArchAddrWidth, MemRepr(..))
import Data.Macaw.Memory (AddrWidthRepr(..), Endianness(..), MemWidth, addrWidthClass, addrWidthNatRepr, addrWidthRepr, memWidthNatRepr)
import Data.Macaw.Symbolic.Backend (MacawEvalStmtFunc, MacawArchEvalFn(..))
import Data.Macaw.Symbolic ( MacawStmtExtension(..), MacawExprExtension(..), MacawExt
                           , GlobalMap, MacawSimulatorState(..)
                           , IsMemoryModel(..)
                           , SymArchConstraints
                           , evalMacawExprExtension
                           )
import qualified Data.Macaw.Symbolic as MS

import Data.Macaw.Symbolic.MemOps ( doGetGlobal )

import Data.Parameterized.Context (pattern (:>), pattern Empty)
import qualified Data.Parameterized.Map as MapF
import Data.Text (pack)
import Lang.Crucible.Backend (IsSymInterface, assert)
import Lang.Crucible.CFG.Common (GlobalVar, freshGlobalVar)
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM.Bytes (Bytes, bitsToBytes, bytesToInteger)
import Lang.Crucible.LLVM.MemModel (LLVMPointerType, LLVMPtr, pattern LLVMPointer, llvmPointer_bv)
import Lang.Crucible.Simulator.ExecutionTree (CrucibleState, ExtensionImpl(..), actFrame, gpGlobals, stateSymInterface, stateTree)
import Lang.Crucible.Simulator.GlobalState (insertGlobal, lookupGlobal)
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass(..), IntrinsicMuxFn(..), IntrinsicTypes)
import Lang.Crucible.Simulator.RegMap (RegEntry(..))
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Types ((::>), BoolType, BVType, EmptyCtx, IntrinsicType, SymbolicArrayType,
                            SymbolRepr, TypeRepr(BVRepr), MaybeType, knownSymbol)
import What4.Expr.Builder (ExprBuilder)
import What4.Interface


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
data UndefinedPtrOps sym ptrW =
  UndefinedPtrOps
    { undefPtrOff :: (forall w. sym -> LLVMPtr sym w -> IO (SymBV sym w))
    , undefPtrLt :: UndefinedPtrPredOp sym
    , undefPtrLeq :: UndefinedPtrPredOp sym
    , undefPtrAdd :: UndefinedPtrBinOp sym
    , undefPtrSub :: UndefinedPtrBinOp sym
    , undefPtrAnd :: UndefinedPtrBinOp sym
    , undefPtrXor :: UndefinedPtrBinOp sym
    , undefWriteSize :: forall valW. sym -> LLVMPtr sym valW -> SymBV sym ptrW -> IO (SymBV sym ptrW)
    -- ^ arguments are the value being written and the index of the byte within that value being written
    , undefMismatchedRegionRead :: sym -> LLVMPtr sym ptrW -> SymBV sym ptrW -> IO (SymBV sym 8)   
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
  | UndefWriteSize
  | UndefRegionRead
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

natAbsBVFixed :: 1 <= w => NatRepr w -> NatRepr w' -> (NatAbs (BaseBVType w) w' :~: BaseBVType w)
natAbsBVFixed _ _ = unsafeCoerce Refl

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

mkPtrBVUF ::
  forall ptrW sym.
  IsSymInterface sym =>
  KnownNat ptrW =>
  1 <= ptrW =>
  UndefPtrOpTag ->
  PolyFunMaker sym (EmptyCtx ::> BasePtrType AnyNat ::> BaseBVType ptrW) (BaseBVType ptrW)
mkPtrBVUF tag = PolyFunMaker $ \sym w ->
  case natAbsBVFixed (knownNat @ptrW) w of
    Refl -> do
      let
        ptrRepr = BaseStructRepr (Empty :> BaseIntegerRepr :> BaseBVRepr w)
        repr = Empty :> ptrRepr :> BaseBVRepr (knownNat @ptrW)
      c <- freshConstant sym (polySymbol tag w) (BaseArrayRepr (flattenStructRepr repr) (BaseBVRepr (knownNat @ptrW)))
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
withPtrWidth _ _ = error "impossible"

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
  forall sym ptrW.
  IsSymInterface sym =>
  KnownNat ptrW =>
  1 <= ptrW =>
  sym ->
  IO (UndefinedPtrOps sym ptrW)
mkUndefinedPtrOps sym = do
  (PolyFunMaker offFn, classOff) <- cachedPolyFun sym $ mkOffUF UndefPtrOff
  let
    offPtrFn :: forall w. sym -> LLVMPtr sym w -> IO (SymBV sym w)
    offPtrFn sym'  ptr = withPtrWidth ptr $ \w -> do
      sptr <- asSymPtr sym' ptr
      resultfn <- offFn sym' w
      applyPolyFun resultfn (Empty :> sptr)
    ptrW :: NatRepr ptrW
    ptrW = knownNat @ptrW
    ptrRepr = BaseStructRepr (Empty :> BaseIntegerRepr :> BaseBVRepr ptrW)
    
  (PolyFunMaker undefWriteFn, classWrite) <- cachedPolyFun sym $ mkPtrBVUF @ptrW UndefWriteSize

  let
    undefWriteFn' :: forall valW. sym -> LLVMPtr sym valW -> SymBV sym ptrW -> IO (SymBV sym ptrW)
    undefWriteFn' sym' ptr bv = withPtrWidth ptr $ \w -> do
      sptr <- asSymPtr sym' ptr
      resultfn <- undefWriteFn sym' w
      Refl <- return $ natAbsBVFixed ptrW w
      applyPolyFun resultfn (Empty :> sptr :> bv)

    undefReadRepr = Empty :> ptrRepr :> BaseBVRepr ptrW
  
  undefReadFn <- freshConstant sym (polySymbol UndefRegionRead ptrW)
    (BaseArrayRepr (flattenStructRepr undefReadRepr) (BaseBVRepr (knownNat @8)))

  

  let
    undefReadFn' :: sym -> LLVMPtr sym ptrW -> SymBV sym ptrW -> IO (SymBV sym 8)
    undefReadFn' sym' ptr bv = do
      sptr <- asSymPtr sym' ptr
      arrayLookup sym undefReadFn =<< flattenStructs sym (Empty :> sptr :> bv)

    classRead :: UndefPtrClassify sym
    classRead = mkClassify UndefRegionRead undefReadFn

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
      , undefWriteSize = undefWriteFn'
      , undefMismatchedRegionRead = undefReadFn'
      , undefPtrClassify = mconcat [classOff, classLt, classLeq, classAdd, classSub, classAnd, classXor, classWrite, classRead]
      }

-- * Memory trace model

-- | Like 'macawExtensions', but with an alternative memory model that records
-- memory operations without trying to carefully guess the results of
-- performing them.
macawTraceExtensions ::
  (IsSymInterface sym, SymArchConstraints arch, sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn sym (MemTrace arch) arch ->
  GlobalVar (MemTrace arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  UndefinedPtrOps sym (ArchAddrWidth arch) ->
  ExtensionImpl (MacawSimulatorState sym) sym (MacawExt arch)
macawTraceExtensions archStmtFn mvar globs undefptr =
  ExtensionImpl
    { extensionEval = evalMacawExprExtensionTrace undefptr
    , extensionExec = execMacawStmtExtension archStmtFn undefptr mvar globs
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
  MergeOps ::
    Pred sym ->
    MemTraceSeq sym ptrW ->
    MemTraceSeq sym ptrW ->
    MemOp sym ptrW

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
  MergeOps p opsT opsF == MergeOps p' opsT' opsF'
    | Just Refl <- testEquality p p'
    = opsT == opsT' && opsF == opsF'
  _ == _ = False

data MemTraceImpl sym ptrW = MemTraceImpl
  { memSeq :: MemTraceSeq sym ptrW
  -- ^ the sequence of memory operations in execution order
  , memArr :: MemTraceBytes sym ptrW
  -- ^ the logical contents of memory
  }

-- | 'MemTraceByte' is the struct that we store to describe a single byte of
-- memory. We want to be able to reconstruct pointers when we read back out of
-- this thing, so we have to store a bit more information than just the byte
-- that's in memory. (In fact, we don't even store what byte goes there!)
--
-- Two of the fields in the struct come from an LLVMPointer, and one is
-- metadata. The 'mtbSubOff' field is an index into the bytes of the pointer
-- that the given region+offset decodes to (0 means the LSB, ptrW/8-1 is the
-- MSB).
--
-- Writing is straightforward. But reading is a bit tricky -- we sort of rely
-- on the normal pattern being that entire pointers are read in one operation.
-- When they are, we check that their region+offset all match each other and
-- that the indices go 0, 1, 2, .... If they don't, we either use a descriptive
-- uninterpreted function or drop the result into region 0, depending on
-- exactly how they're mismatched.
data MemTraceByte sym w = MemTraceByte
  { mtbRegion :: SymInteger sym
  , mtbOffset :: SymBV sym w
  , mtbSubOff :: SymBV sym w
  }

muxMemTraceByte :: IsExprBuilder sym =>
  sym -> Pred sym ->
  MemTraceByte sym w -> MemTraceByte sym w -> IO (MemTraceByte sym w)
muxMemTraceByte sym p t f = pure MemTraceByte
  <*> baseTypeIte sym p (mtbRegion t) (mtbRegion f)
  <*> baseTypeIte sym p (mtbOffset t) (mtbOffset f)
  <*> baseTypeIte sym p (mtbSubOff t) (mtbSubOff f)

-- | Checks whether the two bytes are identical, that is, come from the same
-- region, offset, and suboffset. This is stronger than semantic equality,
-- where for each argument we notionally first decode the region+offset to an
-- actual word, then look at some part of the decoded word.
mtbIdentical :: IsExprBuilder sym =>
  sym -> MemTraceByte sym w -> MemTraceByte sym w -> IO (Pred sym)
mtbIdentical sym mtb1 mtb2 = WEH.allPreds sym =<< sequence
  [ isEq sym (mtbRegion mtb1) (mtbRegion mtb2)
  , isEq sym (mtbOffset mtb1) (mtbOffset mtb2)
  , isEq sym (mtbSubOff mtb1) (mtbSubOff mtb2)
  ]

-- | Check whether two bytes are semantically equal, that is, if after looking
-- up the word associated with their region, adding their offset, and then
-- picking out the byte at index suboffset, we get the same resulting byte.
mtbEq :: (1 <= w, 9 <= w, IsExprBuilder sym) =>
  sym -> MemTraceByte sym w -> MemTraceByte sym w -> IO (Pred sym)
mtbEq sym mtb1 mtb2 = do
  byte1 <- bvLshr sym (mtbOffset mtb1) (mtbSubOff mtb1) >>= bvTrunc sym (knownNat @8)
  byte2 <- bvLshr sym (mtbOffset mtb2) (mtbSubOff mtb2) >>= bvTrunc sym (knownNat @8)
  eqBytes <- isEq sym byte1 byte2
  eqRegs <- isEq sym (mtbRegion mtb1) (mtbRegion mtb2)
  andPred sym eqBytes eqRegs


-- | A data structure that conceptually represents memory; that is, a mapping
-- from a (symbolic) region+offset to a 'MemTraceByte'.
--
-- Currently, that mapping is implemented as three symbolic arrays, one for
-- each field of 'MemTraceByte', but that is subject to change.
data MemTraceBytes sym w = MemTraceBytes
  { mtbRegions :: MemArrBase sym w BaseIntegerType
  , mtbOffsets :: MemArrBase sym w (BaseBVType w)
  , mtbSubOffs :: MemArrBase sym w (BaseBVType w)
  }

muxMemTraceBytes :: IsExprBuilder sym =>
  sym -> Pred sym ->
  MemTraceBytes sym w -> MemTraceBytes sym w -> IO (MemTraceBytes sym w)
muxMemTraceBytes sym p t f = pure MemTraceBytes
  <*> baseTypeIte sym p (mtbRegions t) (mtbRegions f)
  <*> baseTypeIte sym p (mtbOffsets t) (mtbOffsets f)
  <*> baseTypeIte sym p (mtbSubOffs t) (mtbSubOffs f)

-- | The lowest-level way to read a byte from our memory implementation; it
-- does no sanity checks at all, simply returning the contents of the symbolic
-- array as-is.
readMemTraceByte :: (MemWidth w, IsExprBuilder sym) =>
  sym -> LLVMPtr sym w -> MemTraceBytes sym w -> IO (MemTraceByte sym w)
readMemTraceByte sym ptr mtbs = head <$> readMemTraceByteMany sym ptr 1 mtbs

-- | Like 'readMemTraceByte', but read many consecutive bytes. This is more
-- efficient than calling 'readMemTraceByte' in a loop.
readMemTraceByteMany :: (MemWidth w, IsExprBuilder sym) =>
  sym -> LLVMPtr sym w -> Integer -> MemTraceBytes sym w -> IO [MemTraceByte sym w]
readMemTraceByteMany sym (LLVMPointer reg off) n mtbs = do
  reg' <- Ctx.singleton <$> natToInteger sym reg
  regs <- arrayLookup sym (mtbRegions mtbs) reg'
  offs <- arrayLookup sym (mtbOffsets mtbs) reg'
  subs <- arrayLookup sym (mtbSubOffs mtbs) reg'

  forM [0 .. n-1] $ \doff -> do
    off' <- pure . Ctx.singleton =<< bvAdd sym off =<< bvFromInteger sym (bvWidth off) doff
    pure MemTraceByte
      <*> arrayLookup sym regs off'
      <*> arrayLookup sym offs off'
      <*> arrayLookup sym subs off'

-- | The lowest-level way to write a byte to our memory implementation; it does
-- no sanity checks at all, simply inserting the given byte fields into the
-- symbolic array as-is.
writeMemTraceByte :: IsExprBuilder sym =>
  sym -> LLVMPtr sym w -> MemTraceByte sym w ->
  MemTraceBytes sym w -> IO (MemTraceBytes sym w)
writeMemTraceByte sym (LLVMPointer reg off) mtb mtbs = do
  reg' <- Ctx.singleton <$> natToInteger sym reg
  let off' = Ctx.singleton off
  regs <- arrayLookup sym (mtbRegions mtbs) reg'
  offs <- arrayLookup sym (mtbOffsets mtbs) reg'
  subs <- arrayLookup sym (mtbSubOffs mtbs) reg'

  regs' <- arrayUpdate sym regs off' . mtbRegion $ mtb
  offs' <- arrayUpdate sym offs off' . mtbOffset $ mtb
  subs' <- arrayUpdate sym subs off' . mtbSubOff $ mtb

  pure MemTraceBytes
    <*> arrayUpdate sym (mtbRegions mtbs) reg' regs'
    <*> arrayUpdate sym (mtbOffsets mtbs) reg' offs'
    <*> arrayUpdate sym (mtbSubOffs mtbs) reg' subs'

-- | Copy a given region from one memory to another. The first memory is the
-- source, the second the destination, like @cp@ in Linux.
copyRegion :: IsExprBuilder sym =>
  sym -> SymNat sym ->
  MemTraceBytes sym w -> MemTraceBytes sym w -> IO (MemTraceBytes sym w)
copyRegion sym reg src dst = do
  reg' <- Ctx.singleton <$> natToInteger sym reg

  regs <- arrayLookup sym (mtbRegions src) reg'
  offs <- arrayLookup sym (mtbOffsets src) reg'
  subs <- arrayLookup sym (mtbSubOffs src) reg'

  pure MemTraceBytes
    <*> arrayUpdate sym (mtbRegions dst) reg' regs
    <*> arrayUpdate sym (mtbOffsets dst) reg' offs
    <*> arrayUpdate sym (mtbSubOffs dst) reg' subs

-- | 'mtbIdentical', lifted to entire regions. See also 'mtbsIdentical' for
-- lifting it to entire memories.
mtbsIdenticalAt :: IsExprBuilder sym =>
  sym -> SymNat sym ->
  MemTraceBytes sym w -> MemTraceBytes sym w -> IO (Pred sym)
mtbsIdenticalAt sym reg mtbs1 mtbs2 = do
  reg' <- Ctx.singleton <$> natToInteger sym reg

  regs1 <- arrayLookup sym (mtbRegions mtbs1) reg'
  offs1 <- arrayLookup sym (mtbOffsets mtbs1) reg'
  subs1 <- arrayLookup sym (mtbSubOffs mtbs1) reg'

  regs2 <- arrayLookup sym (mtbRegions mtbs2) reg'
  offs2 <- arrayLookup sym (mtbOffsets mtbs2) reg'
  subs2 <- arrayLookup sym (mtbSubOffs mtbs2) reg'

  WEH.allPreds sym =<< sequence
    [ isEq sym regs1 regs2
    , isEq sym offs1 offs2
    , isEq sym subs1 subs2
    ]

-- | 'mtbIdentical', lifted to entire memories. See also 'mtbsIdenticalAt' for
-- lifting only to the level of regions, and 'liftByteRel' for lifting
-- arbitrary 'MemTraceByte' relations to bounded chunks of a memory.
mtbsIdentical :: IsExprBuilder sym =>
  sym ->
  MemTraceBytes sym w -> MemTraceBytes sym w -> IO (Pred sym)
mtbsIdentical sym mtbs1 mtbs2 = WEH.allPreds sym =<< sequence
  [ isEq sym (mtbRegions mtbs1) (mtbRegions mtbs2)
  , isEq sym (mtbOffsets mtbs1) (mtbOffsets mtbs2)
  , isEq sym (mtbSubOffs mtbs1) (mtbSubOffs mtbs2)
  ]

type MemTraceVar = MemTraceBytes
type MemTraceSeq sym ptrW = Seq (MemOp sym ptrW)
type MemArrBase sym ptrW tp = RegValue sym (SymbolicArrayType (EmptyCtx ::> BaseIntegerType) (BaseArrayType (EmptyCtx ::> BaseBVType ptrW) tp))
type MemTrace arch = IntrinsicType "memory_trace" (EmptyCtx ::> BVType (ArchAddrWidth arch))
data MemTraceK

instance IsMemoryModel MemTraceK where
  type MemModelType MemTraceK arch = MemTrace arch
  type MemModelConstraint MemTraceK sym = ()

memTraceRepr :: (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) => TypeRepr (MemTrace arch)
memTraceRepr = knownRepr

mkMemTraceVar ::
  forall arch.
  (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) =>
  HandleAllocator ->
  IO (GlobalVar (MemTrace arch))
mkMemTraceVar ha = freshGlobalVar ha (pack "llvm_memory_trace") knownRepr

mkReturnIPVar ::
  forall arch.
  (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) =>
  HandleAllocator ->
  IO (GlobalVar (MaybeType (LLVMPointerType (ArchAddrWidth arch))))
mkReturnIPVar ha = freshGlobalVar ha (pack "ret_ip") knownRepr

initMemTrace ::
  forall sym ptrW.
  IsSymExprBuilder sym =>
  sym ->
  AddrWidthRepr ptrW ->
  IO (MemTraceImpl sym ptrW)
initMemTrace sym addrRepr = do
  regs <- ioFreshConstant sym "InitMemRegs" $ case addrRepr of
    Addr32 -> knownRepr
    Addr64 -> knownRepr
  offs <- ioFreshConstant sym "InitMemOffs" $ case addrRepr of
    Addr32 -> knownRepr
    Addr64 -> knownRepr
  subs <- ioFreshConstant sym "InitMemSubs" $ case addrRepr of
    Addr32 -> knownRepr
    Addr64 -> knownRepr
  return $ MemTraceImpl mempty (MemTraceBytes regs offs subs)

initMemTraceVar ::
  forall sym ptrW.
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  IO (MemTraceImpl sym ptrW, MemTraceVar sym ptrW)
initMemTraceVar sym repr = do
  impl <- initMemTrace sym repr
  return (impl, memArr impl)

equalPrefixOf :: forall a. Eq a => Seq a -> Seq a -> (Seq a, (Seq a, Seq a))
equalPrefixOf s1 s2 = go s1 s2 Seq.empty
  where
    go :: Seq a -> Seq a -> Seq a -> (Seq a, (Seq a, Seq a))
    go (l' Seq.:|> a) (r' Seq.:|> b) acc | a == b =
      go l' r' (a Seq.<| acc)
    go l r acc =
      (acc, (l, r))

muxTraces ::
  sym ~ (ExprBuilder t st fs) =>
  RegValue sym BoolType ->
  MemTraceSeq sym ptrW ->
  MemTraceSeq sym ptrW ->
  IO (MemTraceSeq sym ptrW)
muxTraces p t f =
  let (pre, (t', f')) = equalPrefixOf t f
  in case (t', f') of
    (Seq.Empty, Seq.Empty) -> return pre
    _ -> return $ pre Seq.:|> MergeOps p t' f'


instance IntrinsicClass (ExprBuilder t st fs) "memory_trace" where
  -- TODO: cover other cases with a TypeError
  type Intrinsic (ExprBuilder t st fs) "memory_trace" (EmptyCtx ::> BVType ptrW) = MemTraceImpl (ExprBuilder t st fs) ptrW
  muxIntrinsic sym _ _ (Empty :> BVRepr _) p t f = do
    s <- muxTraces p (memSeq t) (memSeq f)
    mtb <- muxMemTraceBytes sym p (memArr t) (memArr f)
    return $ MemTraceImpl s mtb

  muxIntrinsic _ _ _ _ _ _ _ = error "Unexpected operands in memory_trace mux"

memTraceIntrinsicTypes :: IsSymInterface (ExprBuilder t st fs) => IntrinsicTypes (ExprBuilder t st fs)
memTraceIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "memory_trace") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn
  $ MapF.empty

type MacawTraceEvalStmtFunc sym arch = MacawEvalStmtFunc (MacawStmtExtension arch) (MacawSimulatorState sym) sym (MacawExt arch)

execMacawStmtExtension ::
  forall sym arch t st fs. (IsSymInterface sym, SymArchConstraints arch, sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn sym (MemTrace arch) arch ->
  UndefinedPtrOps sym (ArchAddrWidth arch) ->
  GlobalVar (MemTrace arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  MacawTraceEvalStmtFunc sym arch
execMacawStmtExtension (MacawArchEvalFn archStmtFn) mkundef mvar globs stmt
  = case stmt of
    MacawReadMem addrWidth memRepr addr
      -> liftToCrucibleState mvar $ \sym ->
        doReadMem sym mkundef addrWidth (regValue addr) memRepr

    MacawCondReadMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondReadMem sym mkundef (regValue cond) (regValue def) addrWidth (regValue addr) memRepr

    MacawWriteMem addrWidth memRepr addr val
      -> liftToCrucibleState mvar $ \sym ->
        doWriteMem sym mkundef addrWidth (regValue addr) (regValue val) memRepr

    MacawCondWriteMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondWriteMem sym mkundef (regValue cond) addrWidth (regValue addr) (regValue def) memRepr

    MacawGlobalPtr w addr -> \cst -> addrWidthClass w $ doGetGlobal cst mvar globs addr
    MacawFreshSymbolic t -> liftToCrucibleState mvar $ \sym -> case t of
       MT.BoolTypeRepr -> liftIO $ freshConstant sym (safeSymbol "macawFresh") BaseBoolRepr
       MT.BVTypeRepr n -> liftIO $ do
         regI <- freshConstant sym (safeSymbol "macawFresh") BaseIntegerRepr
         reg <- integerToNat sym regI
         off <- freshConstant sym (safeSymbol "macawFresh") (BaseBVRepr n)
         return $ LLVMPointer reg off
       _ -> error ( "MacawFreshSymbolic is unsupported in the trace memory model: " ++ show t)
    MacawLookupFunctionHandle _typeReps _registers -> error "MacawLookupFunctionHandle is unsupported in the trace memory model"

    MacawArchStmtExtension archStmt -> archStmtFn mvar globs archStmt

    MacawArchStateUpdate{} -> \cst -> pure ((), cst)
    MacawInstructionStart{} -> \cst -> pure ((), cst)

    PtrEq w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regEq <- natEq sym reg reg'
      offEq <- bvEq sym off off'
      andPred sym regEq offEq

    PtrLeq w x y -> ptrOp w x y $ ptrPredOp (undefPtrLeq mkundef) natEqConstraint $ \sym _reg off _reg' off' -> bvUle sym off off'


    PtrLt w x y -> ptrOp w x y $ ptrPredOp (undefPtrLt mkundef) natEqConstraint $ \sym _reg off _reg' off' -> bvUlt sym off off'

    PtrMux w (RegEntry _ p) x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      reg'' <- natIte sym p reg reg'
      off'' <- bvIte sym p off off'
      pure (LLVMPointer reg'' off'')

    PtrAdd w x y -> ptrOp w x y $ ptrBinOp (undefPtrAdd mkundef) someZero $ \sym reg off reg' off' -> do
      regZero <- isZero sym reg

      reg'' <- natIte sym regZero reg' reg
      off'' <- bvAdd sym off off'
      pure (LLVMPointer reg'' off'')

    PtrSub w x y -> ptrOp w x y $ ptrBinOp (undefPtrSub mkundef) compatSub $ \sym reg off reg' off' -> do
      regEq <- natEq sym reg reg'
      zero <- natLit sym 0

      reg'' <- natIte sym regEq zero reg
      off'' <- bvSub sym off off'
      pure (LLVMPointer reg'' off'')

    PtrAnd w x y -> ptrOp w x y $ ptrBinOp (undefPtrAnd mkundef) someZero $ \sym reg off reg' off' -> do
      regZero <- isZero sym reg

      reg'' <- natIte sym regZero reg' reg
      off'' <- bvAndBits sym off off'
      pure (LLVMPointer reg'' off'')

    PtrXor w x y -> ptrOp w x y $ ptrBinOp (undefPtrXor mkundef) bothZero $ \sym _ off _ off' -> do
      off'' <- bvXorBits sym off off'
      llvmPointer_bv sym off''

evalMacawExprExtensionTrace :: forall sym arch ptrW f tp
                       .  IsSymInterface sym
                       => UndefinedPtrOps sym ptrW
                       -> sym
                       -> IntrinsicTypes sym
                       -> (Int -> String -> IO ())
                       -> (forall utp . f utp -> IO (RegValue sym utp))
                       -> MacawExprExtension arch f tp
                       -> IO (RegValue sym tp)
evalMacawExprExtensionTrace undefptr sym iTypes logFn f e0 =
  case e0 of
    PtrToBits _w x  -> doPtrToBits sym undefptr =<< f x
    _ -> evalMacawExprExtension sym iTypes logFn f e0

doPtrToBits ::
  (IsSymInterface sym, 1 <= w) =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  LLVMPtr sym w ->
  IO (SymBV sym w)
doPtrToBits sym mkundef ptr@(LLVMPointer base off) = do
  case asNat base of
    Just 0 -> return off
    _ -> do
      cond <- natEq sym base =<< natLit sym 0
      case asConstantPred cond of
        Just True -> return off
        _ -> do
          assert sym cond $ AssertFailureSimError "doPtrToBits" "doPtrToBits"
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

asCrucibleStateT ::
  (sym -> StateT (CrucibleState p sym ext rtp blocks r ctx) IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
asCrucibleStateT f cst = do
  (a, cst') <- runStateT (f (cst ^. stateSymInterface)) cst
  pure (a, cst')

readOnlyWithSym ::
  (sym -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
readOnlyWithSym f cst = flip (,) cst <$> f (cst ^. stateSymInterface)

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
natAny ::
  IsSymInterface sym =>
  RegionConstraint sym
natAny = RegionConstraint "impossible" $ \sym _ _ -> return $ truePred sym

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

-- | A 'RegionConstraint' that requires that both of the regions are zero.
bothZero ::
  IsSymInterface sym =>
  RegionConstraint sym
bothZero = RegionConstraint "both pointer regions must be zero" $ \sym reg1 reg2 -> do
  regZero1 <- isZero sym reg1
  regZero2 <- isZero sym reg2
  andPred sym regZero1 regZero2

-- | A 'RegionConstraint' that defines when regions are compatible for subtraction:
-- either the regions are equal or the first region is zero.
compatSub ::
  IsSymInterface sym =>
  RegionConstraint sym
compatSub = RegionConstraint msg $ \sym reg1 reg2 -> do
  regZero2 <- isZero sym reg2
  regEq <- natEq sym reg1 reg2
  orPred sym regZero2 regEq
  where
    msg = "both regions must be equal, or the offset must be region 0"

ptrOp ::
  AddrWidthRepr w ->
  RegEntry sym (LLVMPointerType w) ->
  RegEntry sym (LLVMPointerType w) ->
  (1 <= w => sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
ptrOp w (RegEntry _ (LLVMPointer region offset)) (RegEntry _ (LLVMPointer region' offset')) f =
  addrWidthsArePositive w $ readOnlyWithSym $ \sym -> do
    f sym region offset region' offset'
        
ptrPredOp ::
  IsSymInterface sym =>
  UndefinedPtrPredOp sym ->
  RegionConstraint sym ->
  (sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (Pred sym)) ->
  sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (Pred sym)
ptrPredOp mkundef regconstraint f sym reg1 off1 reg2 off2  = do
  cond <- regConstraintEval regconstraint sym reg1 reg2
  result <- f sym reg1 off1 reg2 off2
  case asConstantPred cond of
    Just True -> return result
    _ -> do
      assert sym cond $ AssertFailureSimError "ptrPredOp" $ "ptrPredOp: " ++ regConstraintMsg regconstraint
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
  IsSymInterface sym =>
  UndefinedPtrBinOp sym ->
  RegionConstraint sym ->
  (sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (LLVMPtr sym w)) ->
  sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO (LLVMPtr sym w)
ptrBinOp mkundef regconstraint f sym reg1 off1 reg2 off2 = do
  cond <- regConstraintEval regconstraint sym reg1 reg2
  result <- f sym reg1 off1 reg2 off2
  case asConstantPred cond of
    Just True -> return result
    _ -> do
      assert sym cond $ AssertFailureSimError "ptrBinOp" $ "ptrBinOp: " ++ regConstraintMsg regconstraint
      undef <- mkUndefPtr mkundef sym (LLVMPointer reg1 off1) (LLVMPointer reg2 off2)
      muxPtr sym cond result undef

cases ::
  IsExprBuilder sym =>
  sym ->
  [(IO (Pred sym), IO (SymExpr sym tp))] ->
  IO (SymExpr sym tp) ->
  IO (SymExpr sym tp)
cases sym branches def = go branches where
  go [] = def
  go ((iop, iov):bs) = do
    p <- iop
    vT <- iov
    vF <- go bs
    baseTypeIte sym p vT vF

isZero :: IsExprBuilder sym => sym -> SymNat sym -> IO (Pred sym)
isZero sym reg = do
  zero <- natLit sym 0
  natEq sym reg zero

doReadMem ::
  IsSymInterface sym =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (MS.ToCrucibleType ty))
doReadMem sym undef ptrW ptr memRepr = addrWidthClass ptrW $ do
  mem <- get
  val <- liftIO $ readMemArr sym undef mem ptr memRepr
  doMemOpInternal sym Read Unconditional undef ptrW ptr val memRepr
  pure val

doCondReadMem ::
  IsSymInterface sym =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  RegValue sym BoolType ->
  RegValue sym (MS.ToCrucibleType ty) ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (MS.ToCrucibleType ty))
doCondReadMem sym undef cond def ptrW ptr memRepr = addrWidthClass ptrW $ do
  mem <- get
  val <- liftIO $ readMemArr sym undef mem ptr memRepr
  doMemOpInternal sym Read (Conditional cond) undef ptrW ptr val memRepr
  liftIO $ iteDeep sym cond val def memRepr

doWriteMem ::
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  UndefinedPtrOps sym ptrW ->
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
  UndefinedPtrOps sym ptrW ->
  RegValue sym BoolType ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doCondWriteMem sym undef cond = doMemOpInternal sym Write (Conditional cond) undef

ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrAdd sym (LLVMPointer base off1) off2 =
  LLVMPointer base <$> bvAdd sym off1 off2

bvFromInteger ::
  (1 <= w, IsExprBuilder sym) => sym ->
  NatRepr w -> Integer -> IO (SymBV sym w)
bvFromInteger sym w n = bvLit sym w (BV.mkBV w n)

-- | Calculate an index into the memory array from a pointer
arrayIdx ::
  1 <= ptrW =>
  IsExprBuilder sym =>
  sym ->
  LLVMPtr sym ptrW ->
  Integer ->
  IO (LLVMPtr sym ptrW)
arrayIdx sym ptr off' = bvFromInteger sym (ptrWidth ptr) off' >>= ptrAdd sym ptr

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

testByteSizeEquality :: forall w w'. MemWidth w => NatRepr w' -> Maybe (8*w' :~: w)
testByteSizeEquality w' = case addrWidthRepr @w Proxy of
  Addr32 -> (\Refl -> Refl) <$> testEquality w' (knownRepr :: NatRepr 4)
  Addr64 -> (\Refl -> Refl) <$> testEquality w' (knownRepr :: NatRepr 8)

leibnizMultiplication :: forall n a b. OrderingF a b -> OrderingF (n*a) (n*b)
leibnizMultiplication LTF = LTF
leibnizMultiplication EQF = EQF
leibnizMultiplication GTF = GTF

compareByteSize :: forall w w'. MemWidth w => NatRepr w' -> OrderingF w (8*w')
compareByteSize w' = case addrWidthRepr @w Proxy of
  Addr32 -> leibnizMultiplication @8 (compareF (knownNat @4) w')
  Addr64 -> leibnizMultiplication @8 (compareF (knownNat @8) w')

-- | Read a packed value from the underlying array
readMemArr :: forall sym ptrW ty.
  MemWidth ptrW =>
  IsSymInterface sym =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (MS.ToCrucibleType ty))
readMemArr sym undef mem ptr repr = go 0 repr
  where
  go :: Integer -> MemRepr ty' -> IO (RegValue sym (MS.ToCrucibleType ty'))
  go n (BVMemRepr byteWidth endianness)
    | Just Refl <- testByteSizeEquality @ptrW byteWidth = goPtr n endianness
    | otherwise = goBV n byteWidth endianness

  go _n (FloatMemRepr _infoRepr _endianness) = fail "creating fresh float values not supported in freshRegValue"

  go n (PackedVecMemRepr countRepr recRepr) = V.generateM (fromInteger (intValue countRepr)) $ \i ->
      go (n + memReprByteSize recRepr * fromIntegral i) recRepr

  goPtr :: Integer -> Endianness -> IO (LLVMPtr sym ptrW)
  goPtr n endianness = do
    -- read memory
    ptr' <- arrayIdx sym ptr n
    memBytes@(MemTraceByte valReg valOff _:_) <- readMemTraceByteMany sym ptr' (bytesToInteger ptrWBytes) (memArr mem)

    -- check if we're reading a pointer
    (regsEq, offsEq, subOffsOrdered) <- foldM
      (extendPtrCond endianness valReg valOff)
      (truePred sym, truePred sym, truePred sym)
      (zip [0..] memBytes)
    isPtr <- andPred sym regsEq =<< andPred sym offsEq subOffsOrdered

    -- check if we're reading region-0 data; reassemble the individual bytes if so
    int0 <- intLit sym 0
    isReg0 <- andPred sym regsEq =<< intEq sym valReg int0
    bv0 <- bvFromInteger sym ptrWRepr 0
    appendMemByte <- mkAppendMemByte
    reg0Off <- foldM appendMemByte bv0 (appendOrder endianness memBytes)

    -- bad case: mismatched regions. use an uninterpreted function
    -- TODO: use a single uninterpreted function
    undefBytes <- forM memBytes $ \(MemTraceByte badReg badOff badSubOff) -> do
      badRegNat <- integerToNat sym badReg
      undefMismatchedRegionRead undef sym (LLVMPointer badRegNat badOff) badSubOff
    predAvoidUndef <- andPred sym isPtr isReg0
    assert sym predAvoidUndef $ AssertFailureSimError "readMemArr" $ "readMemArr: reading bytes from mismatched regions"
    appendByte <- mkAppendByte
    undefOff <- foldM appendByte bv0 (appendOrder endianness undefBytes)

    -- put it all together
    regResult <- integerToNat sym =<< intIte sym regsEq valReg int0
    offResult <- bvIte sym isPtr valOff =<< bvIte sym isReg0 reg0Off undefOff
    pure (LLVMPointer regResult offResult)

  extendPtrCond ::
    conditions ~ (Pred sym, Pred sym, Pred sym) =>
    Endianness ->
    SymInteger sym ->
    SymBV sym ptrW ->
    conditions ->
    (Integer, MemTraceByte sym ptrW) ->
    IO conditions
  extendPtrCond endianness expectedReg expectedOff (regsEq, offsEq, subOffsOrdered) (ix, mtb) = do
    expectedSubOff <- bvFromInteger sym ptrWRepr $ case endianness of
      BigEndian -> bytesToInteger ptrWBytes - ix - 1
      LittleEndian -> ix
    regsEq' <- andPred sym regsEq =<< intEq sym expectedReg (mtbRegion mtb)
    offsEq' <- andPred sym offsEq =<< bvEq sym expectedOff (mtbOffset mtb)
    subOffsOrdered' <- andPred sym subOffsOrdered =<< bvEq sym expectedSubOff (mtbSubOff mtb)
    pure (regsEq', offsEq', subOffsOrdered')

  appendOrder LittleEndian = reverse
  appendOrder BigEndian = id

  -- Not perfectly named. We're not so much appending as shifting it in. If we
  -- start with bytes = 0xAABBCCDD and a memByte representing 0xEE, we end with
  -- 0xBBCCDDEE.
  --
  -- Accomplished by shifting `bytes` left, `off` right, and doing the usual
  -- mask+combine dance we all know and love from our C days.
  mkAppendMemByte = do
    bv3 <- bvFromInteger sym ptrWRepr 3
    bv8 <- bvFromInteger sym ptrWRepr 8
    mask <- bvFromInteger sym ptrWRepr 0xff
    pure $ \bytes mtb -> do
      bytes' <- bvShl sym bytes bv8
      subOff' <- bvShl sym (mtbSubOff mtb) bv3
      off' <- bvLshr sym (mtbOffset mtb) subOff'
      bvOrBits sym bytes' =<< bvAndBits sym off' mask

  mkAppendByte | LeqProof <- memWidthIsBig @ptrW @9 = do
    bv8 <- bvFromInteger sym ptrWRepr 8
    pure $ \bytes byte -> do
      bytes' <- bvShl sym bytes bv8
      byte' <- bvZext sym ptrWRepr byte
      bvOrBits sym bytes' byte'

  goBV :: forall w. 1 <= w => Integer -> NatRepr w -> Endianness -> IO (LLVMPtr sym (8*w))
  goBV n byteWidth endianness =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl
        | Refl <- zeroSubEq byteWidth (knownNat @1) -> do
          ptr' <- arrayIdx sym ptr n
          memByte <- readMemTraceByte sym ptr' (memArr mem)
          content <- getMemByteOff sym undef ptrWRepr memByte
          blk0 <- natLit sym 0
          return $ LLVMPointer blk0 content
      Right LeqProof
        | byteWidth' <- decNat byteWidth
        , Refl <- lemmaMul (knownNat @8) byteWidth
        , Refl <- mulComm (knownNat @8) byteWidth'
        , Refl <- mulComm (knownNat @8) byteWidth
        , LeqProof <- mulMono (knownNat @8) byteWidth' -> do
          hd <- goBV n (knownNat @1) endianness
          tl <- goBV (n + 1) byteWidth' endianness
          concatPtrs sym endianness hd tl

  ptrWRepr = let LLVMPointer _ off = ptr in bvWidth off

  ptrWBytes :: Bytes
  ptrWBytes = bitsToBytes (natValue ptrWRepr)
    
-- | Write to the memory array and set the dirty bits on
-- any written addresses
writeMemArr :: forall sym ptrW w.
  1 <= ptrW =>
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr (MT.BVType w) ->
  LLVMPtr sym w ->
  IO (MemTraceImpl sym ptrW)
writeMemArr sym undef mem_init ptr (BVMemRepr byteWidth endianness) val@(LLVMPointer valReg valOff)
  | Just Refl <- testByteSizeEquality @ptrW byteWidth
    = do
      valRegInt <- natToInteger sym valReg
      goPtr valRegInt 0 mem_init
  | Just 0 <- asNat valReg
  , NatLT _ <- compareNat (knownNat @0) bitWidth
  , NatLT _ <- compareNat bitWidth (memWidthNatRepr @ptrW)
    = do
      valRegInt <- intLit sym 0 -- = valReg, per the Just 0 <- asNat valReg guard
      goNonPtr valRegInt 0 mem_init
  | otherwise = case isZeroOrGT1 byteWidth of
    Left pf -> case pf of -- impossible, and obvious enough GHC can see it
    Right (mulMono @_ @_ @8 Proxy -> LeqProof) -> do
      bvZero <- bvFromInteger sym ptrWRepr 0
      intZero <- intLit sym 0
      bvPtrW <- bvFromInteger sym ptrWRepr ptrWInteger
      bvValW <- bvFromInteger sym ptrWRepr (8*valWByteInteger)
      eqCond <- bvEq sym bvPtrW bvValW
      -- treat any non-pointer-width writes as writing undefined values
      goBV eqCond bvZero intZero 0 mem_init
  where
  goBV ::
    Pred sym ->
    SymBV sym ptrW ->
    SymInteger sym ->
    Integer ->
    MemTraceImpl sym ptrW ->
    IO (MemTraceImpl sym ptrW)
  goBV _eqCond _bvZero _intZero n mem | n == valWByteInteger = pure mem
  goBV eqCond bvZero intZero n mem = do
    nBV <- bvFromInteger sym ptrWRepr (useEnd ptrWByteInteger n)
    assert sym eqCond $ AssertFailureSimError "writeMemArr" $ "writeMemArr: expected write of size " ++ show ptrWInteger ++ ", saw " ++ show (8*valWByteInteger)
    undefBV <- undefWriteSize undef sym val nBV
    writeByte sym ptr (MemTraceByte intZero undefBV bvZero) n mem >>= goBV eqCond bvZero intZero (n+1)

  goPtr ::
    w ~ ptrW =>
    SymInteger sym ->
    Integer ->
    MemTraceImpl sym ptrW ->
    IO (MemTraceImpl sym ptrW)
  goPtr valRegInt n mem | n == ptrWByteInteger = pure mem
  goPtr valRegInt n mem = do
    nBV <- bvFromInteger sym ptrWRepr (useEnd ptrWByteInteger n)
    writeByte sym ptr (MemTraceByte valRegInt valOff nBV) n mem >>= goPtr valRegInt (n+1)

  goNonPtr ::
    (1 <= w, w + 1 <= ptrW) =>
    SymInteger sym ->
    Integer ->
    MemTraceImpl sym ptrW ->
    IO (MemTraceImpl sym ptrW)
  goNonPtr valRegInt n mem | n == valWByteInteger = pure mem
  goNonPtr valRegInt n mem = do
    nBV <- bvFromInteger sym ptrWRepr (useEnd valWByteInteger n)
    valOffExt <- bvZext sym memWidthNatRepr valOff
    writeByte sym ptr (MemTraceByte valRegInt valOffExt nBV) n mem >>= goNonPtr valRegInt (n+1)



  bitWidth = natMultiply (knownNat @8) byteWidth
  ptrWRepr = let LLVMPointer _ off = ptr in bvWidth off
  ptrWInteger = toInteger (natValue ptrWRepr)
  ptrWByteInteger = ptrWInteger `div` 8
  valWByteInteger = toInteger (natValue byteWidth)
  useEnd writeSize = case endianness of
    BigEndian -> ((writeSize-1)-)
    LittleEndian -> id


writeByte ::
  MemWidth ptrW =>
  IsSymInterface sym =>
  sym ->
  -- | base address to write to
  LLVMPtr sym ptrW ->
  -- | value to write
  MemTraceByte sym ptrW ->
  -- | offset from base address
  Integer ->
  MemTraceImpl sym ptrW ->
  IO (MemTraceImpl sym ptrW)
writeByte sym ptr mtb n mem = do
  ptr' <- arrayIdx sym ptr n
  mtbs' <- writeMemTraceByte sym ptr' mtb (memArr mem)
  pure mem { memArr = mtbs' }

-- | An uninterpreted raw chunk of memory, representing 'w' bytes
newtype ByteChunk sym ptrW w where
  ByteChunk :: VF.Vector w (MemTraceByte sym ptrW) -> ByteChunk sym ptrW w

instance PEM.ExprMappable sym (ByteChunk sym ptrW w) where
  mapExpr sym f (ByteChunk chunk) = ByteChunk <$> traverse (PEM.mapExpr sym f) chunk

writeByteChunk ::
  MemWidth ptrW =>
  IsSymInterface sym =>
  sym ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  ByteChunk sym ptrW w ->
  IO (MemTraceImpl sym ptrW)
writeByteChunk sym mem ptr (ByteChunk chunk)  = do
  foldM (\mem' (i, mtb) -> writeByte sym ptr mtb i mem') mem (zip [0..] (VF.toList chunk))

readByteChunk ::
  forall sym ptrW w.
  MemWidth ptrW =>
  1 <= w =>
  IsSymInterface sym =>
  sym ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  NatRepr w ->
  IO (ByteChunk sym ptrW w)
readByteChunk sym mem ptr size = do
  Just chunk <- VF.fromList size <$> readMemTraceByteMany sym ptr (intValue size) (memArr mem)
  pure (ByteChunk chunk)

liftByteRel ::
  forall sym ptrW w.
  MemWidth ptrW =>
  IsExprBuilder sym =>
  sym ->
  LLVMPtr sym ptrW ->
  NatRepr w ->
  (MemTraceByte sym ptrW -> MemTraceByte sym ptrW -> IO (Pred sym)) ->
  MemTraceImpl sym ptrW -> MemTraceImpl sym ptrW -> IO (Pred sym)
liftByteRel sym ptr w byteRel mem1 mem2 = do
  mtbs1 <- readMemTraceByteMany sym ptr (intValue w) (memArr mem1)
  mtbs2 <- readMemTraceByteMany sym ptr (intValue w) (memArr mem2)
  WEH.allPreds sym =<< zipWithM byteRel mtbs1 mtbs2

-- | True iff the two memory states are representationally equal
-- at the given address, for 'w' bytes read.
-- Note: this is stronger than memory being semantically equivalent at the given addresses,
-- as it asserts that the provenance of each byte is equal.
-- There exist memory traces which would yield semantically equivalent memory states, but
-- would not be equal according to this predicate.
-- These differences should be unobservable according to the usual memory API, however.
-- We may therefore soundly assume this predicate when constructing pre-domains, but
-- it would be too strong to require it as the equivalence post-condition.
memEqAt ::
  forall sym ptrW w.
  MemWidth ptrW =>
  1 <= w =>
  IsSymInterface sym =>
  sym ->
  MemTraceImpl sym ptrW ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  NatRepr w ->
  IO (Pred sym)
memEqAt sym mem1 mem2 ptr w = liftByteRel sym ptr w (mtbIdentical sym) mem1 mem2

-- | True iff 'w' bytes following the given pointer are semantically equivalent
-- in memory, regardless of their representation.
memByteEqAt ::
  forall sym ptrW w.
  MemWidth ptrW =>
  1 <= w =>
  IsSymInterface sym =>
  sym ->
  MemTraceImpl sym ptrW ->
  MemTraceImpl sym ptrW ->
  LLVMPtr sym ptrW ->
  NatRepr w ->
  IO (Pred sym)
memByteEqAt sym mem1 mem2 ptr w = do
  LeqProof <- return $ memWidthIsBig @ptrW @9
  liftByteRel sym ptr w (mtbEq sym) mem1 mem2


freshChunk ::
  forall sym ptrW w.
  MemWidth ptrW =>
  1 <= w =>
  IsSymInterface sym =>
  sym ->
  NatRepr w ->
  IO (ByteChunk sym ptrW w)
freshChunk sym w
  | Refl <- minusPlusCancel w (knownNat @1) =
      ByteChunk <$> VF.generateM (decNat w) (\_ -> go)
  where
    go :: IO (MemTraceByte sym ptrW)
    go = pure MemTraceByte
      <*> freshConstant sym emptySymbol BaseIntegerRepr
      <*> freshConstant sym emptySymbol (BaseBVRepr (memWidthNatRepr @ptrW))
      <*> freshConstant sym emptySymbol (BaseBVRepr (memWidthNatRepr @ptrW))


getMemByteOff :: forall sym ptrW.
  (MemWidth ptrW, IsExprBuilder sym) =>
  sym ->
  UndefinedPtrOps sym ptrW ->
  NatRepr ptrW ->
  MemTraceByte sym ptrW ->
  IO (SymBV sym 8)
getMemByteOff sym undef ptrWRepr memByte
  | LeqProof <- memWidthIsBig @ptrW @9
  = do
    -- pick a byte of the offset in case we're in region 0
    bv8 <- bvFromInteger sym ptrWRepr 8
    subOffBits <- bvMul sym (mtbSubOff memByte) bv8
    knownByteLong <- bvLshr sym (mtbOffset memByte) subOffBits
    knownByte <- bvTrunc sym knownRepr knownByteLong

    -- check if we're in region 0, and use an uninterpreted byte if not
    useKnownByte <- intEq sym (mtbRegion memByte) =<< intLit sym 0
    reg <- integerToNat sym (mtbRegion memByte)
    -- TODO: use off + subOff w/ endianness as the pointer, then truncate to a byte
    unknownByte <- undefPtrOff undef sym (LLVMPointer reg knownByte)
    bvIte sym useKnownByte knownByte unknownByte

memWidthIsBig :: (MemWidth ptrW, n <= 32) => LeqProof n ptrW
memWidthIsBig = fix $ \v -> case addrWidthRepr v of
  Addr32 -> leqTrans (LeqProof @_ @32) LeqProof
  Addr64 -> leqTrans (LeqProof @_ @32) LeqProof

ifCond ::
  IsSymInterface sym =>
  sym ->  
  MemOpCondition sym ->
  MemTraceBytes sym w ->
  MemTraceBytes sym w ->
  IO (MemTraceBytes sym w)
ifCond _ Unconditional eT _ = return eT
ifCond sym (Conditional p) eT eF = muxMemTraceBytes sym p eT eF

doMemOpInternal :: forall sym ptrW ty.
  IsSymInterface sym =>
  MemWidth ptrW =>
  sym ->
  MemOpDirection ->
  MemOpCondition sym ->
  UndefinedPtrOps sym ptrW ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (MS.ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doMemOpInternal sym dir cond undef ptrW = go where
  go :: LLVMPtr sym ptrW -> RegValue sym (MS.ToCrucibleType ty') -> MemRepr ty' -> StateT (MemTraceImpl sym ptrW) IO ()
  go ptr@(LLVMPointer reg off) regVal = \case
    repr@(BVMemRepr byteWidth endianness)
      | LeqProof <- mulMono (knownNat @8) byteWidth
      -> addrWidthsArePositive ptrW $ do
     
      modify $ \mem -> mem { memSeq = (memSeq mem) Seq.:|> MemOp ptr dir cond byteWidth regVal endianness }
      case dir of
        Read -> return ()
        Write -> do
          mem <- get
          mem' <- liftIO $ writeMemArr sym undef mem ptr repr regVal
          arr <- liftIO $ ifCond sym cond (memArr mem') (memArr mem)
          put $ mem { memArr = arr }
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

ioFreshVar :: IsSymExprBuilder sym => sym -> String -> BaseTypeRepr tp -> IO (BoundVar sym tp)
ioFreshVar sym nm ty = do
  symbol <- ioSolverSymbol nm
  freshBoundVar sym symbol ty

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

andCond ::
  IsExprBuilder sym =>
  sym ->
  MemOpCondition sym ->
  MemOpCondition sym ->
  IO (MemOpCondition sym)
andCond sym cond1 cond2 = case (cond1, cond2) of
  (Unconditional, _) -> return cond2
  (_, Unconditional) -> return cond1
  (Conditional cond1', Conditional cond2') ->
    Conditional <$> andPred sym cond1' cond2'

mconcatSeq :: Monoid a => Seq a -> a
mconcatSeq = foldl' (<>) mempty

-- | Flatten a 'MemOp' into a sequence of atomic operations
flatMemOp ::
  IsExprBuilder sym =>
  sym ->
  MemOpCondition sym ->
  MemOp sym ptrW ->
  IO (Seq (MemOp sym ptrW))
flatMemOp sym outer_cond mop = case mop of
  MemOp ptr dir cond w val endianness -> do
    cond' <- andCond sym outer_cond cond
    let wop = MemOp ptr dir cond' w val endianness
    return $ Seq.singleton wop
  MergeOps cond seqT seqF -> do
    cond' <- andCond sym outer_cond (Conditional cond)
    seqT' <- mconcatSeq <$> traverse (flatMemOp sym cond') seqT
    notcond <- notPred sym cond
    notcond' <- andCond sym outer_cond (Conditional notcond)
    seqF' <- mconcatSeq <$> traverse (flatMemOp sym notcond') seqF
    return $ seqT' Seq.>< seqF'

-- | Collapse a 'MemTraceSeq' into a sequence of conditional write operations
flatMemOps ::
  IsExprBuilder sym =>
  sym ->
  MemTraceSeq sym ptrW ->
  IO (Seq (MemOp sym ptrW))
flatMemOps sym mem = mconcatSeq <$> traverse (flatMemOp sym Unconditional) mem

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

memFootDir :: MemFootprint sym ptrW -> MemOpDirection
memFootDir (MemFootprint _ _ dir _ _) = dir

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
  MemOp sym ptrW ->
  MemFootprint sym ptrW
memOpFootprint (MemOp ptr dir cond w _ end) = MemFootprint ptr w dir cond end
memOpFootprint _ = error "Unexpected merge op"

traceFootprint ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  MemTraceSeq sym ptrW ->
  IO (Set (MemFootprint sym ptrW))
traceFootprint sym mem = do
  footprints <- (fmap memOpFootprint) <$> flatMemOps sym mem
  return $ foldl' (\a b -> Set.insert b a) mempty footprints

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


traceFootprints ::
  IsSymInterface sym =>
  sym ->
  MemTraceImpl sym ptrW ->
  MemTraceImpl sym ptrW ->
  IO [MemFootprint sym ptrW]
traceFootprints sym mem1 mem2 = do
  foot1 <- traceFootprint sym (memSeq mem1)
  foot2 <- traceFootprint sym (memSeq mem2)
  return $ Set.toList (Set.union foot1 foot2)

getCond ::
  IsExprBuilder sym =>
  sym ->
  MemOpCondition sym ->
  Pred sym
getCond sym Unconditional = truePred sym
getCond _sym (Conditional p) = p

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
    MergeOps p seq1 seq2 -> do
      p' <- f p
      seq1' <- traverse (PEM.mapExpr sym f) seq1
      seq2' <- traverse (PEM.mapExpr sym f) seq2
      return $ MergeOps p' seq1' seq2'

instance PEM.ExprMappable sym (MemTraceByte sym w) where
  mapExpr sym f mtb = pure MemTraceByte
    <*> f (mtbRegion mtb)
    <*> f (mtbOffset mtb)
    <*> f (mtbSubOff mtb)

instance PEM.ExprMappable sym (MemTraceBytes sym w) where
  mapExpr _sym f mtbs = pure MemTraceBytes
    <*> f (mtbRegions mtbs)
    <*> f (mtbOffsets mtbs)
    <*> f (mtbSubOffs mtbs)

instance PEM.ExprMappable sym (MemTraceImpl sym w) where
  mapExpr sym f mem = do
    memSeq' <- traverse (PEM.mapExpr sym f) $ memSeq mem
    memArr' <- PEM.mapExpr sym f $ memArr mem
    return $ MemTraceImpl memSeq' memArr'

instance PEM.ExprMappable sym (MemFootprint sym arch) where
  mapExpr sym f (MemFootprint ptr w dir cond end) = do
    ptr' <- WEH.mapExprPtr sym f ptr
    cond' <- PEM.mapExpr sym f cond
    return $ MemFootprint ptr' w dir cond' end
