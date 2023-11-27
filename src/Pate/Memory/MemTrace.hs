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
, isDir
, getCond
, MemTraceK
, traceFootprint
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
, mkAnnotatedPtrOps
, macawTraceExtensions
, memEqOutsideRegion
, memEqAtRegion
, memEqExact
, memOpOverlapsRegion
, prettyMemOp
, prettyMemEvent
, prettyMemTraceSeq
, addExternalCallEvent
, SymBV'(..)
, getPtrAssertion
, PtrAssertions
, doStaticRead
, doStaticReadAddr
, TraceEvent(..)
, RegOp(..)
, memFullSeq
, GroundInfo(..)
) where

import Unsafe.Coerce
import           Control.Applicative
import           Control.Lens ((%~), (&), (^.), (.~))
import           Control.Monad.State
import qualified Control.Monad.IO.Class as IO
import qualified Data.BitVector.Sized as BV
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Vector as V
import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Proxy
import           Data.IORef
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.TypeNats (KnownNat, type Nat)
import           Prettyprinter

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.Types as MT
import Data.Macaw.CFG.AssignRhs (ArchAddrWidth, MemRepr(..), ArchReg)
import Data.Macaw.Memory
           (AddrWidthRepr(..), Endianness(..), MemWidth
           , addrWidthClass, addrWidthRepr, addrWidthNatRepr, memWidthNatRepr
           , incSegmentOff, memWordToUnsigned, MemSegmentOff
           , MemWord, memWordToUnsigned, segmentFlags
           , Memory, emptyMemory, memWord, segoffSegment
           , segoffAddr, readWord8, readWord16be, readWord16le
           , readWord32le, readWord32be, readWord64le, readWord64be, MemAddr, asSegmentOff
           )
import qualified Data.Macaw.Memory.Permissions as MMP
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
import What4.Interface hiding ( integerToNat )
import           Data.Parameterized.SetF (AsOrd(..))

import           Pate.Panic
import qualified Pate.ExprMappable as PEM
import           What4.ExprHelpers ( integerToNat )
import qualified What4.ExprHelpers as WEH
import qualified Pate.Memory as PM
import Data.Macaw.CFG (ArchSegmentOff, RegisterInfo)
import qualified Pate.SimulatorRegisters as PSr
import Data.Data (Typeable, eqT)

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
    { undefPtrOff :: UndefinedPtrUnOp sym (SymBV' sym)
    , undefPtrLt :: UndefinedPtrBinOp sym (Const (Pred sym))
    , undefPtrLeq :: UndefinedPtrBinOp sym (Const (Pred sym))
    , undefPtrAdd :: UndefinedPtrBinOp sym (LLVMPtr' sym)
    , undefPtrSub :: UndefinedPtrBinOp sym (LLVMPtr' sym)
    , undefPtrAnd :: UndefinedPtrBinOp sym (LLVMPtr' sym)
    , undefPtrXor :: UndefinedPtrBinOp sym (LLVMPtr' sym)
    , undefPtrClassify :: UndefPtrClassify sym
    }

-- Needed since SymBV is a type alias
newtype SymBV' sym w = SymBV' { unSymBV :: SymBV sym w }

instance OrdF (SymExpr sym) => TestEquality (SymBV' sym) where
  testEquality a b = case compareF a b of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF (SymExpr sym) => OrdF (SymBV' sym) where
  compareF (SymBV' a) (SymBV' b) = case compareF a b of
    EQF -> EQF
    LTF -> LTF
    GTF -> GTF

instance PEM.ExprMappable2 sym1 sym2 (SymBV' sym w) (SymBV' sym2 w) where
  mapExpr2 _sym1 _sym2 f (SymBV' bv) = SymBV' <$> f bv

instance IsExpr (SymExpr sym) => Pretty (SymBV' sym w) where
  pretty (SymBV' bv) = printSymExpr bv

instance IsExpr (SymExpr sym) => Show (SymBV' sym w) where
  show (SymBV' bv) = show (printSymExpr bv)

instance IsExpr (SymExpr sym) => ShowF (SymBV' sym) where

-- Needed since LLVMPtr is a type alias
newtype LLVMPtr' sym w = LLVMPtr' { unLLVMPtr:: LLVMPtr sym w }

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

data AssertedResult sym f = AssertedResult
  { assertedPred :: Pred sym
  , assertedResult :: f
  }

-- | Wraps a function which is used to produce an "undefined" pointer that
-- may result from a binary pointer operation.
-- The given predicate is true when the operation is defined. i.e if this predicate
-- is true then this undefined value is unused. The two other arguments are the original inputs to the binary pointer operation.
newtype UndefinedPtrBinOp sym a =
  UndefinedPtrBinOp
    { mkBinUndef ::
        forall w.
        sym ->
        (AssertedResult sym (a w)) ->
        LLVMPtr sym w ->
        LLVMPtr sym w ->
        IO (a w)
    }


newtype UndefinedPtrUnOp sym a =
  UndefinedPtrUnOp
    { mkUnUndef ::
        forall w.
        sym ->
        (AssertedResult sym (a w)) ->
        LLVMPtr sym w ->
        IO (a w)
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
  let ireg = natToIntegerPure reg
  mkStruct sym (Empty :> ireg :> off)

fromSymPtr ::
  IsSymExprBuilder sym =>
  sym ->
  SymPtr sym w ->
  IO (LLVMPtr sym w )
fromSymPtr sym sptr = do
  reg <- WEH.assumePositiveInt sym <$> structField sym sptr Ctx.i1of2
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
  IO (UndefinedPtrBinOp sym (LLVMPtr' sym), UndefPtrClassify sym)
mkBinOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkBinUF tag
  let binop =
        UndefinedPtrBinOp $ \sym' r ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          sptrResult <- applyPolyFun resultfn (Empty :> sptr1 :> sptr2)
          undefResultPtr <- fromSymPtr sym' sptrResult
          LLVMPtr' <$> muxPtr sym (assertedPred r) (unLLVMPtr $ assertedResult r) undefResultPtr

  return (binop, classifier)

mkPredOp ::
  IsSymInterface sym =>
  sym ->
  UndefPtrOpTag ->
  IO (UndefinedPtrBinOp sym (Const (Pred sym)), UndefPtrClassify sym)
mkPredOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkPredUF tag
  let binop =
        UndefinedPtrBinOp $ \sym' r ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          undefResultPred <- applyPolyFun resultfn (Empty :> sptr1 :> sptr2)
          Const <$> baseTypeIte sym (assertedPred r) (getConst $ assertedResult r) undefResultPred

  return (binop, classifier)

data PtrAssert sym tp = PtrAssert
  { _ptrAssertPred :: Pred sym -- TODO: extract pointer assertions so we can assume them
  , ptrAssertTag:: UndefPtrOpTag
  }

newtype PtrAssertions sym = PtrAssertions (IORef (MapF.MapF (SymAnnotation sym) (PtrAssert sym)))

-- | Retrieve any pointer assertions associate with this expression
getPtrAssertion ::
  IsSymExprBuilder sym =>
  sym ->
  PtrAssertions sym ->
  SymExpr sym tp ->
  IO (Maybe (Pred sym, SymExpr sym tp))
getPtrAssertion sym (PtrAssertions ref) e = do
  asserts <- readIORef ref
  case getAnnotation sym e of
    Just ann | Just (PtrAssert p _) <- MapF.lookup ann asserts, Just e' <- getUnannotatedTerm sym e -> return $ Just (p, e')
    _ -> return $ Nothing

annotatePredicate ::
  IsSymExprBuilder sym =>
  sym ->
  PtrAssertions sym ->
  UndefPtrOpTag ->
  AssertedResult sym (Const (Pred sym) w) ->
  IO (Const (Pred sym) w)
annotatePredicate sym (PtrAssertions ref) tag (AssertedResult assertion (Const p)) = do
  (ann, p') <- annotateTerm sym p
  modifyIORef' ref (MapF.insert ann (PtrAssert assertion tag))
  return $ Const p'

annotatePtr ::
  IsSymExprBuilder sym =>
  sym ->
  PtrAssertions sym ->
  UndefPtrOpTag ->
  AssertedResult sym (LLVMPtr' sym w) ->
  IO (LLVMPtr' sym w)
annotatePtr sym (PtrAssertions ref) tag (AssertedResult assertion (LLVMPtr' (LLVMPointer reg off))) = do
  (annReg, reg') <- annotateTerm sym (natToIntegerPure reg)
  (annOff, off') <- annotateTerm sym off
  regNat' <- integerToNat sym reg'
  modifyIORef' ref (MapF.insert annReg (PtrAssert assertion tag))
  modifyIORef' ref (MapF.insert annOff (PtrAssert assertion tag))
  return $ LLVMPtr' (LLVMPointer regNat' off')

-- | Add annotations to the result of potentially undefined pointer operations,
--   but leave them otherwise unmodified.
mkAnnotatedPtrOps ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  IO (UndefinedPtrOps sym, PtrAssertions sym)
mkAnnotatedPtrOps sym = do
  asnsRef <- newIORef MapF.empty
  let asns = PtrAssertions asnsRef
  let classify = UndefPtrClassify $ \e -> case getAnnotation sym e of
        Just ann -> do
          m <- readIORef asnsRef
          case MapF.lookup ann m of
            Just ptrAsn -> return $ Set.singleton (ptrAssertTag ptrAsn)
            Nothing -> return $ Set.empty
        Nothing -> return $ Set.empty
  let uops =
        UndefinedPtrOps
          { undefPtrOff = UndefinedPtrUnOp $ \sym' (AssertedResult cond (SymBV' bv)) _ -> do
              (annBV, bv') <- annotateTerm sym' bv
              modifyIORef' asnsRef (MapF.insert annBV (PtrAssert cond UndefPtrOff))
              return $ SymBV' bv'
          , undefPtrLt =  UndefinedPtrBinOp $ \sym' r _ _ -> annotatePredicate sym' asns UndefPtrLt r
          , undefPtrLeq = UndefinedPtrBinOp $ \sym' r _ _ -> annotatePredicate sym' asns UndefPtrLeq r
          , undefPtrAdd = UndefinedPtrBinOp $ \sym' r _ _ -> annotatePtr sym' asns UndefPtrAdd r
          , undefPtrSub = UndefinedPtrBinOp $ \sym' r _ _ -> annotatePtr sym' asns UndefPtrSub r
          , undefPtrAnd = UndefinedPtrBinOp $ \sym' r _ _ -> annotatePtr sym' asns UndefPtrAnd r
          , undefPtrXor = UndefinedPtrBinOp $ \sym' r _ _ -> annotatePtr sym' asns UndefPtrXor r
          , undefPtrClassify = classify
          }
  return (uops, asns)

-- | Wrap potentially undefined pointer operations in uninterpreted functions
mkUndefinedPtrOps ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  IO (UndefinedPtrOps sym)
mkUndefinedPtrOps sym = do
  (PolyFunMaker offFn, classOff) <- cachedPolyFun sym $ mkOffUF UndefPtrOff
  let
    offPtrFn :: UndefinedPtrUnOp sym (SymBV' sym)
    offPtrFn  = UndefinedPtrUnOp $ \sym' r ptr -> withPtrWidth ptr $ \w -> do
      sptr <- asSymPtr sym' ptr
      resultfn <- offFn sym' w
      undefResultBV <- applyPolyFun resultfn (Empty :> sptr)
      SymBV' <$> baseTypeIte sym' (assertedPred r) (unSymBV $ assertedResult r) undefResultBV

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

ppPtr' :: IsExpr (SymExpr sym) => LLVMPtr sym arch -> Doc ann
ppPtr' ptr@(LLVMPointer r off) 
  | BaseBVRepr w <- exprType off
  = case (asNat r, asBV off) of
  (Just 1, Just off') -> "Stack Slot:" <+> viaShow (BV.asSigned w off')
  _ -> ppPtr ptr

prettyMemOp :: IsExpr (SymExpr sym) => MemOp sym ptrW -> Doc ann
prettyMemOp (MemOp ptr dir cond _sz val _end) =
  viaShow dir <+>
  ppPtr' ptr <+>
  (case dir of Read -> "->" ; Write -> "<-") <+>
  ppPtr val <+>
  case cond of
    Unconditional -> mempty
    Conditional p -> "when" <+> printSymExpr p

-- | Test if a memory operation overlaps with a concretrely-defined
--   region of memory, given as a starting address and a length.
--   For this test, we ignore the pointer region of the memory operation.
memOpOverlapsRegion :: forall sym ptrW.
  (MemWidth ptrW, IsExprBuilder sym) =>
  sym ->
  MemOp sym ptrW {- ^ operation to test -} ->
  MemWord ptrW {- ^ starting address of the region -} ->
  Integer {- ^ length of the region -} ->
  IO (Pred sym)
memOpOverlapsRegion sym (MemOp (LLVMPointer _blk off) _dir _cond w _val _end) addr len =
  -- NB, the algorithm for computing if two intervals (given by a start address and a length)
  -- overlap is not totally obvious. This is taken from the What4 abstract domain definitions,
  -- which have been carefully tested and verified. The cryptol for the definition  is:
  --   overlap : {n} (fin n) => Dom n -> Dom n -> Bit
  --   overlap a b = diff <= b.sz \/ carry diff a.sz
  --     where diff = a.lo - b.lo

  do let aw = addrWidthNatRepr (addrWidthRepr (Proxy @ptrW))
     addr' <- bvLit sym aw (BV.mkBV aw (memWordToUnsigned addr))
     len'  <- bvLit sym aw (BV.mkBV aw len)
     oplen <- bvLit sym aw (BV.mkBV aw (intValue w))

     -- Here the two intervals are given by (off, oplen) and (addr', len')

     diff <- bvSub sym off addr'
     x1 <- bvUle sym diff len'
     (x2, _) <- addUnsignedOF sym diff oplen
     orPred sym x1 x2

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

data RegOp sym arch =
  RegOp (MapF.MapF (ArchReg arch) (PSr.MacawRegEntry sym))

-- | Used for presenting counter-examples that contain all register updates
data TraceEvent sym arch =
    RegOpEvent { traceInstr :: MuxTree sym (Maybe (ArchSegmentOff arch, Text)), _traceRegOp :: RegOp sym arch }
  | TraceMemEvent { traceInstr :: MuxTree sym (Maybe (ArchSegmentOff arch, Text)), _traceMemEvent :: MemEvent sym (ArchAddrWidth arch)}

data GroundInfo tp = 
  GroundInfo {groundTags :: UndefPtrOpTags, groundIsStackRegion :: Bool }

-- instance PG.SymCoercable sym1 sym2 (TraceEvent sym1 arch)

data MemEvent sym ptrW where
  MemOpEvent :: MemOp sym ptrW -> MemEvent sym ptrW
  SyscallEvent :: forall sym ptrW w.
    (1 <= w) =>
    MuxTree sym (Maybe (MemSegmentOff ptrW, Text))
      {- ^ location and dissassembly of the instruction generating this system call -} ->
    SymBV sym w
      {- ^ Value of r0 during this syscall -} ->
    MemEvent sym ptrW
  ExternalCallEvent :: forall sym ptrW ctx.
    Text ->
    Ctx.Assignment (SymBV' sym) ctx
      {- ^ relevant data for this visible call -} ->
    MemEvent sym ptrW

instance OrdF (SymExpr sym) => Eq (MemEvent sym ptrW) where
  a == b = case compare a b of
    EQ -> True
    _ -> False

compareTrees :: OrdF (SymExpr sym) => Ord tp => MuxTree sym tp -> MuxTree sym tp -> Ordering
compareTrees mt1 mt2 = 
  let 
    es1 = map (\(x, p) -> (x, AsOrd p)) $ viewMuxTree mt1
    es2 = map (\(x, p) -> (x, AsOrd p)) $ viewMuxTree mt2
  in compare es1 es2

instance OrdF (SymExpr sym) => Ord (MemEvent sym ptrW) where
  compare a b = case (a,b) of
    (MemOpEvent op1, MemOpEvent op2) -> compare op1 op2
    (SyscallEvent mt1 bv1, SyscallEvent mt2 bv2) -> compareTrees mt1 mt2 <> (toOrdering $ compareF bv1 bv2)
    (ExternalCallEvent nm1 vs1, ExternalCallEvent nm2 vs2) -> 
      compare nm1 nm2 <> (toOrdering $ (compareF vs1 vs2))
    (MemOpEvent{}, _) -> GT
    (SyscallEvent{}, ExternalCallEvent{}) -> GT
    (ExternalCallEvent{}, _) -> LT
    (SyscallEvent{}, MemOpEvent{}) -> LT


addExternalCallEvent ::
  IsExprBuilder sym =>
  OrdF (SymExpr sym) =>
  sym ->
  Text {- ^ name of the external call -} ->
  Ctx.Assignment (SymBV' sym) ctx {- ^ data relevant to the call -} ->
  MemTraceImpl sym ptrW ->
  IO (MemTraceImpl sym ptrW)
addExternalCallEvent sym nm data_ mem = do
  let
    event = ExternalCallEvent nm data_
  memSeq' <- consSymSequence sym event (memSeq mem)
  return $ mem { memSeq = memSeq' }

prettyMemEvent :: (MemWidth ptrW, IsExpr (SymExpr sym)) => MemEvent sym ptrW -> Doc ann
prettyMemEvent (MemOpEvent op) = prettyMemOp op
prettyMemEvent (SyscallEvent i v) =
  case viewMuxTree i of
    [(Just (addr, dis), _)] -> "Syscall At:" <+> viaShow addr <+> pretty dis <> line <> printSymExpr v
    _ -> "Syscall" <+> printSymExpr v
prettyMemEvent (ExternalCallEvent nm vs) = "External Call At:" <+> pretty nm <+> pretty (show vs)
  
prettyMemTraceSeq :: (MemWidth ptrW, IsExpr (SymExpr sym)) => MemTraceSeq sym ptrW -> Doc ann
prettyMemTraceSeq = prettySymSequence prettyMemEvent

-- FIXME: existentially-quantified
data MemTraceImpl sym ptrW = MemTraceImpl 
  { memSeq :: MemTraceSeq sym ptrW
  -- ^ The sequence of memory operations in reverse execution order;
  --   later events appear closer to the front of the sequence.
  , memState :: MemTraceState sym ptrW
  -- ^ the logical contents of memory
  , memCurrentInstr :: MuxTree sym (Maybe (MemSegmentOff ptrW, Text))
  -- ^ the most recent program instruction we encountered (address, dissassembly)
  , memBaseMemory :: Memory ptrW
  -- ^ The "base" memory loaded with the binary. We use this to directly service concrete
  --   reads from read-only memory. INVARIANT: we only mux together memories that were
  --   derived from the same initial memory, so we can assume the base memories are identical.
  , memFullSeq_ :: MemTraceFullSeq sym ptrW
  -- ^ Full sequence of register and memory operations since the start of the block

  }

data MemTraceState sym ptrW = MemTraceState
  { memArrBytes :: MemTraceArrBytes sym ptrW
  , memArrRegions :: MemTraceArrRegions sym ptrW
  }

type MemTraceSeq sym ptrW = SymSequence sym (MemEvent sym ptrW)

--   FIXME: existentially-quantified 'arch' parameter is a workaround for the
--   fact that only 'ptrW' is available in 'MemTraceImpl'
data MemTraceFullSeq sym ptrW = 
  forall arch. (Typeable arch, ptrW ~ ArchAddrWidth arch, RegisterInfo (ArchReg arch)) => 
    MemTraceFullSeq (Proxy arch) (SymSequence sym (TraceEvent sym arch)) 

memFullSeq ::
  forall sym arch.
  Typeable arch =>
  MemTraceImpl sym (ArchAddrWidth arch) -> 
  SymSequence sym (TraceEvent sym arch)
memFullSeq mem | MemTraceFullSeq (_ :: Proxy arch2) s <- memFullSeq_ mem =
  case eqT @arch @arch2 of
    Just Refl -> s
    Nothing -> error "memFullSeq: unexpected architecture"

muxFullSeq :: 
  sym ->
  Pred sym ->
  MemTraceFullSeq sym ptrW ->
  MemTraceFullSeq sym ptrW ->
  IO (MemTraceFullSeq sym ptrW)
muxFullSeq sym p (MemTraceFullSeq (px :: Proxy arch1) a) (MemTraceFullSeq (_ :: Proxy arch2) b) = 
  case eqT @arch1 @arch2 of
    Just Refl -> MemTraceFullSeq px <$> muxSymSequence sym p a b
    Nothing -> fail "muxFullSeq: incompatible architectures"

-- | A map from pointers (a region integer combined with a pointer-width bitvector)
-- to bytes, representing the contents of memory at the given pointer.
type MemTraceArrBytes sym ptrW = MemArrBase sym ptrW (BaseBVType 8)


-- | A map from pointers (a region integer combined with a pointer-width bitvector)
-- to integers, representing the region that should be used when reading a pointer
-- back from memory (each individual byte-width slice of the pointer bitvector is assigned
-- the region of the pointer in this map).
-- TODO: This is a very naive model of pointer regions - there are many situations where
-- this is not enough information to accurately recover the region of a stored pointer.
type MemTraceArrRegions sym ptrW = MemArrBase sym ptrW BaseIntegerType

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
  forall sym arch ptrW.
  ptrW ~ ArchAddrWidth arch =>
  (Typeable arch, SymArchConstraints arch) =>
  IsSymExprBuilder sym =>
  sym ->
  Memory ptrW ->
  AddrWidthRepr ptrW ->
  IO (MemTraceImpl sym ptrW)
initMemTrace sym baseMem Addr32 = do
  arrBytes <- ioFreshConstant sym "InitMemBytes" knownRepr
  arrRegions <- ioFreshConstant sym "InitMemRegions" knownRepr
  sq <- nilSymSequence sym
  fullsq <- MemTraceFullSeq (Proxy @arch) <$> nilSymSequence sym
  return $ MemTraceImpl sq (MemTraceState arrBytes arrRegions) (toMuxTree sym Nothing) baseMem fullsq
initMemTrace sym baseMem Addr64 = do
  arrBytes <- ioFreshConstant sym "InitMemBytes" knownRepr
  arrRegions <- ioFreshConstant sym "InitMemRegions" knownRepr
  sq <- nilSymSequence sym
  fullsq <- MemTraceFullSeq (Proxy @arch) <$> nilSymSequence sym
  return $ MemTraceImpl sq (MemTraceState arrBytes arrRegions) (toMuxTree sym Nothing) baseMem fullsq


mkMemoryBinding ::
  forall sym ptrW.
  IsSymExprBuilder sym =>
  -- | initial memory state (appears in the the given expression when the binding is applied)
  MemTraceState sym ptrW ->
  -- | target memory state (to appear in the resulting expression when the binding is applied)
  MemTraceState sym ptrW ->
  WEH.ExprBindings sym
mkMemoryBinding memSrc memTgt =
  let
    MemTraceState memSrcArrBytes memSrcArrRegions = memSrc
    MemTraceState memTgtArrBytes memTgtArrRegions = memTgt
  in MapF.fromList [MapF.Pair memSrcArrBytes memTgtArrBytes
                   ,MapF.Pair memSrcArrRegions memTgtArrRegions
                   ]


instance IsExprBuilder sym => IntrinsicClass sym "memory_trace" where
  -- TODO: cover other cases with a TypeError
  type Intrinsic sym "memory_trace" (EmptyCtx ::> BVType ptrW) = MemTraceImpl sym ptrW
  muxIntrinsic sym _ _ (Empty :> BVRepr _) p t f = do
    memSeq'   <- muxSymSequence sym p (memSeq t) (memSeq f)
    memArrBytes'   <- baseTypeIte sym p (memArrBytes $ memState t) (memArrBytes $ memState f)
    memArrRegions'   <- baseTypeIte sym p (memArrRegions $ memState t) (memArrRegions $ memState f)
    memInstr' <- mergeMuxTree sym p (memCurrentInstr t) (memCurrentInstr f)
    memFullSeq' <- muxFullSeq sym p (memFullSeq_ t) (memFullSeq_ f)
    -- NB, we assume that the "base" memories are always the same, so we can arbitrarily choose
    -- one to use.
    return $ MemTraceImpl memSeq' (MemTraceState memArrBytes' memArrRegions') memInstr' (memBaseMemory t) memFullSeq'

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
         reg <- freshNat sym (safeSymbol "macawFresh")
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
          unSymBV <$> mkUnUndef (undefPtrOff mkundef) sym (AssertedResult cond (SymBV' off)) ptr

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
  UndefinedPtrBinOp sym (Const (Pred sym)) ->
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
      getConst <$> mkBinUndef mkundef sym (AssertedResult cond (Const result)) (LLVMPointer reg1 off1) (LLVMPointer reg2 off2)

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
  UndefinedPtrBinOp sym (LLVMPtr' sym) ->
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
      unLLVMPtr <$> mkBinUndef mkundef sym (AssertedResult cond (LLVMPtr' result)) (LLVMPointer reg1 off1) (LLVMPointer reg2 off2)

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
  val <- liftIO $ readMemState sym (memState mem) (memBaseMemory mem) ptr memRepr
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
  val <- liftIO $ readMemState sym (memState mem) (memBaseMemory mem) ptr memRepr
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
  let ireg = natToIntegerPure reg
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
  MemWidth ptrW =>
  IsSymExprBuilder sym =>
  MemWidth ptrW =>
  sym ->
  MemTraceState sym ptrW ->
  Memory ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (MS.ToCrucibleType ty))
readMemState sym mem baseMem ptr repr = go 0 repr
  where
  -- This is an incomplete heuristic for determining when the region in storage should
  -- be used (i.e. the read value should be treated like a pointer).
  -- In general it should be possible to read in pointers with smaller reads and
  -- re-assemble them with their region intact. Additionally, a pointer-length read does
  -- not guarantee that the result is actually a valid pointer in the resulting region.
  --
  -- TODO: track enough information in the underlying storage type to be able to
  -- accurately determine when a read (of any length) should be considered a pointer
  -- (with a defined region), and when bitvector operations on these pointers are
  -- region-preserving.
  isPtrReadWidth :: Bool
  isPtrReadWidth = case repr of
    BVMemRepr byteWidth _ |
      Just Refl <- testEquality (natMultiply (knownNat @8) byteWidth) (memWidthNatRepr @ptrW)
        -> True
    _ -> False

  go :: Integer -> MemRepr ty' -> IO (RegValue sym (MS.ToCrucibleType ty'))
  go n (BVMemRepr byteWidth endianness) =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl
        | Refl <- zeroSubEq byteWidth (knownNat @1) ->
          do (_ Ctx.:> reg Ctx.:> off) <- arrayIdx sym ptr n
             blk0 <- natLit sym 0
             ro <- asConcreteReadOnly sym reg off byteWidth endianness baseMem
             (blk, content) <-
               case ro of
                 Just val -> return (blk0, val)
                 Nothing ->
                   do regArrayBytes <- arrayLookup sym (memArrBytes mem) (Ctx.singleton reg)
                      membyte <- arrayLookup sym regArrayBytes (Ctx.singleton off)
                      blk <- case isPtrReadWidth of
                        True -> do
                          regArrayRegion <- arrayLookup sym (memArrRegions mem) (Ctx.singleton reg)
                          regInt <- arrayLookup sym regArrayRegion (Ctx.singleton off)
                          integerToNat sym (WEH.assumePositiveInt sym regInt)
                        False -> return blk0
                      return (blk, membyte)
             return $ LLVMPointer blk content
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

-- | Attempt to service a read from a concrete pointer into a
--   read-only region of memory. If the pointer is not syntactically
--   concrete, or does not point into a read-only region, this will
--   return Nothing.
--
--   This will only attempt to service reads that are 1, 2, 4, or 8
--   bytes long. Only concrete pointers into region 0 will be
--   serviced.
asConcreteReadOnly :: forall sym w ptrW.
  MemWidth ptrW =>
  1 <= w =>
  IsExprBuilder sym =>
  sym ->
  SymInteger sym {- ^ pointer region number -}->
  SymBV sym ptrW {- ^ pointer offset value -} ->
  NatRepr w      {- ^ number of bytes to read -} ->
  Endianness     {- ^ byte order of the read -} ->
  Memory ptrW    {- ^ memory image to read from -} ->
  IO (Maybe (SymBV sym (8*w)))
asConcreteReadOnly sym blk off sz end baseMem =
  case (asInteger blk, asBV off) of
    -- NB, only looking for reads at region 0
    (Just 0, Just off') ->
      do let mw :: MemWord ptrW
             mw = memWord (fromIntegral (BV.asUnsigned off'))
         LeqProof <- return $ leqMulPos (knownNat @8) sz
         let bits = natMultiply (knownNat @8) sz
         case doStaticRead baseMem mw bits end of
           Just bv -> Just <$> bvLit sym bits bv
           Nothing -> return Nothing
    _ -> return Nothing

doStaticRead ::
  forall w ptrW.
  MemWidth ptrW =>
  Memory ptrW ->
  MemWord ptrW ->
  NatRepr w ->
  Endianness ->
  Maybe (BV.BV w)
doStaticRead mem mw w end = do
  segoff <- PM.resolveAbsoluteAddress mem mw
  let addr = segoffAddr segoff
  doStaticReadAddr mem addr w end

doStaticReadAddr ::
  forall w ptrW.
  MemWidth ptrW =>
  Memory ptrW ->
  MemAddr ptrW ->
  NatRepr w ->
  Endianness ->
  Maybe (BV.BV w)
doStaticReadAddr mem addr w end = do
  segOff <- asSegmentOff mem addr
  True <- return $ MMP.isReadonly (segmentFlags $ segoffSegment segOff)
  fmap (BV.mkBV w) $
    case (intValue w, end) of
      (8, _) -> liftErr $ readWord8 mem addr
      (16, BigEndian) -> liftErr $ readWord16be mem addr
      (16, LittleEndian) -> liftErr $ readWord16le mem addr
      (32, BigEndian) -> liftErr $ readWord32be mem addr
      (32, LittleEndian) -> liftErr $ readWord32le mem addr
      (64, BigEndian) -> liftErr $ readWord64be mem addr
      (64, LittleEndian) -> liftErr $ readWord64le mem addr
      _ -> Nothing

  where
    liftErr :: Show e => Integral a => Either e a -> Maybe Integer
    liftErr (Left _err) = Nothing
    liftErr (Right a) = Just (fromIntegral a)

-- | Compute the updated memory state resulting from writing a value to the given address, without
-- accumulating any trace information.
writeMemState ::
  forall sym arch ptrW ty.
  ptrW ~ ArchAddrWidth arch =>
  (Typeable arch, RegisterInfo (ArchReg arch)) =>
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
  fullsq <- MemTraceFullSeq (Proxy @arch) <$> nilSymSequence sym
  let mem = MemTraceImpl sq memSt (toMuxTree sym Nothing) (emptyMemory (addrWidthRepr Proxy)) fullsq
  MemTraceImpl _ memSt' _ _ _ <- execStateT (doMemOpInternal sym Write (Conditional cond) (addrWidthRepr mem) ptr val repr) mem
  return memSt'

-- | Write to the memory array and set the dirty bits on
-- any written addresses
writeMemBV :: forall sym ptrW w.
  1 <= ptrW =>
  IsExprBuilder sym =>
  MemWidth ptrW =>
  sym ->
  MemTraceState sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr (MT.BVType w) ->
  LLVMPtr sym w ->
  IO (MemTraceState sym ptrW)
writeMemBV sym mem_init ptr repr (LLVMPointer region val) = go 0 repr val mem_init
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
        regArrayBytes <- arrayLookup sym (memArrBytes mem) (Ctx.singleton reg)
        regArrayBytes' <- arrayUpdate sym regArrayBytes (Ctx.singleton off) bv
        arrBytes <- arrayUpdate sym (memArrBytes mem) (Ctx.singleton reg) regArrayBytes'
        regionInt <- case (exprType val) of
          BaseBVRepr w | Just Refl <- testEquality w (memWidthNatRepr @ptrW) ->
            return $ natToIntegerPure region
          _ -> intLit sym 0
        regArrayRegions <- arrayLookup sym (memArrRegions mem) (Ctx.singleton reg)
        regArrayRegions' <- arrayUpdate sym regArrayRegions (Ctx.singleton off) regionInt
        arrRegions <- arrayUpdate sym (memArrRegions mem) (Ctx.singleton reg) regArrayRegions'
        return $ mem { memArrBytes = arrBytes, memArrRegions = arrRegions }
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
          mem <- get
          memSt' <- liftIO $ writeMemBV sym (memState mem) ptr repr regVal
          arrBytes <- liftIO $ ifCond sym cond (memArrBytes $ memSt') (memArrBytes $ memState mem)
          arrRegions <- liftIO $ ifCond sym cond (memArrRegions $ memSt') (memArrRegions $ memState mem)
          put $ mem { memState = MemTraceState arrBytes arrRegions }
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


isDir :: MemOpDirection -> MemFootprint sym ptrW -> Bool
isDir dir (MemFootprint _ _ dir' _ _) = dir == dir'

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

filterEvent ::
  IsExprBuilder sym =>
  sym ->
  (MemOp sym ptrW -> IO (Pred sym)) ->
  MemEvent sym ptrW ->
  IO (Maybe (MemEvent sym ptrW), Pred sym)
filterEvent sym f x = case x of
    -- always include system call events
    SyscallEvent{} -> return $ (Nothing, truePred sym)
    -- always include external call events
    ExternalCallEvent{} -> return $ (Nothing, truePred sym)
    
    -- Include memory operations only if they acutally
    -- happen (their condition is true) and if they are
    -- deemed observable by the given filtering function.
    MemOpEvent op@(MemOp ptr dir cond w val end) -> do
      opObservable <- f op
      p <- andPred sym opObservable (getCond sym cond)
      let x' = MemOpEvent (MemOp ptr dir Unconditional w val end)
      return $ (Just x', p)

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
observableEvents sym opIsObservable mem = 
  PEM.updateFilterSeq sym (filterEvent sym opIsObservable) (memSeq mem)


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
  let iRegion = natToIntegerPure region
  mem1StackBytes <- arrayLookup sym (memArrBytes mem1) (Ctx.singleton iRegion)
  mem1StackRegions <- arrayLookup sym (memArrRegions mem1) (Ctx.singleton iRegion)
  mem2Bytes' <- arrayUpdate sym (memArrBytes mem2) (Ctx.singleton iRegion) mem1StackBytes
  mem2Regions' <- arrayUpdate sym (memArrRegions mem2) (Ctx.singleton iRegion) mem1StackRegions

  bytesEq <- isEq sym (memArrBytes mem1) mem2Bytes'
  regionsEq <- isEq sym (memArrRegions mem1) mem2Regions'
  andPred sym bytesEq regionsEq

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
  let iStackRegion = natToIntegerPure stackRegion
  mem1StackBytes <- arrayLookup sym (memArrBytes mem1) (Ctx.singleton iStackRegion)
  mem2StackBytes <- arrayLookup sym (memArrBytes mem2) (Ctx.singleton iStackRegion)
  mem1StackRegions <- arrayLookup sym (memArrRegions mem1) (Ctx.singleton iStackRegion)
  mem2StackRegions <- arrayLookup sym (memArrRegions mem2) (Ctx.singleton iStackRegion)

  bytesEq <- isEq sym mem1StackBytes mem2StackBytes
  regionsEq <- isEq sym mem1StackRegions mem2StackRegions
  andPred sym bytesEq regionsEq


-- | Memory states are exactly equivalent.
memEqExact ::
  forall sym ptrW.
  IsExprBuilder sym =>
  sym ->
  MemTraceState sym ptrW ->
  MemTraceState sym ptrW ->
  IO (Pred sym)
memEqExact sym mem1 mem2 = do
  bytesEq <- isEq sym (memArrBytes mem1) (memArrBytes mem2)
  regionsEq <- isEq sym (memArrRegions mem1) (memArrRegions mem2)
  andPred sym bytesEq regionsEq

instance PEM.ExprMappable2 sym1 sym2 (MemOpCondition sym1) (MemOpCondition sym2) where
  mapExpr2 _sym1 _sym2 f = \case
    Conditional p -> Conditional <$> f p
    Unconditional -> return Unconditional

instance PEM.ExprMappable2 sym1 sym2 (MemOp sym1 w) (MemOp sym2 w) where
  mapExpr2 sym1 sym2 f = \case
    MemOp ptr dir cond w val endian -> do
      ptr' <- WEH.mapExprPtr2 sym1 sym2 f ptr
      val' <- WEH.mapExprPtr2 sym1 sym2 f val
      cond' <- PEM.mapExpr2 sym1 sym2 f cond
      return $ MemOp ptr' dir cond' w val' endian

instance PEM.ExprMappable2 sym1 sym2 (MemEvent sym1 w) (MemEvent sym2 w) where
  mapExpr2 sym1 sym2 f = \case
    MemOpEvent op -> MemOpEvent <$> PEM.mapExpr2 sym1 sym2 f op
    SyscallEvent i arg -> SyscallEvent i <$> f arg
    -- MuxTree is unmodified since it has no symbolic expressions
    ExternalCallEvent nm vs -> ExternalCallEvent nm <$> TFC.traverseFC (PEM.mapExpr2 sym1 sym2 f) vs

instance (MemWidth ptrW, IsExpr (SymExpr sym)) => Pretty (MemEvent sym ptrW) where
  pretty ev = prettyMemEvent ev



instance PEM.ExprMappable2 sym1 sym2 (MemTraceFullSeq sym1 ptrW) (MemTraceFullSeq sym2 ptrW) where
  mapExpr2 sym1 sym2 f (MemTraceFullSeq px s) = MemTraceFullSeq px <$> PEM.mapExpr2 sym1 sym2 f s

instance PEM.ExprMappable2 sym1 sym2 (MemTraceImpl sym1 w) (MemTraceImpl sym2 w) where
  mapExpr2 sym1 sym2 f mem = do
    memSeq' <- PEM.mapExpr2 sym1 sym2 f (memSeq mem)
    memState' <- PEM.mapExpr2 sym1 sym2 f $ memState mem
    memInstr' <- PEM.mapExpr2 sym1 sym2 f $ memCurrentInstr mem
    memFullSeq' <- PEM.mapExpr2 sym1 sym2 f (memFullSeq_ mem)
    return $ MemTraceImpl memSeq' memState' memInstr' (memBaseMemory mem) memFullSeq'

instance PEM.ExprMappable2 sym1 sym2 (MemTraceState sym1 w) (MemTraceState sym2 w) where
  mapExpr2 _sym1 _sym2 f memSt = do
    memArrBytes' <- f $ memArrBytes memSt
    memArrRegions' <- f $ memArrRegions memSt
    return $ MemTraceState memArrBytes' memArrRegions'

instance PEM.ExprMappable2 sym1 sym2 (MemFootprint sym1 arch) (MemFootprint sym2 arch) where
  mapExpr2 sym1 sym2 f (MemFootprint ptr w dir cond end) = do
    ptr' <- WEH.mapExprPtr2 sym1 sym2 f ptr
    cond' <- PEM.mapExpr2 sym1 sym2 f cond
    return $ MemFootprint ptr' w dir cond' end

instance RegisterInfo (ArchReg arch) => PEM.ExprMappable2 sym1 sym2 (RegOp sym1 arch) (RegOp sym2 arch) where
  mapExpr2 sym1 sym2 f (RegOp rm) = 
    (RegOp . PEM.unExprMapFElems) <$> PEM.mapExpr2 sym1 sym2 f (PEM.ExprMapFElems rm)

instance PEM.ExprMappable2 sym1 sym2 (MemSegmentOff arch) (MemSegmentOff arch) where
  mapExpr2 _ _ _ = return 

instance PEM.ExprMappable2 sym1 sym2 Text Text where
  mapExpr2 _ _ _ = return 

instance RegisterInfo (ArchReg arch) => PEM.ExprMappable2 sym1 sym2 (TraceEvent sym1 arch) (TraceEvent sym2 arch) where
  mapExpr2 sym1 sym2 f ev = case ev of
    RegOpEvent i rop -> RegOpEvent <$> PEM.mapExpr2 sym1 sym2 f i <*> PEM.mapExpr2 sym1 sym2 f rop
    TraceMemEvent i mev -> TraceMemEvent <$> PEM.mapExpr2 sym1 sym2 f i <*> PEM.mapExpr2 sym1 sym2 f mev