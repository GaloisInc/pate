{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
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
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.TypeNats (KnownNat)

import           Data.Parameterized.Classes

import qualified Data.Macaw.Types as MT
import Data.Macaw.CFG.AssignRhs (ArchAddrWidth, MemRepr(..))
import Data.Macaw.Memory (AddrWidthRepr(..), Endianness(..), addrWidthClass, addrWidthNatRepr)
import Data.Macaw.Symbolic.Backend (EvalStmtFunc, MacawArchEvalFn(..))
import Data.Macaw.Symbolic ( MacawStmtExtension(..), MacawExt
                           , GlobalMap, MacawSimulatorState(..)
                           , ToCrucibleType, evalMacawExprExtension
                           , IsMemoryModel(..)
                           , MacawBlockEnd(..)
                           )
import Data.Macaw.Symbolic.MemOps ( doGetGlobal )
import Data.Parameterized.Context (pattern (:>), pattern Empty, Assignment)
import qualified Data.Parameterized.Map as MapF
import Data.Text (pack)
import Lang.Crucible.Backend (IsSymInterface, assert)
import Lang.Crucible.CFG.Common (GlobalVar, freshGlobalVar)
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM.MemModel (LLVMPointerType, LLVMPtr, pattern LLVMPointer, llvmPointer_bv)
import Lang.Crucible.Simulator.ExecutionTree (CrucibleState, ExtensionImpl(..), actFrame, gpGlobals, stateSymInterface, stateTree)
import Lang.Crucible.Simulator.GlobalState (insertGlobal, lookupGlobal)
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass(..), IntrinsicMuxFn(..), IntrinsicTypes)
import Lang.Crucible.Simulator.RegMap (RegEntry(..))
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Types ((::>), BoolType, BVType, EmptyCtx, IntrinsicType, SymbolicArrayType,
                            SymbolRepr, TypeRepr(BVRepr), knownSymbol)
import What4.Expr.Builder (ExprBuilder)
import qualified What4.Expr.GroundEval as W4G
import What4.Interface -- (NatRepr, knownRepr, BaseTypeRepr(..), SolverSymbol, userSymbol, freshConstant, natLit)

----------------------------------
-- Reify jump kind as a crucible global



type ExitClassify arch = IntrinsicType "exit_classify" EmptyCtx

data ExitClassifyImpl sym =
  ExitClassifyImpl (SymExpr sym (BaseStructType (EmptyCtx ::> BaseBoolType ::> BaseBoolType)))

instance IsExprBuilder sym => IntrinsicClass sym "exit_classify" where
  type Intrinsic sym "exit_classify" EmptyCtx = ExitClassifyImpl sym
  muxIntrinsic sym _ _ Empty p (ExitClassifyImpl t) (ExitClassifyImpl f) = do
    muxed <- baseTypeIte sym p t f
    return $ ExitClassifyImpl muxed
  muxIntrinsic _ _ _ _ _ _ _ = error "Unexpected operands in exit_classify mux"

exitCaseToImpl ::
  IsSymInterface sym =>
  sym ->
  ExitCase ->
  IO (ExitClassifyImpl sym)
exitCaseToImpl sym classk = ExitClassifyImpl <$> case classk of
  ExitCall -> mkStruct sym (Empty :> truePred sym :> falsePred sym)
  ExitReturn -> mkStruct sym (Empty :> falsePred sym :> truePred sym)
  ExitArch -> mkStruct sym (Empty :> truePred sym :> truePred sym)
  ExitUnknown -> mkStruct sym (Empty :> falsePred sym :> falsePred sym)


groundExitCase ::
  sym ~ (ExprBuilder t s f) =>
  W4G.GroundEvalFn t ->
  ExitClassifyImpl sym ->
  IO ExitCase
groundExitCase (W4G.GroundEvalFn fn) (ExitClassifyImpl e) = do
  (Empty :> W4G.GVW b1 :> W4G.GVW b2) <- fn e
  return $ case (b1, b2) of
    (True, False) -> ExitCall
    (False, True) -> ExitReturn
    (True, True) -> ExitArch
    (False, False) -> ExitUnknown

data ExitCase = ExitCall | ExitReturn | ExitArch | ExitUnknown
  deriving (Eq, Ord, Show)

blockEndToExitCase :: MacawBlockEnd arch -> ExitCase
blockEndToExitCase blkend = case blkend of
  MacawBlockEndCall -> ExitCall
  MacawBlockEndReturn -> ExitReturn
  MacawBlockEndArch -> ExitArch
  _ -> ExitUnknown


exitCases ::
  IsSymInterface sym =>
  sym ->
  ExitClassifyImpl sym ->
  BaseTypeRepr tp ->
  (ExitCase -> IO (SymExpr sym tp)) ->
  IO (SymExpr sym tp)
exitCases sym (ExitClassifyImpl jclass) repr f = do
  let
    mkCase classk = do
      ExitClassifyImpl jclass' <- exitCaseToImpl sym classk
      test <- isEq sym jclass jclass'
      expr <- f classk
      return (test, expr)

  (testUnknown, exprUnknown) <- mkCase ExitUnknown
  (testCall, exprCall) <- mkCase ExitCall
  (testReturn, exprReturn) <- mkCase ExitReturn
  (testArch, exprArch) <- mkCase ExitArch

  default_ <- ioFreshConstant sym "impossible" repr

  unknownCase <- baseTypeIte sym testUnknown exprUnknown default_
  callCase <- baseTypeIte sym testCall exprCall unknownCase
  returnCase <- baseTypeIte sym testReturn exprReturn callCase
  baseTypeIte sym testArch exprArch returnCase



-- | Like 'macawExtensions', but with an alternative memory model that records
-- memory operations without trying to carefully guess the results of
-- performing them.
macawTraceExtensions ::
  (IsSymInterface sym, KnownNat (ArchAddrWidth arch), sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn sym (MemTrace arch) arch ->
  GlobalVar (MemTrace arch) ->
  GlobalVar (ExitClassify arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  ExtensionImpl (MacawSimulatorState sym) sym (MacawExt arch)
macawTraceExtensions archStmtFn mvar evar globs =
  ExtensionImpl
    { extensionEval = evalMacawExprExtension
    , extensionExec = execMacawStmtExtension archStmtFn mvar evar globs
    }


data MemOpCondition sym
  = Unconditional
  | Conditional (Pred sym)


deriving instance Show (Pred sym) => Show (MemOpCondition sym)

data MemOpDirection = Read | Write deriving (Bounded, Enum, Eq, Ord, Read, Show)

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
     , Just Refl <- testEquality addrR addrR'
     , Just Refl <- testEquality addrO addrO'
     , Just Refl <- testEquality valR valR'
     , Just Refl <- testEquality valO valO'
    = cond == cond' && dir == dir' && end == end'
  MergeOps p opsT opsF == MergeOps p' opsT' opsF'
    | Just Refl <- testEquality p p'
    = opsT == opsT' && opsF == opsF'
  _ == _ = False

data MemTraceImpl sym ptrW = MemTraceImpl
  { memSeq :: MemTraceSeq sym ptrW
  , memArr :: MemTraceArr sym ptrW
  }

instance TestEquality (SymExpr sym) => Eq (MemTraceImpl sym ptrW) where
  (MemTraceImpl s1 arr1) == (MemTraceImpl s2 arr2)
    | Just Refl <- testEquality arr1 arr2
    = s1 == s2
  _ == _ = False

type MemTraceSeq sym ptrW = Seq (MemOp sym ptrW)
type MemTraceArr sym ptrW =
  RegValue sym (SymbolicArrayType (EmptyCtx ::> BaseNatType ::> (BaseBVType ptrW)) (BaseBVType 8))
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

mkExitClassVar ::
  forall arch.
  HandleAllocator ->
  IO (GlobalVar (ExitClassify arch))
mkExitClassVar ha = freshGlobalVar ha (pack "exit_classify") knownRepr

initMemTrace ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  IO (MemTraceImpl sym ptrW)
initMemTrace sym Addr32 = do
  arr <- ioFreshConstant sym "InitMem" knownRepr
  return $ MemTraceImpl mempty arr
initMemTrace sym Addr64 = do
  arr <- ioFreshConstant sym "InitMem" knownRepr
  return $ MemTraceImpl mempty arr

initExitClass ::
  IsSymInterface sym =>
  sym ->
  IO (ExitClassifyImpl sym)
initExitClass sym = do
  bs <- ioFreshConstant sym "InitExitClass" knownRepr
  return $ ExitClassifyImpl bs

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
    arr <- baseTypeIte sym p (memArr t) (memArr f)
    return $ MemTraceImpl s arr
  muxIntrinsic _ _ _ _ _ _ _ = error "Unexpected operands in memory_trace mux"

memTraceIntrinsicTypes :: IsSymInterface (ExprBuilder t st fs) => IntrinsicTypes (ExprBuilder t st fs)
memTraceIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "exit_classify") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "memory_trace") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn
  $ MapF.empty

type MacawTraceEvalStmtFunc sym arch = EvalStmtFunc (MacawStmtExtension arch) (MacawSimulatorState sym) sym (MacawExt arch)

execMacawStmtExtension ::
  forall sym arch t st fs. (IsSymInterface sym, KnownNat (ArchAddrWidth arch), sym ~ ExprBuilder t st fs) =>
  MacawArchEvalFn sym (MemTrace arch) arch ->
  GlobalVar (MemTrace arch) ->
  GlobalVar (ExitClassify arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  MacawTraceEvalStmtFunc sym arch
execMacawStmtExtension (MacawArchEvalFn archStmtFn) mvar jvar globs stmt
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
    MacawFreshSymbolic _t -> error "MacawFreshSymbolic is unsupported in the trace memory model"
    MacawLookupFunctionHandle _typeReps _registers -> error "MacawLookupFunctionHandle is unsupported in the trace memory model"

    MacawArchStmtExtension archStmt -> archStmtFn mvar globs archStmt

    MacawArchStateUpdate{} -> \cst -> pure ((), cst)
    MacawInstructionStart{} -> \cst -> pure ((), cst)

    MacawBlockEnd blkend -> liftToCrucibleState jvar $ \sym -> do
      let classk = blockEndToExitCase blkend
      eImpl <- liftIO $ exitCaseToImpl sym classk
      put eImpl

    PtrEq w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regEq <- natEq sym reg reg'
      offEq <- bvEq sym off off'
      andPred sym regEq offEq

    PtrLeq w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      whoKnows <- ioFreshConstant sym "PtrLeq_across_allocations" knownRepr
      regEq <- natEq sym reg reg'
      offLeq <- bvUle sym off off'
      itePred sym regEq offLeq whoKnows

    PtrLt w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      whoKnows <- ioFreshConstant sym "PtrLt_across_allocations" knownRepr
      regEq <- natEq sym reg reg'
      offLt <- bvUlt sym off off'
      itePred sym regEq offLt whoKnows

    PtrMux w (RegEntry _ p) x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      reg'' <- natIte sym p reg reg'
      off'' <- bvIte sym p off off'
      pure (LLVMPointer reg'' off'')

    PtrAdd w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regZero <- isZero sym reg
      regZero' <- isZero sym reg'
      someZero <- orPred sym regZero regZero'
      assert sym someZero $ AssertFailureSimError
        "PtrAdd: expected ptr+constant, saw ptr+ptr"
        "When doing pointer addition, we expect at least one of the two arguments to the addition to have a region of 0 (i.e. not be the result of allocating memory). Both arguments had non-0 regions."

      reg'' <- cases sym
        [ (pure regZero, pure reg')
        , (pure regZero', pure reg)
        ]
        (ioFreshConstant sym "PtrAdd_both_ptrs_region" knownRepr)
      off'' <- cases sym
        [ (pure someZero, bvAdd sym off off')
        ]
        (ioFreshConstant sym "PtrAdd_both_ptrs_offset" knownRepr)
      pure (LLVMPointer reg'' off'')

    PtrSub w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regZero' <- isZero sym reg'
      regEq <- natEq sym reg reg'
      compatSub <- orPred sym regZero' regEq
      assert sym compatSub $ AssertFailureSimError
        "PtrSub: strange mix of allocation regions"
        "When doing pointer subtraction, we expect that either the two pointers are from the same allocation region or the negated one is actually a constant. Other mixings of allocation regions have arbitrary behavior."

      reg'' <- cases sym
        [ (pure regZero', pure reg)
        , (pure regEq, natLit sym 0)
        ]
        (ioFreshConstant sym "PtrSub_region_mismatch" knownRepr)
      off'' <- cases sym
        [ (pure compatSub, bvSub sym off off')
        ]
        (ioFreshConstant sym "PtrSub_region_mismatch" knownRepr)
      pure (LLVMPointer reg'' off'')

    PtrAnd w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regZero <- isZero sym reg
      regZero' <- isZero sym reg'
      someZero <- orPred sym regZero regZero'
      assert sym someZero $ AssertFailureSimError
        "PtrAnd: expected ptr&constant, saw ptr&ptr"
        "When doing pointer addition, we expect at least one of the two arguments to the addition to have a region of 0 (i.e. not be the result of allocating memory). Both arguments had non-0 regions."

      reg'' <- cases sym
        [ (pure regZero, pure reg')
        , (pure regZero', pure reg)
        ]
        (ioFreshConstant sym "PtrAnd_both_ptrs_region" knownRepr)
      off'' <- cases sym
        [ (pure someZero, bvAndBits sym off off')
        ]
        (ioFreshConstant sym "PtrAnd_both_ptrs_offset" knownRepr)
      pure (LLVMPointer reg'' off'')

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

getGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> IO (RegValue sym mem)
getGlobalVar cst gv = case lookupGlobal gv (cst ^. stateTree . actFrame . gpGlobals) of
  Just val -> return val
  Nothing -> fail ("Global variable not initialized: " ++ show gv)

setGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> RegValue sym mem -> CrucibleState s sym ext rtp blocks r ctx
setGlobalVar cst gv val = cst & stateTree . actFrame . gpGlobals %~ insertGlobal gv val

ptrOp ::
  AddrWidthRepr w ->
  RegEntry sym (LLVMPointerType w) ->
  RegEntry sym (LLVMPointerType w) ->
  (1 <= w => sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
ptrOp w (RegEntry _ (LLVMPointer region offset)) (RegEntry _ (LLVMPointer region' offset')) f =
  addrWidthsArePositive w $ readOnlyWithSym $ \sym -> f sym region offset region' offset'

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

andIOPred :: IsExprBuilder sym => sym -> IO (Pred sym) -> IO (Pred sym) -> IO (Pred sym)
andIOPred sym p1_ p2_ = do
  p1 <- p1_
  p2 <- p2_
  andPred sym p1 p2

orIOPred :: IsExprBuilder sym => sym -> IO (Pred sym) -> IO (Pred sym) -> IO (Pred sym)
orIOPred sym p1_ p2_ = do
  p1 <- p1_
  p2 <- p2_
  orPred sym p1 p2


doReadMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doReadMem sym ptrW ptr memRepr = addrWidthClass ptrW $ do
  arr <- gets memArr
  val <- liftIO $ readMemArr sym arr ptr memRepr
  doMemOpInternal sym Read Unconditional ptrW ptr val memRepr
  pure val

doCondReadMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  RegValue sym (ToCrucibleType ty) ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doCondReadMem sym cond def ptrW ptr memRepr = addrWidthClass ptrW $ do
  arr <- gets memArr
  val <- liftIO $ readMemArr sym arr ptr memRepr
  doMemOpInternal sym Read (Conditional cond) ptrW ptr val memRepr
  liftIO $ iteDeep sym cond val def memRepr

doWriteMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doWriteMem sym = doMemOpInternal sym Write Unconditional

doCondWriteMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doCondWriteMem sym cond = doMemOpInternal sym Write (Conditional cond)

ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrAdd sym _w (LLVMPointer base off1) off2 =
  LLVMPointer base <$> bvAdd sym off1 off2

-- | Calculate an index into the memory array from a pointer
arrayIdx ::
  1 <= ptrW =>
  IsSymInterface sym =>
  sym ->
  LLVMPtr sym ptrW ->
  Integer ->
  IO (Assignment (SymExpr sym) (EmptyCtx ::> BaseNatType ::> BaseBVType ptrW))
arrayIdx sym ptr@(LLVMPointer reg off) off' = do
  let w = ptrWidth ptr
  offBV <- bvLit sym w $ BV.mkBV w off'
  bvIdx <- bvAdd sym off offBV
  return $ Empty :> reg :> bvIdx

concatPtrs ::
  1 <= w1 =>
  1 <= w2 =>
  IsSymInterface sym =>
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
  IsSymInterface sym =>
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

-- | Read a packed value from the underlying array
readMemArr :: forall sym ptrW ty.
  1 <= ptrW =>
  IsSymInterface sym =>
  sym ->
  MemTraceArr sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
readMemArr sym arr ptr = go 0 where
  go :: Integer -> MemRepr ty' -> IO (RegValue sym (ToCrucibleType ty'))
  go n (BVMemRepr byteWidth endianness) =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl
        | Refl <- zeroSubEq byteWidth (knownNat @1) -> do
          idx <- arrayIdx sym ptr n
          content <- arrayLookup sym arr idx
          llvmPointer_bv sym content
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

writeMemArr :: forall sym ptrW w.
  1 <= ptrW =>
  IsSymInterface sym =>
  sym ->
  MemTraceArr sym ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr (MT.BVType w) ->
  SymBV sym w ->
  IO (MemTraceArr sym ptrW)
writeMemArr sym arr_init ptr repr val = go 0 repr val arr_init where
  go ::
    Integer ->
    MemRepr (MT.BVType w') ->
    SymBV sym w' ->
    MemTraceArr sym ptrW ->
    IO (MemTraceArr sym ptrW)
  go n (BVMemRepr byteWidth endianness) bv arr =
    case isZeroOrGT1 (decNat byteWidth) of
      Left Refl -> do
        idx <- arrayIdx sym ptr n
        Refl <- return $ zeroSubEq byteWidth (knownNat @1)
        arrayUpdate sym arr idx bv
      Right LeqProof -> do
        let
          byteWidth' = decNat byteWidth
          repr' = BVMemRepr byteWidth' endianness
          reprHead = BVMemRepr (knownNat @1) endianness
        LeqProof <- return $ oneSubEq byteWidth
        (hd, tl) <- chunkBV sym endianness byteWidth bv
        arr1 <- go n reprHead hd arr
        go (n + 1) repr' tl arr1


doMemOpInternal :: forall sym ptrW ty.
  IsSymInterface sym =>
  sym ->
  MemOpDirection ->
  MemOpCondition sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doMemOpInternal sym dir cond ptrW = go where
  go :: LLVMPtr sym ptrW -> RegValue sym (ToCrucibleType ty') -> MemRepr ty' -> StateT (MemTraceImpl sym ptrW) IO ()
  go ptr@(LLVMPointer reg off) regVal = \case
    repr@(BVMemRepr byteWidth endianness)
      | LeqProof <- mulMono (knownNat @8) byteWidth
      -> addrWidthsArePositive ptrW $ do
      MemTraceImpl s arr <- get
      let s' = s Seq.:|> MemOp ptr dir cond byteWidth regVal endianness
      arr' <- case dir of
        Read -> return arr
        Write -> do
          LLVMPointer _ rawBv <- return regVal
          liftIO $ writeMemArr sym arr ptr repr rawBv
      put $ MemTraceImpl s' arr'
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
  RegValue sym (ToCrucibleType ty) ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
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

andCond ::
  IsSymInterface sym =>
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
  IsSymInterface sym =>
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
  IsSymInterface sym =>
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
    MemFootprint sym ptrW

memFootDir :: MemFootprint sym ptrW -> MemOpDirection
memFootDir (MemFootprint _ _ dir _) = dir

instance TestEquality (SymExpr sym) => Eq (MemFootprint sym ptrW) where
  (MemFootprint (LLVMPointer reg1 off1) sz1 dir1 cond1) == (MemFootprint (LLVMPointer reg2 off2) sz2 dir2 cond2)
   | Just Refl <- testEquality reg1 reg2
   , Just Refl <- testEquality off1 off2
   , Just Refl <- testEquality sz1 sz2
   = cond1 == cond2 && dir1 == dir2
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemFootprint sym ptrW) where
  compare (MemFootprint (LLVMPointer reg1 off1) sz1 dir1 cond1) (MemFootprint (LLVMPointer reg2 off2) sz2 dir2 cond2) =
    compare dir1 dir2 <>
    (toOrdering $ compareF reg1 reg2) <>
    (toOrdering $ compareF off1 off2) <>
    (toOrdering $ compareF sz1 sz2) <>
    compare cond1 cond2


memOpFootprint ::
  MemOp sym ptrW ->
  MemFootprint sym ptrW
memOpFootprint (MemOp ptr dir cond w _ _) = MemFootprint ptr w dir cond
memOpFootprint _ = error "Unexpected merge op"

traceFootprint ::
  IsSymInterface sym =>
  sym ->
  MemTraceSeq sym ptrW ->
  IO (Set (MemFootprint sym ptrW))
traceFootprint sym mem = do
  footprints <- (fmap memOpFootprint) <$> flatMemOps sym mem
  return $ foldl' (\a b -> Set.insert b a) mempty footprints

equalAt :: IsSymInterface sym =>
  1 <= ptrW =>
  sym ->
  (forall w. LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)) ->
  MemTraceArr sym ptrW ->
  MemTraceArr sym ptrW ->
  MemFootprint sym ptrW ->
  IO (Pred sym)
equalAt sym eqRel arr1 arr2 (MemFootprint ptr w _ cond) = do
  let repr = BVMemRepr w BigEndian
  val1 <- readMemArr sym arr1 ptr repr
  val2 <- readMemArr sym arr2 ptr repr
  cond' <- case cond of
    Unconditional -> return $ truePred sym
    Conditional c -> return c
  eqP <- eqRel val1 val2
  impliesPred sym cond' eqP

-- | Return a predicate that is true if the resulting memory
-- states are equivalent, up to reordering of individual writes
-- and the given equivalence relation
equivWrites ::
  forall sym ptrW.
  IsSymInterface sym =>
  1 <= ptrW =>
  sym ->
  (forall w. LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)) ->
  MemTraceImpl sym ptrW ->
  MemTraceImpl sym ptrW ->
  IO (Pred sym)
equivWrites sym eqRel mem1 mem2 = do
  foot1 <- traceFootprint sym (memSeq mem1)
  foot2 <- traceFootprint sym (memSeq mem2)
  let foot = Set.union foot1 foot2
  foldM addFoot (truePred sym) foot
  where
    addFoot ::
      Pred sym ->
      MemFootprint sym ptrW ->
      IO (Pred sym)
    addFoot p f | Write <- memFootDir f = do
      p' <- equalAt sym eqRel (memArr mem1) (memArr mem2) f
      andPred sym p p'
    addFoot _ _ = return $ truePred sym
