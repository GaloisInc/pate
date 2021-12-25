{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | These operations support representing undefined values in the memory model
--
-- The trace memory model is intended to support verifying the equivalence of
-- programs, even when they contain undefined operations.  In cases where we
-- cannot resolve an operation because its semantics are undefined, we use these
-- operations to explicitly represent the undefined-ness so that we can prove
-- equi-undefined behavior.
module Pate.Memory.Trace.Undefined (
    UndefinedPtrOps(..)
  , UndefPtrOpTag
  , mkUndefinedPtrOps
  ) where

import qualified Data.IORef as IORef
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Set as Set
import           GHC.TypeLits ( Nat, type (<=) )
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM

-- | Wraps a function which is used to produce an "undefined" predicate that
-- may result from a binary pointer operation.
-- The given predicate is true when the operation is defined. i.e if this predicate
-- is true then this undefined value is unused. The two other arguments are the original inputs to the binary pointer operation.
newtype UndefinedPtrPredOp sym =
  UndefinedPtrPredOp
    { mkUndefPred :: forall w
                   . sym
                   -> LCLM.LLVMPtr sym w
                   -> LCLM.LLVMPtr sym w
                   -> IO (WI.Pred sym)
    }

-- | Wraps a function which is used to produce an "undefined" pointer that
-- may result from a binary pointer operation.
-- The given predicate is true when the operation is defined. i.e if this predicate
-- is true then this undefined value is unused. The two other arguments are the original inputs to the binary pointer operation.
newtype UndefinedPtrBinOp sym =
  UndefinedPtrBinOp
    { mkUndefPtr :: forall w
                  . sym
                 -> LCLM.LLVMPtr sym w
                 -> LCLM.LLVMPtr sym w
                 -> IO (LCLM.LLVMPtr sym w)
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

-- | Classify an expression as representing an undefined pointer.
newtype UndefPtrClassify sym =
  UndefPtrClassify
    { classifyExpr :: forall tp. WI.SymExpr sym tp -> IO (Set.Set UndefPtrOpTag) }

instance Semigroup (UndefPtrClassify sym) where
  f1 <> f2 = UndefPtrClassify $ \e -> do
    class1 <- classifyExpr f1 e
    class2 <- classifyExpr f2 e
    return $ class1 <> class2

instance Monoid (UndefPtrClassify sym) where
  mempty = UndefPtrClassify $ \_ -> return mempty

-- | A collection of functions used to produce undefined values for each pointer operation.
data UndefinedPtrOps sym =
  UndefinedPtrOps
    { undefPtrOff :: (forall w. sym -> LCLM.LLVMPtr sym w -> IO (WI.SymBV sym w))
    , undefPtrLt :: UndefinedPtrPredOp sym
    , undefPtrLeq :: UndefinedPtrPredOp sym
    , undefPtrAdd :: UndefinedPtrBinOp sym
    , undefPtrSub :: UndefinedPtrBinOp sym
    , undefPtrAnd :: UndefinedPtrBinOp sym
    , undefPtrXor :: UndefinedPtrBinOp sym
    , undefPtrClassify :: UndefPtrClassify sym
    }

withPtrWidth
  :: (LCB.IsSymInterface sym)
  => LCLM.LLVMPtr sym w
  -> (1 <= w => PN.NatRepr w -> a)
  -> a
withPtrWidth (LCLM.LLVMPointer _blk bv) f
  | WT.BaseBVRepr w <- WI.exprType bv = f w

-- | Wrapping a pointer as a struct, so that it may be represented as the result
-- of an uninterpreted function.  We need to do this because LLVMPointer is not
-- a base type; we translate it to this format when necessary
type BasePtrType w = WT.BaseStructType (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType w)
type SymPtr sym w = WI.SymExpr sym (BasePtrType w)

asSymPtr
  :: (LCB.IsSymInterface sym)
  => sym
  -> LCLM.LLVMPtr sym w
  -> IO (SymPtr sym w)
asSymPtr sym (LCLM.LLVMPointer reg off) = do
  ireg <- WI.natToInteger sym reg
  WI.mkStruct sym (Ctx.Empty Ctx.:> ireg Ctx.:> off)

-- | Convert the other way: sym pointer back into LLVM pointer
fromSymPtr
  :: (LCB.IsSymInterface sym)
  => sym
  -> SymPtr sym w
  -> IO (LCLM.LLVMPtr sym w )
fromSymPtr sym sptr = do
  reg <- WI.structField sym sptr Ctx.i1of2
  off <- WI.structField sym sptr Ctx.i2of2
  nreg <- WI.integerToNat sym reg
  return $ LCLM.LLVMPointer nreg off


type AnyNat = 0

-- | Defines how a given type can be concretized to a specific type-level nat.
-- This allows us to easily describe a type that is polymorphic in one natural,
-- using existing type constructors.
type family NatAbs tp (w :: Nat) :: WT.BaseType where
  NatAbs (BasePtrType AnyNat) w' = BasePtrType w'
  NatAbs (BasePtrType w) _ = BasePtrType w
  NatAbs (WT.BaseBVType AnyNat) w' = WT.BaseBVType w'
  NatAbs (WT.BaseBVType w) _ = WT.BaseBVType w
  NatAbs WT.BaseBoolType _ = WT.BaseBoolType
  NatAbs WT.BaseIntegerType _ = WT.BaseIntegerType

type family NatAbsCtx tp (w :: Nat) :: Ctx.Ctx WT.BaseType where
  NatAbsCtx Ctx.EmptyCtx w = Ctx.EmptyCtx
  NatAbsCtx (ctx Ctx.::> tp) w' = NatAbsCtx ctx w' Ctx.::> NatAbs tp w'

data PolyFun sym args ret (w :: Nat) where
  PolyFun ::
    { polyFunClassify :: UndefPtrClassify sym
    , applyPolyFun :: Ctx.Assignment (WI.SymExpr sym) (NatAbsCtx args w) -> IO (WI.SymExpr sym (NatAbs ret w))
    }
    -> PolyFun sym args ret w

newtype PolyFunMaker sym args ret =
  PolyFunMaker (forall w. 1 <= w => sym -> PN.NatRepr w -> IO (PolyFun sym args ret w))

-- avoiding struct-indexed arrays, which are unsupported by ground evaluation
type family FlatStructs tp :: Ctx.Ctx WT.BaseType where
  FlatStructs (WT.BaseStructType ctx) = FlatStructsCtx ctx
  FlatStructs (WT.BaseBVType w) = Ctx.EmptyCtx Ctx.::> (WT.BaseBVType w)
  FlatStructs WT.BaseIntegerType = Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType
  FlatStructs WT.BaseBoolType = Ctx.EmptyCtx Ctx.::> WT.BaseBVType 1

type family FlatStructsCtx ctx :: Ctx.Ctx WT.BaseType where
  FlatStructsCtx Ctx.EmptyCtx = Ctx.EmptyCtx
  FlatStructsCtx (ctx Ctx.::> tp) = FlatStructsCtx ctx Ctx.<+> FlatStructs tp

flattenStructRepr :: Ctx.Assignment WT.BaseTypeRepr ctx -> Ctx.Assignment WT.BaseTypeRepr (FlatStructsCtx ctx)
flattenStructRepr Ctx.Empty = Ctx.Empty
flattenStructRepr (ctx Ctx.:> WT.BaseStructRepr ctx') = flattenStructRepr ctx Ctx.<++> flattenStructRepr ctx'
flattenStructRepr (ctx Ctx.:> (WT.BaseBVRepr w)) = flattenStructRepr ctx Ctx.:> (WT.BaseBVRepr w)
flattenStructRepr (ctx Ctx.:> WT.BaseIntegerRepr) = flattenStructRepr ctx Ctx.:> WT.BaseIntegerRepr
flattenStructRepr (ctx Ctx.:> WT.BaseBoolRepr) = flattenStructRepr ctx Ctx.:> WT.BaseBVRepr (PN.knownNat @1)
flattenStructRepr tp = error ("flattenStructRepr: unsupported type:" ++ show tp)

flattenStructs
  :: (LCB.IsSymInterface sym)
  => sym
  -> Ctx.Assignment (WI.SymExpr sym) ctx
  -> IO (Ctx.Assignment (WI.SymExpr sym) (FlatStructsCtx ctx))
flattenStructs sym (ctx Ctx.:> e) = do
  ctx_flat <- flattenStructs sym ctx
  case WI.exprType e of
    WT.BaseStructRepr ctx' -> do
      fields <- Ctx.traverseWithIndex (\idx _ -> WI.structField sym e idx) ctx'
      ctx'_flat <- flattenStructs sym fields
      return $ ctx_flat Ctx.<++> ctx'_flat
    WT.BaseBVRepr _ -> return $ ctx_flat Ctx.:> e
    WT.BaseIntegerRepr -> return $ ctx_flat Ctx.:> e
    WT.BaseBoolRepr -> do
      bv <- WI.predToBV sym e (PN.knownNat @1)
      return $ ctx_flat Ctx.:> bv
    tp -> fail ("flattenStructs: unsupported type:" ++ show tp)
flattenStructs _sym Ctx.Empty = return Ctx.empty

mkClassify
  :: forall sym tp1
   . (LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> WI.SymExpr sym tp1
  -> UndefPtrClassify sym
mkClassify tag e1 = UndefPtrClassify $ \e2 -> case PC.testEquality e1 e2 of
  Just PC.Refl -> return $ Set.singleton tag
  _ -> return mempty

polySymbol :: UndefPtrOpTag -> PN.NatRepr w -> WS.SolverSymbol
polySymbol tag w = WS.safeSymbol $ (show tag) ++ "_" ++ (show w)


mkBinUF
  ::(LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> PolyFunMaker sym (Ctx.EmptyCtx Ctx.::> BasePtrType AnyNat Ctx.::> BasePtrType AnyNat) (BasePtrType AnyNat)
mkBinUF tag  = PolyFunMaker $ \sym w -> do
  let ptrRepr = WT.BaseStructRepr (Ctx.Empty Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w)
      repr = Ctx.Empty Ctx.:> ptrRepr Ctx.:> ptrRepr
  c <- WI.freshConstant sym (polySymbol tag w) (WT.BaseArrayRepr (flattenStructRepr repr) ptrRepr)
  return $ PolyFun (mkClassify tag c) $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

mkPredUF
  :: forall sym
   . (LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> PolyFunMaker sym (Ctx.EmptyCtx Ctx.::> BasePtrType AnyNat Ctx.::> BasePtrType AnyNat) WT.BaseBoolType
mkPredUF tag = PolyFunMaker $ \sym w -> do
  let repr = Ctx.Empty Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w
  c <- WI.freshConstant sym (polySymbol tag w) (WT.BaseArrayRepr (flattenStructRepr repr) WT.BaseBoolRepr)
  return $ PolyFun (mkClassify tag c) $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

mkOffUF
  :: forall sym
   . (LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> PolyFunMaker sym (Ctx.EmptyCtx Ctx.::> BasePtrType AnyNat) (WT.BaseBVType AnyNat)
mkOffUF tag = PolyFunMaker $ \sym w -> do
  let ptrRepr = WT.BaseStructRepr (Ctx.Empty Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w)
      repr = Ctx.Empty Ctx.:> ptrRepr
  c <- WI.freshConstant sym (polySymbol tag w) (WT.BaseArrayRepr (flattenStructRepr repr) (WT.BaseBVRepr w))
  return $ PolyFun (mkClassify tag c) $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

cachedPolyFun
  :: forall sym f g
   . sym
  -> PolyFunMaker sym f g
  -> IO (PolyFunMaker sym f g, UndefPtrClassify sym)
cachedPolyFun _sym (PolyFunMaker f) = do
  ref <- IORef.newIORef (MapF.empty :: MapF.MapF PN.NatRepr (PolyFun sym f g))
  let
    mker' = PolyFunMaker $ \sym' nr -> do
      m <- IORef.readIORef ref
      case MapF.lookup nr m of
        Just a -> return a
        Nothing -> do
          result <- f sym' nr
          let m' = MapF.insert nr result m
          IORef.writeIORef ref m'
          return result
    classify = UndefPtrClassify $ \e -> do
      m <- IORef.readIORef ref
      let classifier = mconcat (map (\(Some pf) -> polyFunClassify pf) (MapF.elems m))
      classifyExpr classifier e
  return (mker', classify)

mkBinOp
  :: forall sym
   . (LCB.IsSymInterface sym)
  => sym
  -> UndefPtrOpTag
  -> IO (UndefinedPtrBinOp sym, UndefPtrClassify sym)
mkBinOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkBinUF tag
  let binop =
        UndefinedPtrBinOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          sptrResult <- applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr1 Ctx.:> sptr2)
          fromSymPtr sym' sptrResult
  return (binop, classifier)

mkPredOp
  :: (LCB.IsSymInterface sym)
  => sym
  -> UndefPtrOpTag
  -> IO (UndefinedPtrPredOp sym, UndefPtrClassify sym)
mkPredOp sym tag = do
  (PolyFunMaker fn', classifier) <- cachedPolyFun sym $ mkPredUF tag
  let binop =
        UndefinedPtrPredOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr1 Ctx.:> sptr2)
  return (binop, classifier)

mkUndefinedPtrOps
  :: forall sym
   . (LCB.IsSymInterface sym)
  => sym
  -> IO (UndefinedPtrOps sym)
mkUndefinedPtrOps sym = do
  (PolyFunMaker offFn, classOff) <- cachedPolyFun sym $ mkOffUF UndefPtrOff
  let offPtrFn :: forall w. sym -> LCLM.LLVMPtr sym w -> IO (WI.SymBV sym w)
      offPtrFn sym'  ptr = withPtrWidth ptr $ \w -> do
        sptr <- asSymPtr sym' ptr
        resultfn <- offFn sym' w
        applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr)

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
