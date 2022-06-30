 {-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
-- | These operations support representing undefined values in the memory model
--
-- The trace memory model is intended to support verifying the equivalence of
-- programs, even when they contain undefined operations.  In cases where we
-- cannot resolve an operation because its semantics are undefined, we use these
-- operations to explicitly represent the undefined-ness so that we can prove
-- equi-undefined behavior.
module Pate.Memory.Trace.Undefined (
    UndefinedPtrOps
  , UndefPtrOpTag(..)
  , mkUndefinedPtrOps
  , inlineUndefinedValidityChecks
  , undefinedPointerOperations
  ) where

import qualified Data.IORef as IORef
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Set as Set
import           GHC.TypeLits ( Nat, type (<=) )
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS

import qualified Pate.Memory.Trace.ValidityPolicy as PMTV
import qualified Pate.Panic as PP
import qualified What4.ExprHelpers as WEH

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

-- | This is a newtype wrapper around 'UndefPtrOpTag' that has a phantom type
-- parameter to enable them to be stored in a 'MapF.MapF'
--
-- Making a newtype with a fixed kind on the type parameter helps avoid a number
-- of annoying errors that can arise with 'Const' due to it being too poly-kinded.
newtype TypedUndefTag (tp :: WT.BaseType) = TypedUndefTag UndefPtrOpTag

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
    , undefPtrTerms :: IORef.IORef (MapF.MapF (WI.SymAnnotation sym) TypedUndefTag)
    -- ^ Maintains the mapping from what4 term annotations to undefined pointer
    -- operation tags; as undefined pointer operation terms are created, they
    -- are annotated and the annotations are persisted in this map.
    --
    -- The idea is that this can then be used in conjunction with
    -- 'undefinedPointerOperations' to find all of the undefined behavior that a
    -- term depends on.
    --
    -- See Note [Undefined Pointer Identification] for details
    }

-- | Record a term annotation when we generate the term
--
-- This is /not/ meant to be exported outside of this module - it is only meant
-- to be used in the undefined pointer operations.
recordTermAnnotation
  :: (LCB.IsSymInterface sym)
  => sym
  -> IORef.IORef (MapF.MapF (WI.SymAnnotation sym) TypedUndefTag)
  -> UndefPtrOpTag
  -> WI.SymExpr sym tp
  -> IO (WI.SymExpr sym tp)
recordTermAnnotation sym mapRef tag e0 = do
  (annot, annotated) <- WI.annotateTerm sym e0
  IORef.modifyIORef' mapRef (MapF.insert annot (TypedUndefTag tag))
  return annotated

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
    { applyPolyFun :: Ctx.Assignment (WI.SymExpr sym) (NatAbsCtx args w) -> IO (WI.SymExpr sym (NatAbs ret w))
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
  return $ PolyFun $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

mkPredUF
  :: forall sym
   . (LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> PolyFunMaker sym (Ctx.EmptyCtx Ctx.::> BasePtrType AnyNat Ctx.::> BasePtrType AnyNat) WT.BaseBoolType
mkPredUF tag = PolyFunMaker $ \sym w -> do
  let repr = Ctx.Empty Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w
  c <- WI.freshConstant sym (polySymbol tag w) (WT.BaseArrayRepr (flattenStructRepr repr) WT.BaseBoolRepr)
  return $ PolyFun $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

mkOffUF
  :: forall sym
   . (LCB.IsSymInterface sym)
  => UndefPtrOpTag
  -> PolyFunMaker sym (Ctx.EmptyCtx Ctx.::> BasePtrType AnyNat) (WT.BaseBVType AnyNat)
mkOffUF tag = PolyFunMaker $ \sym w -> do
  let ptrRepr = WT.BaseStructRepr (Ctx.Empty Ctx.:> WT.BaseIntegerRepr Ctx.:> WT.BaseBVRepr w)
      repr = Ctx.Empty Ctx.:> ptrRepr
  c <- WI.freshConstant sym (polySymbol tag w) (WT.BaseArrayRepr (flattenStructRepr repr) (WT.BaseBVRepr w))
  return $ PolyFun $ \args -> WI.arrayLookup sym c =<< flattenStructs sym args

cachedPolyFun
  :: forall sym f g
   . sym
  -> PolyFunMaker sym f g
  -> IO (PolyFunMaker sym f g)
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
  return mker'

mkBinOp
  :: forall sym
   . (LCB.IsSymInterface sym)
  => sym
  -> IORef.IORef (MapF.MapF (WI.SymAnnotation sym) TypedUndefTag)
  -> UndefPtrOpTag
  -> IO (UndefinedPtrBinOp sym)
mkBinOp sym mapRef tag = do
  PolyFunMaker fn' <- cachedPolyFun sym $ mkBinUF tag
  let binop =
        UndefinedPtrBinOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          sptrResult <- applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr1 Ctx.:> sptr2)
          -- NOTE: We annotate the sptr here, which is a what4 struct, rather
          -- than the LLVMPointer. This is necessary because the LLVMPointer is
          -- not a base type, and thus cannot be annotated. We are therefore
          -- annotating both the region and offset of this pointer
          sptrResult' <- recordTermAnnotation sym' mapRef tag sptrResult
          fromSymPtr sym' sptrResult'
  return binop

mkPredOp
  :: (LCB.IsSymInterface sym)
  => sym
  -> IORef.IORef (MapF.MapF (WI.SymAnnotation sym) TypedUndefTag)
  -> UndefPtrOpTag
  -> IO (UndefinedPtrPredOp sym)
mkPredOp sym mapRef tag = do
  PolyFunMaker fn' <- cachedPolyFun sym $ mkPredUF tag
  let binop =
        UndefinedPtrPredOp $ \sym' ptr1 ptr2 -> withPtrWidth ptr1 $ \w -> do
          sptr1 <- asSymPtr sym' ptr1
          sptr2 <- asSymPtr sym' ptr2
          resultfn <- fn' sym' w
          res <- applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr1 Ctx.:> sptr2)
          recordTermAnnotation sym' mapRef tag res
  return binop

mkUndefinedPtrOps
  :: forall sym
   . (LCB.IsSymInterface sym)
  => sym
  -> IO (UndefinedPtrOps sym)
mkUndefinedPtrOps sym = do
  -- We allocate the annotation map early because we need to capture the
  -- reference in all of the function makers.
  --
  -- It isn't super obvious how necessary any of this polyfun machinery is, but
  -- it seems difficult to untangle. We want to perform these map updates as
  -- early as possible so that we have access to the necessary undefined
  -- behavior tags (which are not obviously accessible at call sites).
  mapRef <- IORef.newIORef MapF.empty

  PolyFunMaker offFn <- cachedPolyFun sym $ mkOffUF UndefPtrOff
  let offPtrFn :: forall w. sym -> LCLM.LLVMPtr sym w -> IO (WI.SymBV sym w)
      offPtrFn sym'  ptr = withPtrWidth ptr $ \w -> do
        sptr <- asSymPtr sym' ptr
        resultfn <- offFn sym' w
        res <- applyPolyFun resultfn (Ctx.Empty Ctx.:> sptr)
        recordTermAnnotation sym mapRef UndefPtrOff res

  undefPtrLt' <- mkPredOp sym mapRef UndefPtrLt
  undefPtrLeq' <- mkPredOp sym mapRef UndefPtrLeq
  undefPtrAdd' <- mkBinOp sym mapRef UndefPtrAdd
  undefPtrSub' <- mkBinOp sym mapRef UndefPtrSub
  undefPtrAnd' <- mkBinOp sym mapRef UndefPtrAnd
  undefPtrXor' <- mkBinOp sym mapRef UndefPtrXor

  return $
    UndefinedPtrOps
      { undefPtrOff = offPtrFn
      , undefPtrLt = undefPtrLt'
      , undefPtrLeq = undefPtrLeq'
      , undefPtrAdd = undefPtrAdd'
      , undefPtrSub = undefPtrSub'
      , undefPtrAnd = undefPtrAnd'
      , undefPtrXor = undefPtrXor'
      , undefPtrTerms = mapRef
      }

ptrWidth :: (LCB.IsSymInterface sym) => LCLM.LLVMPtr sym w -> PN.NatRepr w
ptrWidth (LCLM.LLVMPointer _ off) =
  case WI.exprType off of
    WT.BaseBVRepr w -> w

-- | A set of validity checks that insert the validity checks "inline" into
-- generated symbolic terms
--
-- Undefinedness is represented using the undefined pointer operations defined
-- in this module, and are uninterpreted functions that can be compared for
-- equi-undefinedness.
--
-- NOTE: This (and the other implementations) need to do the bitvector->pointer
-- translation for global pointers.
inlineUndefinedValidityChecks :: (LCB.IsSymInterface sym) => UndefinedPtrOps sym -> PMTV.ValidityPolicy sym arch
inlineUndefinedValidityChecks undefPtrOps =
  PMTV.ValidityPolicy { PMTV.validateExpression = \sym expr ->
                     case expr of
                       DMS.PtrToBits _w (LCS.RV ptr@(LCLM.LLVMPointer base offset)) ->
                         case WI.asNat base of
                           Just 0 -> return offset
                           _ -> do
                             cond <- WI.natEq sym base =<< WI.natLit sym 0
                             undefVal <- undefPtrOff undefPtrOps sym ptr
                             WI.bvIte sym cond offset undefVal
                       _ -> PP.panic PP.MemoryModel "noValidityChecks" ["Unsupported expression type"]
                 , PMTV.validateStatement = \sym stmt ->
                     case stmt of
                       DMS.PtrMux _w (LCS.regValue -> cond) (LCS.regValue -> x) (LCS.regValue -> y) ->
                         -- No validity checking required
                         LCLM.muxLLVMPtr sym cond x y
                       DMS.PtrEq _w (LCS.regValue -> p1) (LCS.regValue -> p2) ->
                         -- No validity checking required
                         LCLM.ptrEq sym (ptrWidth p1) p1 p2
                       DMS.PtrLeq _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- This is only formally defined if the pointers are in the same allocation
                         validIf <- WI.natEq sym xRegion yRegion
                         undefVal <- mkUndefPred (undefPtrLeq undefPtrOps) sym ptr1 ptr2
                         normalResult <- WI.bvUle sym xOffset yOffset
                         WI.itePred sym validIf normalResult undefVal
                       DMS.PtrLt _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- This is only formally defined if the pointers are in the same allocation
                         validIf <- WI.natEq sym xRegion yRegion
                         undefVal <- mkUndefPred (undefPtrLt undefPtrOps) sym ptr1 ptr2
                         normalResult <- WI.bvUlt sym xOffset yOffset
                         WI.itePred sym validIf normalResult undefVal
                       DMS.PtrAdd _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- For addition, at least one of the regions must be zero. Both may be zero
                         xZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         yZero <- WI.natEq sym yRegion =<< WI.natLit sym 0
                         oneZero <- WI.orPred sym xZero yZero
                         undefVal <- mkUndefPtr (undefPtrAdd undefPtrOps) sym ptr1 ptr2
                         region' <- WI.natIte sym xZero yRegion xRegion
                         offset' <- WI.bvAdd sym xOffset yOffset
                         let normalResult = LCLM.LLVMPointer region' offset'
                         LCLM.muxLLVMPtr sym oneZero normalResult undefVal
                       DMS.PtrSub _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- Either the regions or equal or the second is zero
                         --
                         -- ptr - ptr is safe (regions same)
                         -- ptr - bv is safe (second region 0)
                         -- bv - bv is safe (regions same)
                         regionsEqual <- WI.natEq sym xRegion yRegion
                         yZero <- WI.natEq sym yRegion =<< WI.natLit sym 0
                         validIf <- WI.orPred sym regionsEqual yZero
                         undefVal <- mkUndefPtr (undefPtrSub undefPtrOps) sym ptr1 ptr2
                         offset' <- WI.bvSub sym xOffset yOffset
                         let normalResult = LCLM.LLVMPointer xRegion offset'
                         LCLM.muxLLVMPtr sym validIf normalResult undefVal
                       DMS.PtrAnd _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- Same rules for addition: At least one region must be zero
                         xZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         yZero <- WI.natEq sym yRegion =<< WI.natLit sym 0
                         oneZero <- WI.orPred sym xZero yZero
                         undefVal <- mkUndefPtr (undefPtrAnd undefPtrOps) sym ptr1 ptr2
                         region' <- WI.natIte sym xZero yRegion xRegion
                         offset' <- WI.bvAndBits sym xOffset yOffset
                         let normalResult = LCLM.LLVMPointer region' offset'
                         LCLM.muxLLVMPtr sym oneZero normalResult undefVal
                       DMS.PtrXor _w (LCS.regValue -> ptr1@(LCLM.LLVMPointer xRegion xOffset)) (LCS.regValue -> ptr2@(LCLM.LLVMPointer yRegion yOffset)) -> do
                         -- This has the same rules as PtrAnd
                         xZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         yZero <- WI.natEq sym yRegion =<< WI.natLit sym 0
                         oneZero <- WI.orPred sym xZero yZero
                         undefVal <- mkUndefPtr (undefPtrXor undefPtrOps) sym ptr1 ptr2
                         region' <- WI.natIte sym xZero yRegion xRegion
                         offset' <- WI.bvXorBits sym xOffset yOffset
                         let normalResult = LCLM.LLVMPointer region' offset'
                         LCLM.muxLLVMPtr sym oneZero normalResult undefVal
                       DMS.PtrTrunc w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
                         -- No validity checks required
                         offset' <- WI.bvTrunc sym w offset
                         return (LCLM.LLVMPointer region offset')
                       DMS.PtrUExt w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
                         -- No validity checks required
                         offset' <- WI.bvZext sym w offset
                         return (LCLM.LLVMPointer region offset')
                       DMS.MacawGlobalPtr {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawGlobalPtr does not currently generate validity checks"]
                       DMS.MacawArchStmtExtension {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawArchStmtExtension does not currently generate validity checks"]
                       DMS.MacawReadMem {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawReadMem does not generate validity checks"]
                       DMS.MacawCondReadMem {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawCondReadMem does not generate validity checks"]
                       DMS.MacawWriteMem {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawWriteMem does not generate validity checks"]
                       DMS.MacawCondWriteMem {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["MacawCondWriteMem does not generate validity checks"]
                       DMS.MacawFreshSymbolic {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["Fresh values are not supported in the compositional verification extension"]
                       DMS.MacawLookupFunctionHandle {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["Function calls are not supported in the compositional verification extension"]
                       DMS.MacawLookupSyscallHandle {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["System calls are not supported in the compositional verification extension"]
                       DMS.MacawArchStateUpdate {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["Arch state update is not handled in the validity checker"]
                       DMS.MacawInstructionStart {} ->
                         PP.panic PP.MemoryModel "noValidityChecks" ["Instruction starts are not handled in the validity checker"]
                 }

-- | Like 'TypedUndefTag', add a fixed kind phantom type parameter to avoid kind
-- ambiguity with 'Const' (this one is just used for the cache during term traversal).
data TypedTags (tp :: WT.BaseType) where
  TypedTags :: Set.Set UndefPtrOpTag -> TypedTags tp

instance Semigroup (TypedTags tp) where
  TypedTags s1 <> TypedTags s2 = TypedTags (s1 <> s2)

getTypedTags :: TypedTags tp -> Set.Set UndefPtrOpTag
getTypedTags (TypedTags s) = s

-- | Traverse a symbolic term to find all of the undefined pointer operations it depends on
--
-- Note that this /grounds/ the term during the traversal so that it only
-- considers the branches chosen during the grounding process
--
-- The intent of this function is to annotate terms during the grounding process
-- so that users can see which ground values depend on undefined operations,
-- which might produce spurious results.
undefinedPointerOperations
  :: forall sym scope solver fs tp
   . ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope solver fs
     )
  => sym
  -> UndefinedPtrOps sym
  -> WEG.GroundEvalFn scope
  -> WI.SymExpr sym tp
  -> IO (Set.Set UndefPtrOpTag)
undefinedPointerOperations sym undefPtrOps groundEvalFn e0 = do
  cache <- WEB.newIdxCache
  -- FIXME: Evaluate whether or not this is really required. This is quite
  -- heavyweight and it isn't obvious what it is trying to accomplish.
  e1 <- WEH.resolveConcreteLookups sym resolveEq e0
  go cache e1
  where
    -- FIXME: Add timeouts
    resolveEq :: forall tp1 . WI.SymExpr sym tp1 -> WI.SymExpr sym tp1 -> IO (Maybe Bool)
    resolveEq e1 e2 = Just <$> (WEG.groundEval groundEvalFn =<< WI.isEq sym e1 e2)

    acc :: forall tp1 tp2
         . WEB.IdxCache scope TypedTags
        -> WEB.Expr scope tp1
        -> TypedTags tp2
        -> IO (TypedTags tp2)
    acc cache e (TypedTags tags) = do
      tags' <- go cache e
      return (TypedTags (tags <> tags'))

    go :: forall tp1
        . WEB.IdxCache scope TypedTags
       -> WEB.Expr scope tp1
       -> IO (Set.Set UndefPtrOpTag)
    go cache e = fmap getTypedTags $ WEB.idxCacheEval cache e $ do
      theseAnnots <- case WI.getAnnotation sym e of
        Nothing -> return (TypedTags mempty)
        Just annot -> do
          annotMap <- IORef.readIORef (undefPtrTerms undefPtrOps)
          case MapF.lookup annot annotMap of
            Nothing -> return (TypedTags mempty)
            Just (TypedUndefTag tag) -> return (TypedTags (Set.singleton tag))
      otherAnnots <- case e of
        WEB.NonceAppExpr a0 -> FC.foldrMFC (acc cache) (TypedTags mempty) (WEB.nonceExprApp a0)
        WEB.AppExpr a0 ->
          case WEB.appExprApp a0 of
            WEB.BaseIte _ _ cond eT eF -> do
              cond_tags <- go cache cond
              branch_tags <- WEG.groundEval groundEvalFn cond >>= \case
                True -> go cache eT
                False -> go cache eF
              return (TypedTags (cond_tags <> branch_tags))
            app -> FC.foldrMFC (acc cache) (TypedTags mempty) app
        _ -> return (TypedTags mempty)

      return (otherAnnots <> theseAnnots)

{- Note [Undefined Pointer Identification]

Some parts of the verifier rely on being able to identify terms that depend on
undefined pointer operations (as they should be thought of as uninterpreted
bitvector operations, rather than pointer operations) -- particularly when
grounding terms.

A previous version of this code attempted to achieve this by marking undefined
terms with fresh constants that could be looked for in recursive term traversals
(and identified with 'testEquality').  This was very complex and unnecessarily
indirect.

This version of the code annotates undefined pointer operations with the what4
annotation feature and replaces that search with a search for annotations, with
help from a map from what4 annotations to the undefined pointer operation
represented by that term.

The external interface is now just 'undefinedPointerOperations'

-}
