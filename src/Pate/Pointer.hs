{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Provides a wrapper around llvm pointers, which are otherwise inconvenient
--   to use directly since they can't have class instances defined for them
module Pate.Pointer
  ( Pointer
  , pattern Pointer
  , pattern StackSlot
  , pattern Bitvector
  , fromLLVMPointer
  , toLLVMPointer
  , width
  , withWidth
  , asConcrete
  , traverseAsPtr
  , ptrEq
  , groundPtr
  ) where

import Data.UnwrapType
import GHC.TypeLits
import Prettyprinter hiding ( width )

import qualified Data.BitVector.Sized as BVS

import Data.Parameterized.NatRepr
import Data.Parameterized.Classes

import qualified What4.Interface as W4
import qualified What4.Concrete as W4
import qualified What4.JSON as W4S

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Data.Aeson as JSON
import Data.Aeson ((.=))
import qualified Pate.ExprMappable as PEM
import qualified What4.ExprHelpers as WEH
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified Pate.Verification.Concretize as PVC


newtype Pointer sym w = PointerC { unPtr :: (CLM.LLVMPtr sym w) }

pattern Pointer :: W4.SymNat sym -> W4.SymBV sym w -> Pointer sym w
pattern Pointer reg off = PointerC (CLM.LLVMPointer reg off)
{-# COMPLETE Pointer #-}

pattern StackSlot :: W4.IsExpr (W4.SymExpr sym) => W4.SymBV sym w -> Pointer sym w
pattern StackSlot slot <- (asStackSlot -> Just slot)

pattern Bitvector :: W4.IsExpr (W4.SymExpr sym) => W4.SymBV sym w -> Pointer sym w
pattern Bitvector bv <- (asBitvector -> Just bv)

stackRegion :: Natural
stackRegion = 1

asStackSlot :: W4.IsExpr (W4.SymExpr sym) => Pointer sym w -> Maybe (W4.SymBV sym w)
asStackSlot (Pointer reg off) | Just reg_c <- W4.asNat reg, reg_c == stackRegion = Just off
asStackSlot _ = Nothing

asBitvector :: W4.IsExpr (W4.SymExpr sym) => Pointer sym w -> Maybe (W4.SymBV sym w)
asBitvector (Pointer reg off) | Just 0 <- W4.asNat reg = Just off
asBitvector _ = Nothing

-- | Cludge to avoid rewriting everything into Pointer right away
type instance UnwrapType (Pointer sym w) = CLM.LLVMPtr sym w

toLLVMPointer :: Pointer sym w -> CLM.LLVMPtr sym w
toLLVMPointer (PointerC ptr) = ptr
{-# INLINE toLLVMPointer #-}


fromLLVMPointer :: CLM.LLVMPtr sym w -> Pointer sym w
fromLLVMPointer ptr = PointerC ptr
{-# INLINE fromLLVMPointer #-}

asConcrete :: W4.IsExpr (W4.SymExpr sym) => Pointer sym w -> Maybe (Natural, BVS.BV w)
asConcrete (Pointer reg off) = case (W4.asNat reg, W4.asConcrete off) of
  (Just reg_c, Just (W4.ConcreteBV _ off_c)) -> Just (reg_c, off_c)
  _ -> Nothing

groundPtr :: forall sym ptrW t st fs. sym ~ W4B.ExprBuilder t st fs =>
  sym ->
  W4G.GroundEvalFn t ->
  Pointer sym ptrW ->
  IO (Pointer sym ptrW)
groundPtr sym evalFn ptr = 
  PEM.mapExpr sym (\e -> W4G.groundEval evalFn e >>= \gv -> PVC.symbolicFromConcrete sym gv e) ptr

width :: W4.IsExpr (W4.SymExpr sym) => Pointer sym w -> W4.NatRepr w
width ptr = withWidth ptr id

withWidth :: W4.IsExpr (W4.SymExpr sym) => Pointer sym w -> (1 <= w => W4.NatRepr w -> a) -> a
withWidth (Pointer _ off) f | W4.BaseBVRepr w <- W4.exprType off = f w

traverseAsPtr :: Applicative t => CLM.LLVMPtr sym w1 -> (Pointer sym w1 -> t (Pointer sym w2)) -> t (CLM.LLVMPtr sym w2)
traverseAsPtr ptr f = unPtr <$> f (PointerC ptr)

-- | True iff the pointers are the same width and have the same region/offset
ptrEq :: W4.IsExprBuilder sym => sym -> Pointer sym w1 -> Pointer sym w2 -> IO (W4.Pred sym)
ptrEq sym ptr1@(Pointer reg1 off1) ptr2@(Pointer reg2 off2) =
  case testEquality (width ptr1) (width ptr2) of
    Just Refl -> do
      regsEq <- W4.natEq sym reg1 reg2
      W4.BaseBVRepr{} <- return $ W4.exprType off1
      offsEq <- W4.bvEq sym off1 off2
      W4.andPred sym regsEq offsEq
    Nothing -> return $ W4.falsePred sym

instance TestEquality (W4.SymExpr sym) => TestEquality (Pointer sym) where
  testEquality (Pointer reg1 off1) (Pointer reg2 off2) = case (reg1 == reg2, testEquality off1 off2) of
    (True, Just Refl) -> Just Refl
    _ -> Nothing

instance OrdF (W4.SymExpr sym) => OrdF (Pointer sym) where
  compareF (Pointer reg1 off1) (Pointer reg2 off2) = lexCompareF off1 off2 (fromOrdering $ compare reg1 reg2)

instance W4.IsExpr (W4.SymExpr sym) => Pretty (Pointer sym w) where
  pretty ptr = case ptr of
    Bitvector bv -> W4.printSymExpr bv
    StackSlot slot -> "Stack Slot:" <+> W4.printSymExpr slot
    Pointer reg off -> "(" <> W4.printSymNat reg <> "," <> W4.printSymExpr off <> ")"

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (Pointer sym w) where
  w4Serialize (Pointer reg off) = do
    reg_v <- W4S.w4SerializeF (W4.natToIntegerPure reg)
    off_v <- W4S.w4SerializeF off
    return $ JSON.object ["region" .= reg_v, "offset" .= off_v]

instance W4S.SerializableExprs sym => W4S.W4SerializableF sym (Pointer sym) where

instance PEM.ExprMappable sym (Pointer sym w) where
  mapExpr sym f (PointerC llvmptr) = PointerC <$> WEH.mapExprPtr sym f llvmptr

instance PEM.ExprFoldable sym (Pointer sym w) where
  foldExpr _sym f (Pointer reg1 off1) b = f (W4.natToIntegerPure reg1) b >>= f off1