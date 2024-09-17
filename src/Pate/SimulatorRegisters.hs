{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pate.SimulatorRegisters (
  CrucBaseTypes,
  MacawRegEntry(..),
  MacawRegVar(..),
  macawRegEntry,
  macawRegBVWidth, 
  ptrToEntry,
  bvToEntry
  ) where

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI

import qualified Pate.ExprMappable as PEM
import qualified Pate.Pointer as Ptr
import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON

-- | Type family that indicates the 'WI.BaseType' of the sub-expressions of a given 'CT.CrucibleType'.
-- Requires defining a bijection between the two types.
--
-- Note that we use an empty Struct type in the ARM semantics to denote some
-- sentinel values.  This mapping is complicated because the Crucible struct
-- type and the what4 struct type are not actually related.
type family CrucBaseTypes (tp :: CT.CrucibleType) :: Ctx.Ctx WI.BaseType where
  CrucBaseTypes (CLM.LLVMPointerType w) = (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType w)
  CrucBaseTypes CT.BoolType = (Ctx.EmptyCtx Ctx.::> WT.BaseBoolType)
  CrucBaseTypes (CT.StructType Ctx.EmptyCtx) = Ctx.EmptyCtx

-- | This is an analog of the Crucible 'CS.RegEntry' type in terms of the macaw
-- type system
data MacawRegEntry sym (tp :: MT.Type) where
  MacawRegEntry ::
    { macawRegRepr :: CT.TypeRepr (MS.ToCrucibleType tp)
    , macawRegValue :: CS.RegValue sym (MS.ToCrucibleType tp)
    } ->
    MacawRegEntry sym tp


macawRegBVWidth ::  MacawRegEntry sym (MT.BVType ptrW) -> WI.NatRepr ptrW
macawRegBVWidth (MacawRegEntry repr _) = case repr of
  CLM.LLVMPointerRepr ptrW -> ptrW
  _ -> error $ "macawRegBVWidth: unexpected type:" ++ show repr


instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MacawRegEntry sym tp) where
  w4Serialize (MacawRegEntry r v) = case r of
    CLM.LLVMPointerRepr{} -> W4S.w4Serialize (Ptr.fromLLVMPointer v)
    CT.BoolRepr -> W4S.w4SerializeF v
    CT.StructRepr Ctx.Empty -> return $ JSON.String "()"
    tp -> return $ JSON.object [ "error" JSON..= ("MacawRegEntry: unexpected type" :: String), "type" JSON..= (show tp) ]

instance W4S.SerializableExprs sym => W4S.W4SerializableF sym (MacawRegEntry sym)

ptrEquality ::
  PC.TestEquality (WI.SymExpr sym) =>
  CLM.LLVMPtr sym w1 ->
  CLM.LLVMPtr sym w2 ->
  Maybe (w1 PC.:~: w2)
ptrEquality (CLM.LLVMPointer reg1 off1) (CLM.LLVMPointer reg2 off2)
  | reg1 == reg2, Just PC.Refl <- PC.testEquality off1 off2 = Just PC.Refl
ptrEquality _ _ = Nothing

instance WI.IsSymExprBuilder sym => Eq (MacawRegEntry sym tp) where
  (MacawRegEntry repr v1) == (MacawRegEntry _ v2) = case repr of
    CLM.LLVMPointerRepr{} | Just PC.Refl <- ptrEquality v1 v2 -> True
    CLM.LLVMPointerRepr{} | Nothing <- ptrEquality v1 v2 -> False
    CT.BoolRepr | Just PC.Refl <- WI.testEquality v1 v2 -> True
    CT.BoolRepr | Nothing <- WI.testEquality v1 v2 -> False
    CT.StructRepr Ctx.Empty -> True
    _ -> error "MacawRegEntry: unexpected type for equality comparison"

data MacawRegVar sym (tp :: MT.Type) where
  MacawRegVar ::
    { macawVarEntry :: MacawRegEntry sym tp
    , macawVarBVs :: Ctx.Assignment (WI.SymExpr sym) (CrucBaseTypes (MS.ToCrucibleType tp))
    } -> MacawRegVar sym tp

instance (WI.IsExpr (WI.SymExpr sym)) => Show (MacawRegEntry sym tp) where
  show (MacawRegEntry repr v) = case repr of
    CLM.LLVMPointerRepr{} | CLM.LLVMPointer rg bv <- v -> show (WI.printSymNat rg) ++ "+" ++ show (WI.printSymExpr bv)
    CT.BoolRepr -> show (WI.printSymExpr v)
    CT.StructRepr Ctx.Empty -> "()"
    _ -> "macawRegEntry: unsupported"

macawRegEntry :: CS.RegEntry sym (MS.ToCrucibleType tp) -> MacawRegEntry sym tp
macawRegEntry (CS.RegEntry repr v) = MacawRegEntry repr v

ptrToEntry ::
  WI.IsExprBuilder sym =>
  CLM.LLVMPtr sym w ->
  MacawRegEntry sym (MT.BVType w)
ptrToEntry ptr@(CLM.LLVMPointer _ bv) = case WI.exprType bv of
  WI.BaseBVRepr w -> MacawRegEntry (CLM.LLVMPointerRepr w) ptr

bvToEntry ::
  WI.IsExprBuilder sym =>
  sym ->
  WI.SymBV sym w ->
  IO (MacawRegEntry sym (MT.BVType w))
bvToEntry sym bv = do
  zero <- WI.natLit sym 0
  WI.BaseBVRepr w <- return $ WI.exprType bv
  return $ MacawRegEntry (CLM.LLVMPointerRepr w) (CLM.LLVMPointer zero bv)


instance PEM.ExprMappable sym (MacawRegEntry sym tp) where
  mapExpr sym f entry = do
    case macawRegRepr entry of
      CLM.LLVMPointerRepr{} -> do
        val' <- WEH.mapExprPtr sym f $ macawRegValue entry
        return $ entry { macawRegValue = val' }
      CT.BoolRepr -> do
        val' <- f (macawRegValue entry)
        return $ entry { macawRegValue = val' }
      CT.StructRepr Ctx.Empty -> do
        -- In this case, we have a Unit value and there is no transformation
        -- possible (an it isn't even a base type)
        return entry
      rep -> error ("mapExpr: unsupported macaw type " ++ show rep)

instance PEM.ExprFoldable sym (MacawRegEntry sym tp) where
  foldExpr _sym f entry b = do
    case macawRegRepr entry of
      CLM.LLVMPointerRepr{} -> do
        let CLM.LLVMPointer reg off = macawRegValue entry
        f (WI.natToIntegerPure reg) b >>= f off
      CT.BoolRepr -> f (macawRegValue entry) b
      CT.StructRepr Ctx.Empty -> return b
      rep -> error ("foldExpr: unsupported macaw type " ++ show rep)

instance forall sym. PEM.ExprFoldableF sym (MacawRegEntry sym)