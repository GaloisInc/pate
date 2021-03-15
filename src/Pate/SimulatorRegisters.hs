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
{-# LANGUAGE ConstraintKinds #-}

module Pate.SimulatorRegisters (
  CrucBaseTypes,
  MacawRegVar(..),
  MacawRegEntry(..),
  macawRegEntry,
  ptrToEntry,
  ValidMacawType
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

import qualified Pate.Types as PT
import qualified Pate.ExprMappable as PEM
import qualified What4.ExprHelpers as WEH

-- | Type family that indicates the 'WI.BaseType' of the sub-expressions of a given 'CT.CrucibleType'.
-- Requires defining a bijection between the two types.
--
-- Note that we use an empty Struct type in the ARM semantics to denote some
-- sentinel values.  This mapping is complicated because the Crucible struct
-- type and the what4 struct type are not actually related.
type family CrucBaseTypes (tp :: CT.CrucibleType) :: Ctx.Ctx WI.BaseType where
  CrucBaseTypes (CLM.LLVMPointerType w) = (Ctx.EmptyCtx Ctx.::> WT.BaseNatType Ctx.::> WT.BaseBVType w)
  CrucBaseTypes CT.BoolType = (Ctx.EmptyCtx Ctx.::> WT.BaseBoolType)
  CrucBaseTypes (CT.StructType Ctx.EmptyCtx) = Ctx.EmptyCtx

type ValidMacawType tp = Eq (PT.ConcreteValue (MS.ToCrucibleType tp))

-- | This is an analog of the Crucible 'CS.RegEntry' type in terms of the macaw
-- type system
data MacawRegEntry sym (tp :: MT.Type) where
  MacawRegEntry :: ValidMacawType tp =>
    { macawRegRepr :: CT.TypeRepr (MS.ToCrucibleType tp)
    , macawRegValue :: CS.RegValue sym (MS.ToCrucibleType tp)
    } ->
    MacawRegEntry sym tp

instance WI.IsSymExprBuilder sym => Eq (MacawRegEntry sym tp) where
  (MacawRegEntry repr v1) == (MacawRegEntry _ v2) = case repr of
    CLM.LLVMPointerRepr{} | Just PC.Refl <- PT.ptrEquality v1 v2 -> True
    CT.BoolRepr | Just PC.Refl <- WI.testEquality v1 v2 -> True
    CT.StructRepr Ctx.Empty -> True
    _ -> error "MacawRegEntry: unexpected type for equality comparison"

data MacawRegVar sym (tp :: MT.Type) where
  MacawRegVar ::
    { macawVarEntry :: MacawRegEntry sym tp
    , macawVarBVs :: Ctx.Assignment (WI.SymExpr sym) (CrucBaseTypes (MS.ToCrucibleType tp))
    } ->
    MacawRegVar sym tp

instance PC.ShowF (WI.SymExpr sym) => Show (MacawRegEntry sym tp) where
  show (MacawRegEntry repr v) = case repr of
    CLM.LLVMPointerRepr{} | CLM.LLVMPointer rg bv <- v -> PC.showF rg ++ ":" ++ PC.showF bv
    _ -> "macawRegEntry: unsupported"

macawRegEntry :: ValidMacawType tp =>  Eq (CS.RegValue sym (MS.ToCrucibleType tp)) => CS.RegEntry sym (MS.ToCrucibleType tp) -> MacawRegEntry sym tp
macawRegEntry (CS.RegEntry repr v) = MacawRegEntry repr v

ptrToEntry ::
  WI.IsExprBuilder sym =>
  CLM.LLVMPtr sym w ->
  MacawRegEntry sym (MT.BVType w)
ptrToEntry ptr@(CLM.LLVMPointer _ bv) = case WI.exprType bv of
  WI.BaseBVRepr w -> MacawRegEntry (CLM.LLVMPointerRepr w) ptr

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
