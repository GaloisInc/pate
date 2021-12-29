{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module Pate.Memory.Trace.ValidityPolicy.None (
  noValidityChecks
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS

import           Pate.Memory.Trace.ValidityPolicy ( ValidityPolicy(..) )
import qualified Pate.Panic as PP

ptrWidth :: (LCB.IsSymInterface sym) => LCLM.LLVMPtr sym w -> PN.NatRepr w
ptrWidth (LCLM.LLVMPointer _ off) =
  case WI.exprType off of
    WT.BaseBVRepr w -> w

-- | A set of validity checks that do no additional checking
noValidityChecks :: (LCB.IsSymInterface sym) => ValidityPolicy sym arch
noValidityChecks =
  ValidityPolicy { validateExpression = \_sym expr ->
                     case expr of
                       DMS.PtrToBits _w (LCS.RV (LCLM.LLVMPointer _base offset)) -> return offset
                       _ -> PP.panic PP.MemoryModel "noValidityChecks" ["Unsupported expression type"]
                 , validateStatement = \sym stmt ->
                     case stmt of
                       DMS.PtrMux _w (LCS.regValue -> cond) (LCS.regValue -> x) (LCS.regValue -> y) ->
                         LCLM.muxLLVMPtr sym cond x y
                       DMS.PtrEq _w (LCS.regValue -> p1) (LCS.regValue -> p2) ->
                         LCLM.ptrEq sym (ptrWidth p1) p1 p2
                       DMS.PtrLeq _w (LCS.regValue -> LCLM.LLVMPointer _xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer _yRegion yOffset) ->
                         WI.bvUle sym xOffset yOffset
                       DMS.PtrLt _w (LCS.regValue -> LCLM.LLVMPointer _xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer _yRegion yOffset) ->
                         WI.bvUlt sym xOffset yOffset
                       DMS.PtrAdd _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
                         isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         region <- WI.natIte sym isXRegionZero yRegion xRegion
                         offset <- WI.bvAdd sym xOffset yOffset
                         return (LCLM.LLVMPointer region offset)
                       DMS.PtrSub _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
                         isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         region <- WI.natIte sym isXRegionZero yRegion xRegion
                         offset <- WI.bvSub sym xOffset yOffset
                         return (LCLM.LLVMPointer region offset)
                       DMS.PtrAnd _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
                         isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         region <- WI.natIte sym isXRegionZero yRegion xRegion
                         offset <- WI.bvAndBits sym xOffset yOffset
                         return (LCLM.LLVMPointer region offset)
                       DMS.PtrXor _w (LCS.regValue -> LCLM.LLVMPointer xRegion xOffset) (LCS.regValue -> LCLM.LLVMPointer yRegion yOffset) -> do
                         isXRegionZero <- WI.natEq sym xRegion =<< WI.natLit sym 0
                         region <- WI.natIte sym isXRegionZero yRegion xRegion
                         offset <- WI.bvXorBits sym xOffset yOffset
                         return (LCLM.LLVMPointer region offset)
                       DMS.PtrTrunc w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
                         offset' <- WI.bvTrunc sym w offset
                         return (LCLM.LLVMPointer region offset')
                       DMS.PtrUExt w (LCS.regValue -> LCLM.LLVMPointer region offset) -> do
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
