{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-- | Modified crucible extension evaluators for the InlineCallee symbolic execution
--
-- The goal of these overrides is to concretize as much as we can eagerly to
-- improve the performance of the memory model during symbolic execution.  Many
-- code constructs lead to symbolic writes, which cause the memory model to
-- grind to a halt quickly. However, the vast majority of them are really
-- concrete (if you ask the SMT solver for a model, there will only be one).  We
-- take advantage of this by concretizing addresses during writes.
--
-- This module will also support any other optimizations we want. It could, for
-- example, add hooks over operations to reduce the number of safety checks
-- (which are not very relevant for the pate verifier).
module Pate.Verification.SimulatorHooks (
  hookedMacawExtensions
  ) where

import           Control.Lens ( (^.), (&), (%~) )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import qualified Data.Vector as V
import           GHC.Stack ( HasCallStack )
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WS

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.Intrinsics as LCSI
import qualified Lang.Crucible.Types as LCT

import qualified Pate.Panic as PP
import qualified Pate.Verification.Concretize as PVC

getMem
  :: (HasCallStack)
  => LCS.CrucibleState s sym ext rtp blocks r ctx
  -> LCS.GlobalVar (LCT.IntrinsicType nm args)
  -> IO (LCSI.Intrinsic sym nm args)
getMem st mvar =
  case LCSG.lookupGlobal mvar (st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals) of
    Just mem -> return mem
    Nothing  -> PP.panic PP.InlineCallee "getMem" ["Global heap value not initialized: " ++ show mvar]

setMem
  :: LCS.CrucibleState s sym ext rtp blocks r ctx
  -> LCS.GlobalVar (LCT.IntrinsicType nm args)
  -> LCSI.Intrinsic sym nm args
  -> LCS.CrucibleState s sym ext rtp blocks r ctx
setMem st mvar mem =
  st & LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals %~ LCSG.insertGlobal mvar mem

memReprToStorageType
  :: (HasCallStack)
  => DMC.MemRepr ty
  -> IO LCLM.StorageType
memReprToStorageType memRep =
  case memRep of
    DMC.BVMemRepr bytes _endian -> do
      return $ LCLM.bitvectorType (LCLB.Bytes (PN.intValue bytes))
    DMC.FloatMemRepr floatRep _endian -> do
      case floatRep of
        DMC.SingleFloatRepr -> return LCLM.floatType
        DMC.DoubleFloatRepr -> return LCLM.doubleType
        DMC.X86_80FloatRepr -> return LCLM.x86_fp80Type
        _ -> PP.panic PP.InlineCallee "memReprToStorageType" [ "Do not support memory accesses to " ++ show floatRep ++ " values"]
    DMC.PackedVecMemRepr n eltType -> do
      eltStorageType <- memReprToStorageType eltType
      return $ LCLM.arrayType (PN.natValue n) eltStorageType

resolveMemVal
  :: (HasCallStack)
  => DMC.MemRepr ty
  -> LCLM.StorageType
  -> LCS.RegValue sym (DMS.ToCrucibleType ty)
  -> LCLM.LLVMVal sym
resolveMemVal (DMC.BVMemRepr bytes _endian) _ (LCLM.LLVMPointer base bits) =
  case PN.leqMulPos (PN.knownNat @8) bytes of
    PN.LeqProof -> LCLM.LLVMValInt base bits
resolveMemVal (DMC.FloatMemRepr floatRep _endian) _ val =
  case floatRep of
    DMC.SingleFloatRepr -> LCLM.LLVMValFloat LCLM.SingleSize   val
    DMC.DoubleFloatRepr -> LCLM.LLVMValFloat LCLM.DoubleSize   val
    DMC.X86_80FloatRepr -> LCLM.LLVMValFloat LCLM.X86_FP80Size val
    _ -> PP.panic PP.InlineCallee "resolveMemVal" ["Do not support memory accesses to " ++ show floatRep ++ " values"]
resolveMemVal (DMC.PackedVecMemRepr n eltType) stp val =
  case LCLM.storageTypeF stp of
    LCLM.Array cnt eltStp
      | cnt == PN.natValue n, fromIntegral (V.length val) == PN.natValue n ->
        LCLM.LLVMValArray eltStp (resolveMemVal eltType eltStp <$> val)
    _ -> PP.panic PP.InlineCallee "resolveMemVal" ["Unexpected storage type for packed vec"]

memValToCrucible
  :: ( LCB.IsSymInterface sym
     )
  => DMC.MemRepr ty
  -> LCLM.LLVMVal sym
  -> Either String (LCS.RegValue sym (DMS.ToCrucibleType ty))
memValToCrucible memRep val =
  case memRep of
    -- Convert memory model value to pointer
    DMC.BVMemRepr bytes _endian ->
      do let bitw  = PN.natMultiply (PN.knownNat @8) bytes
         case val of
           LCLM.LLVMValInt base off
             | Just PC.Refl <- PC.testEquality (WI.bvWidth off) bitw ->
                 pure (LCLM.LLVMPointer base off)
           _ -> unexpectedMemVal

    DMC.FloatMemRepr floatRep _endian ->
      case val of
        LCLM.LLVMValFloat sz fltVal ->
          case (floatRep, sz) of
            (DMC.SingleFloatRepr, LCLM.SingleSize) ->
              pure fltVal
            (DMC.DoubleFloatRepr, LCLM.DoubleSize) ->
              pure fltVal
            (DMC.X86_80FloatRepr, LCLM.X86_FP80Size) ->
              pure fltVal
            _ -> unexpectedMemVal
        _ -> unexpectedMemVal

    DMC.PackedVecMemRepr _expectedLen eltMemRepr -> do
      case val of
        LCLM.LLVMValArray _ v -> do
          T.traverse (memValToCrucible eltMemRepr) v
        _ -> unexpectedMemVal
  where
    unexpectedMemVal = Left "Unexpected value read from memory"

tryGlobPtr
  :: (LCB.IsSymInterface sym)
  => sym
  -> LCS.RegValue sym LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem w
  -> LCLM.LLVMPtr sym w
  -> IO (LCLM.LLVMPtr sym w)
tryGlobPtr sym mem mapBVAddress val@(LCLM.LLVMPointer base offset)
  | Just blockId <- WI.asNat base
  , blockId /= 0 = do
      -- If we know that the blockId is concretely not zero, the pointer is
      -- already translated into an LLVM pointer and can be passed through.
      return val
  | otherwise = do
      -- If the blockId is zero, we have to translate it into a proper LLVM
      -- pointer
      --
      -- Otherwise, the blockId is symbolic and we need to create a mux that
      -- conditionally performs the translation.
      mapBVAddress sym mem base offset


concretizingWrite
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth ptrW
     , LCLM.HasLLVMAnn sym
     , ptrW ~ DMC.ArchAddrWidth arch
     , HasCallStack
     )
  => LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem ptrW
  -> sym
  -> LCS.CrucibleState (DMS.MacawSimulatorState (LCBO.OnlineBackend scope solver fs))
                       (LCBO.OnlineBackend scope solver fs)
                       (DMS.MacawExt arch)
                       rtp
                       blocks
                       r
                       ctx
  -> DMC.AddrWidthRepr ptrW
  -> DMC.MemRepr ty
  -> LCS.RegEntry sym (LCLM.LLVMPointerType ptrW)
  -> LCS.RegEntry sym (DMS.ToCrucibleType ty)
  -> IO ((), LCS.CrucibleState (DMS.MacawSimulatorState (LCBO.OnlineBackend scope solver fs))
                               (LCBO.OnlineBackend scope solver fs)
                               (DMS.MacawExt arch)
                               rtp
                               blocks
                               r
                               ctx)
concretizingWrite memVar globs sym crucState _addrWidth memRep (LCS.regValue -> ptr) (LCS.regValue -> value) = do
  mem <- getMem crucState memVar
  -- Attempt to concretize the pointer we are writing to, so that we can minimize symbolic writes
  ptr' <- tryGlobPtr sym mem globs ptr
  ptr'' <- PVC.resolveSingletonPointer sym ptr'
  ty <- memReprToStorageType memRep
  let memVal = resolveMemVal memRep ty value
  mem' <- LCLM.storeRaw sym mem ptr'' ty LCLD.noAlignment memVal
  return ((), setMem crucState memVar mem')

concretizingRead
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth ptrW
     , ptrW ~ DMC.ArchAddrWidth arch
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , HasCallStack
     )
  => LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem ptrW
  -> sym
  -> LCS.CrucibleState (DMS.MacawSimulatorState (LCBO.OnlineBackend scope solver fs))
                       (LCBO.OnlineBackend scope solver fs)
                       (DMS.MacawExt arch)
                       rtp
                       blocks
                       r
                       ctx
  -> DMC.AddrWidthRepr ptrW
  -> DMC.MemRepr ty
  -> LCS.RegEntry sym (LCLM.LLVMPointerType ptrW)
  -> IO (LCS.RegValue sym (DMS.ToCrucibleType ty))
concretizingRead memVar globs sym crucState _addrWidth memRep (LCS.regValue -> ptr) = do
  mem <- getMem crucState memVar
  -- Attempt to concretize the pointer we are reading from, avoiding a symbolic
  -- read if possible
  ptr' <- tryGlobPtr sym mem globs ptr
  ptr''@(LCLM.LLVMPointer _ off) <- PVC.resolveSingletonPointer sym ptr'
  case WI.asBV off of
    Just _ -> do
      ty <- memReprToStorageType memRep
      res <- LCLM.assertSafe sym =<< LCLM.loadRaw sym mem ptr'' ty LCLD.noAlignment
      case memValToCrucible memRep res of
        Left err -> PP.panic PP.InlineCallee "concretizingRead" [err]
        Right crucVal -> return crucVal
    Nothing -> do
      -- As an experiment, consider: what happens if we just return arbitrary
      -- symbolic values for symbolic reads? We know that the verifier will
      -- never return if we actually try one.
      case memRep of
        DMC.BVMemRepr nBytesRepr _endianness -> do
          let bitw = PN.natMultiply (PN.knownNat @8) nBytesRepr
          case PC.testEquality (WI.bvWidth off) bitw of
            Just PC.Refl -> do
              symOff <- WI.freshConstant sym (WS.safeSymbol "symbolicReadBytes") (WT.BaseBVRepr bitw)
              LCLM.llvmPointer_bv sym symOff
            _ -> PP.panic PP.InlineCallee "concretizingRead" ["Unsupported memRepr: " ++ show memRep]
        _ -> PP.panic PP.InlineCallee "concretizingRead" ["Unsupported memRepr: " ++ show memRep]

statementWrapper
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth (DMC.ArchAddrWidth arch)
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , HasCallStack
     )
  => LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -> sym
  -> LCS.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
statementWrapper mvar globs sym baseExt stmt crucState =
  case stmt of
    DMS.MacawWriteMem addrWidth memRep ptr value ->
      concretizingWrite mvar globs sym crucState addrWidth memRep ptr value
    DMS.MacawReadMem addrWidth memRep ptr ->
      (, crucState) <$> concretizingRead mvar globs sym crucState addrWidth memRep ptr
    _ -> LCS.extensionExec baseExt stmt crucState

-- | Macaw extensions for Crucible that have some optimizations required for the
-- pate verifier to scale
hookedMacawExtensions
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth (DMC.ArchAddrWidth arch)
     , ?memOpts :: LCLM.MemOptions
     )
  => sym
  -- ^ The (online) symbolic backend
  -> DMS.MacawArchEvalFn sym LCLM.Mem arch
  -- ^ A set of interpretations for architecture-specific functions
  -> LCS.GlobalVar LCLM.Mem
  -- ^ The Crucible global variable containing the current state of the memory
  -- model
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -- ^ A function that maps bitvectors to valid memory model pointers
  -> DMS.LookupFunctionHandle sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> DMS.LookupSyscallHandle sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym (DMC.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates (see 'MkGlobalPointerValidityAssertion' for details)
  -> LCS.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
hookedMacawExtensions sym f mvar globs lookupH lookupSyscall toMemPred =
  baseExtension { LCS.extensionExec = statementWrapper mvar globs sym baseExtension }
  where
    baseExtension = DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred
