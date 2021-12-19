{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- | Functions to analyze LLVM memory post-states
module Pate.Verification.MemoryLog (
    MemoryWrite(..)
  , memoryOperationFootprint
  , concretizeWrites
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.State as CMS
import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.MemLog as LCLMM

import qualified Pate.Verification.DemandDiscovery as PVD

-- | An address and the number of bytes written to it
data MemoryWrite sym where
  -- | A write with a known length (which *could* be symbolic)
  --
  -- The String is the write source type
  MemoryWrite :: (1 <= w) => String -> PN.NatRepr w -> LCLM.LLVMPtr sym w -> WI.SymBV sym w  -> MemoryWrite sym
  -- | A write with a length that is entirely unknown
  UnboundedWrite :: LCLM.LLVMPtr sym w -> MemoryWrite sym

-- | Make a best-effort attempt to concretize the pointers and lengths of each
-- write operation by querying the SMT solver for models
concretizeWrites
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => sym
  -> [MemoryWrite sym]
  -> IO [MemoryWrite sym]
concretizeWrites sym = mapM concWrite
  where
    concWrite mw =
      case mw of
        UnboundedWrite (LCLM.LLVMPointer blk off) -> do
          blk' <- WI.integerToNat sym =<< PVD.resolveSingletonSymbolicValueInt sym =<< WI.natToInteger sym blk
          case WI.exprType off of
            WT.BaseBVRepr w -> do
              off' <- PVD.resolveSingletonSymbolicValue sym w off
              return (UnboundedWrite (LCLM.LLVMPointer blk' off'))
        MemoryWrite rsn w (LCLM.LLVMPointer blk off) len -> do
          blk' <- WI.integerToNat sym =<< PVD.resolveSingletonSymbolicValueInt sym =<< WI.natToInteger sym blk
          off' <- PVD.resolveSingletonSymbolicValue sym w off
          len' <- PVD.resolveSingletonSymbolicValue sym w len
          return (MemoryWrite rsn w (LCLM.LLVMPointer blk' off') len')

-- | Compute the "footprint" exhibited by a memory post state
--
-- This is the set of memory addresses written to (where each entry is paired
-- with the size of the write performed). These will be used to compare the
-- memory post-states of the original and patched binaries.
memoryOperationFootprint
  :: forall sym scope solver fs
   . ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     )
  => sym
  -> LCLM.MemImpl sym
  -> IO [MemoryWrite sym]
memoryOperationFootprint sym memImpl =
  CMS.execStateT (traverseWriteLog (memImpl ^. L.to LCLM.memImplHeap . LCLMM.memState)) []
  where
    processWrite :: LCLMM.MemWrite sym -> CMS.StateT [MemoryWrite sym] IO ()
    processWrite mw =
      case mw of
        LCLMM.WriteMerge _ ws1 ws2 -> do
          processWrites ws1
          processWrites ws2
        LCLMM.MemWrite dst src -> do
          -- Finally at the leaves, this is a write of some 'WriteSource' to a
          -- dest pointer.
          case src of
            LCLMM.MemCopy _src len ->
              case WI.exprType len of
                WT.BaseBVRepr w -> CMS.modify' (MemoryWrite "MemCopy" w dst len:)
            LCLMM.MemSet _byte len ->
              case WI.exprType len of
                WT.BaseBVRepr w -> CMS.modify' (MemoryWrite "MemSet" w dst len:)
            LCLMM.MemStore _llvmVal storageType _align ->
              case WI.exprType (snd (LCLM.llvmPointerView dst)) of
                WT.BaseBVRepr w -> do
                  len <- liftIO $ WI.bvLit sym w (BVS.mkBV w (LCLB.bytesToInteger (LCLM.storageTypeSize storageType)))
                  CMS.modify' (MemoryWrite "MemStore" w dst len:)
            LCLMM.MemArrayStore symArr (Just len) ->
              case WI.exprType len of
                WT.BaseBVRepr w ->
                  case symArr of
                    WEB.BoundVarExpr {} -> CMS.modify' (MemoryWrite "MemArrayStore[BoundVarExpr]" w dst len:)
                    WEB.NonceAppExpr nae ->
                      case WEB.nonceExprApp nae of
                        WEB.ArrayFromFn {} -> CMS.modify' (MemoryWrite "MemArrayStore[ArrayFromFn]" w dst len:)
                        WEB.MapOverArrays {} -> CMS.modify' (MemoryWrite "MemArrayStore[MapOverArrays]" w dst len:)
                        WEB.FnApp {} -> CMS.modify' (MemoryWrite "MemArrayStore[FnApp]" w dst len:)
                        _ -> CMS.modify' (MemoryWrite "MemArrayStore[OtherNonceApp]" w dst len:)
                    WEB.AppExpr appE ->
                      case WEB.appExprApp appE of
                        WEB.UpdateArray _eltRepr idxReprs _symArr idxs _newElt -> do
                          -- This is an update of a single element of the array
                          -- (and we know that elements are bytes, so it is of
                          -- size one) at the given symbolic index.
                          --
                          -- We know the region: it is the region of the dest
                          -- pointer. To turn this into a more logical pointer
                          -- with a single byte update, we can just use the base
                          -- of the pointer we have with the symbolic offset
                          case idxReprs of
                            Ctx.Empty Ctx.:> WT.BaseBVRepr _w
                              | Ctx.Empty Ctx.:> idx <- idxs -> do
                                let tag = "MemArrayStore@"
                                let dst' = LCLM.LLVMPointer (fst (LCLM.llvmPointerView dst)) idx
                                len1 <- liftIO $ WI.bvLit sym w (BVS.mkBV w 1)
                                CMS.modify' (MemoryWrite tag w dst' len1:)
                            _ -> CMS.modify' (MemoryWrite "MemArrayStore[UpdateArray/unknown]" w dst len:)
                        WEB.ArrayMap {} -> CMS.modify' (MemoryWrite "MemArrayStore[ArrayMap]" w dst len:)
                        WEB.ConstantArray {} -> CMS.modify' (MemoryWrite "MemArrayStore[ConstantArray]" w dst len:)
                        WEB.SelectArray {} -> CMS.modify' (MemoryWrite "MemArrayStore[SelectArray]" w dst len:)
                        WEB.BaseIte {} -> CMS.modify' (MemoryWrite "MemArrayStore[ite]" w dst len:)
                        _ -> CMS.modify' (MemoryWrite "MemArrayStore[unknown/app]" w dst len:)
            LCLMM.MemArrayStore _ Nothing -> CMS.modify' (UnboundedWrite dst:)
            LCLMM.MemInvalidate _ len ->
              case WI.exprType len of
                WI.BaseBVRepr w -> CMS.modify' (MemoryWrite "MemInvalidate" w dst len:)

    processChunk c =
      case c of
        LCLMM.MemWritesChunkFlat mws -> mapM_ processWrite mws
        LCLMM.MemWritesChunkIndexed mws -> mapM_ (mapM_ processWrite) mws

    processWrites (LCLMM.MemWrites chunks) = mapM_ processChunk chunks
    traverseWriteLog memState =
      case memState of
        LCLMM.EmptyMem _ _ (_allocs, writes) -> processWrites writes
        LCLMM.StackFrame _ _ _ (_allocs, writes) memState' -> do
          processWrites writes
          traverseWriteLog memState'
        LCLMM.BranchFrame _ _ (_allocs, writes) memState' -> do
          processWrites writes
          traverseWriteLog memState'
