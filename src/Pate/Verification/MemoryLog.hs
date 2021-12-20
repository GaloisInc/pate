{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-- | Functions to analyze LLVM memory post-states
module Pate.Verification.MemoryLog (
    MemoryWrite(..)
  , Footprint(..)
  , writtenLocations
  , memoryOperationFootprint
  , concretizeWrites
  , InvalidWritePolicy(..)
  , FilterPolicy(..)
  , filterWrites
  , WriteSummary(..)
  , SomeWriteSummary(..)
  , differingGlobalMemoryLocations
  , differingOrigHeapLocations
  , differingPatchedHeapLocations
  , pointerWidth
  , indexWriteAddresses
  , unhandledPointers
  , compareMemoryTraces
  ) where

import           Control.Applicative ( (<|>) )
import           Control.Lens ( (^.), (%=) )
import qualified Control.Lens as L
import qualified Control.Lens.TH as LTH
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.State as CMS
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.IntervalSet as DI
import qualified Data.IntervalMap.Interval as DII
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Sequence as Seq
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.MemLog as LCLMM
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial

import qualified Pate.Panic as PP
import qualified Pate.Verification.Concretize as PVC

llvmPtrWidth :: (LCB.IsSymInterface sym) => LCLM.LLVMPtr sym w -> PN.NatRepr w
llvmPtrWidth ptr =
  case WI.exprType (snd (LCLM.llvmPointerView ptr)) of
    WT.BaseBVRepr w -> w

-- | An address and the number of bytes written to it
data MemoryWrite sym where
  -- | A write with a known length (which *could* be symbolic)
  --
  -- The String is the write source type
  MemoryWrite :: (1 <= w) => String -> PN.NatRepr w -> LCLM.LLVMPtr sym w -> WI.SymBV sym w  -> MemoryWrite sym
  -- | A write with a length that is entirely unknown
  UnboundedWrite :: (1 <= w) => LCLM.LLVMPtr sym w -> MemoryWrite sym

data Footprint sym =
  Footprint { _writtenLocations :: !(Seq.Seq (MemoryWrite sym))
            -- ^ Writes that we observe
            , _freedAllocations :: !(Seq.Seq (WI.SymNat sym))
            -- ^ Allocation numbers that are freed in the scope of the calculation
            }

$(LTH.makeLenses ''Footprint)

data InvalidWritePolicy = Ignore | Keep
  deriving (Eq, Ord, Show)

data FilterPolicy sym w =
  FilterPolicy { filterWritesToRegions :: [LCLM.LLVMPtr sym w]
               -- ^ Filter out writes to any pointers into these regions
               , invalidWritePolicy :: InvalidWritePolicy
               -- ^ What to do with invalid writes (e.g., writes to implausible
               -- addresses or bitvectors that cannot be interpreted as real
               -- addresses)
               , unboundedWritePolicy :: InvalidWritePolicy
               -- ^ What to do with obviously unbounded writes
               }

-- | Return 'True' if the memory write satisfies the policy
satisfyPolicy
  :: (LCB.IsSymInterface sym)
  => FilterPolicy sym w
  -> [WI.SymNat sym]
  -> MemoryWrite sym
  -> Bool
satisfyPolicy p ignoreRegions w =
  case w of
    UnboundedWrite {} -> unboundedWritePolicy p == Keep
    MemoryWrite _rsn _w dst len ->
      and [ not (fst (LCLM.llvmPointerView dst) `elem` ignoreRegions)
          -- Max length writes show up when initializing symbolic array regions;
          -- these aren't an interesting write, and are just an implementation
          -- artifact
          , invalidWritePolicy p == Ignore && not (isMaxLength len)
          ]
  where
    isMaxLength len =
      case WI.asBV len of
        Nothing -> False
        Just lenBV ->
          case WI.exprType len of
            WT.BaseBVRepr wrep -> lenBV == BVS.maxUnsigned wrep

-- | Apply a filter policy to discard the requested writes
--
-- It also discards writes to regions that are concretely known to be freed
--
-- It is most useful to apply this after concretizing writes, as this filter
-- does not use the solver to attempt to resolve symbolic terms.
filterWrites
  :: (LCB.IsSymInterface sym)
  => FilterPolicy sym w
  -> Footprint sym
  -> Footprint sym
filterWrites policy fp =
  Footprint { _writtenLocations = Seq.fromList $ filter (satisfyPolicy policy ignoreRegions) (F.toList (fp ^. writtenLocations))
            , _freedAllocations = fp ^. freedAllocations
            }
  where
    -- Also ignore writes to freed allocations
    ignoreRegions = concat [ fmap (fst . LCLM.llvmPointerView) (filterWritesToRegions policy)
                           , F.toList (fp ^. freedAllocations)
                           ]


-- | Make a best-effort attempt to concretize the pointers and lengths of each
-- write operation by querying the SMT solver for models
concretizeWrites
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => sym
  -> Footprint sym
  -> IO (Footprint sym)
concretizeWrites sym fp = do
  locs' <- mapM concWrite (fp ^. writtenLocations)
  frees' <- mapM concFree (fp ^. freedAllocations)
  return Footprint { _writtenLocations = locs'
                   , _freedAllocations = frees'
                   }
  where
    concFree r =
      WI.integerToNat sym =<< PVC.resolveSingletonSymbolicAs PVC.concreteInteger sym =<< WI.natToInteger sym r

    concWrite mw =
      case mw of
        UnboundedWrite ptr -> do
          ptr' <- PVC.resolveSingletonPointer sym ptr
          return (UnboundedWrite ptr')
        MemoryWrite rsn w ptr len -> do
          ptr' <- PVC.resolveSingletonPointer sym ptr
          len' <- PVC.resolveSingletonSymbolicAs (PVC.concreteBV w) sym len
          return (MemoryWrite rsn w ptr' len')

emptyFootprint :: Footprint sym
emptyFootprint = Footprint { _writtenLocations = mempty
                           , _freedAllocations = mempty
                           }

addWrite
  :: (CMS.MonadState (Footprint sym) m)
  => MemoryWrite sym
  -> m ()
addWrite w = writtenLocations %= (<> Seq.singleton w)

addFree
  :: (CMS.MonadState (Footprint sym) m)
  => WI.SymNat sym
  -> m ()
addFree bid = freedAllocations %= (<> Seq.singleton bid)

-- | Compute the "footprint" exhibited by a memory post state
--
-- This is the set of memory addresses written to (where each entry is paired
-- with the size of the write performed). These will be used to compare the
-- memory post-states of the original and patched binaries.
--
-- Note that the order of writes has no particular meaning
memoryOperationFootprint
  :: forall sym scope solver fs
   . ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     )
  => sym
  -> LCLM.MemImpl sym
  -> IO (Footprint sym)
memoryOperationFootprint sym memImpl =
  CMS.execStateT (traverseWriteLog (memImpl ^. L.to LCLM.memImplHeap . LCLMM.memState)) emptyFootprint
  where
    processWrite :: LCLMM.MemWrite sym -> CMS.StateT (Footprint sym) IO ()
    processWrite mw =
      case mw of
        LCLMM.WriteMerge _ ws1 ws2 -> do
          processWrites ws1
          processWrites ws2
        LCLMM.MemWrite dst src -> do
          let w = llvmPtrWidth dst
          -- Finally at the leaves, this is a write of some 'WriteSource' to a
          -- dest pointer.
          case src of
            LCLMM.MemCopy _src len ->
              addWrite (MemoryWrite "MemCopy" w dst len)
            LCLMM.MemSet _byte len ->
              addWrite (MemoryWrite "MemSet" w dst len)
            LCLMM.MemStore _llvmVal storageType _align -> do
              len <- liftIO $ WI.bvLit sym w (BVS.mkBV w (LCLB.bytesToInteger (LCLM.storageTypeSize storageType)))
              addWrite (MemoryWrite "MemStore" w dst len)
            LCLMM.MemArrayStore symArr (Just len) ->
              case symArr of
                WEB.BoundVarExpr {} -> addWrite (MemoryWrite "MemArrayStore[BoundVarExpr]" w dst len)
                WEB.NonceAppExpr nae ->
                  case WEB.nonceExprApp nae of
                    WEB.ArrayFromFn {} -> addWrite (MemoryWrite "MemArrayStore[ArrayFromFn]" w dst len)
                    WEB.MapOverArrays {} -> addWrite (MemoryWrite "MemArrayStore[MapOverArrays]" w dst len)
                    WEB.FnApp {} -> addWrite (MemoryWrite "MemArrayStore[FnApp]" w dst len)
                    _ -> addWrite (MemoryWrite "MemArrayStore[OtherNonceApp]" w dst len)
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
                            addWrite (MemoryWrite tag w dst' len1)
                    WEB.ArrayMap {} -> addWrite (MemoryWrite "MemArrayStore[ArrayMap]" w dst len)
                    WEB.ConstantArray {} -> addWrite (MemoryWrite "MemArrayStore[ConstantArray]" w dst len)
                    WEB.SelectArray {} -> addWrite (MemoryWrite "MemArrayStore[SelectArray]" w dst len)
                    WEB.BaseIte {} -> addWrite (MemoryWrite "MemArrayStore[ite]" w dst len)
                    _ -> addWrite (MemoryWrite "MemArrayStore[unknown/app]" w dst len)
            LCLMM.MemArrayStore _ Nothing -> addWrite (UnboundedWrite dst)
            LCLMM.MemInvalidate _ len ->
              addWrite (MemoryWrite "MemInvalidate" w dst len)

    processChunk c =
      case c of
        LCLMM.MemWritesChunkFlat mws -> mapM_ processWrite mws
        LCLMM.MemWritesChunkIndexed mws -> mapM_ (mapM_ processWrite) mws

    processAlloc a =
      case a of
        LCLMM.Allocations {} -> return ()
        LCLMM.MemFree r _ -> addFree r
        LCLMM.AllocMerge _ allocs1 allocs2 -> do
          processAllocs allocs1
          processAllocs allocs2

    processWrites (LCLMM.MemWrites chunks) = mapM_ processChunk chunks
    processAllocs (LCLMM.MemAllocs allocs) = mapM_ processAlloc allocs
    traverseWriteLog memState =
      case memState of
        LCLMM.EmptyMem _ _ (allocs, writes) -> do
          processAllocs allocs
          processWrites writes
        LCLMM.StackFrame _ _ _ (allocs, writes) memState' -> do
          processAllocs allocs
          processWrites writes
          traverseWriteLog memState'
        LCLMM.BranchFrame _ _ (allocs, writes) memState' -> do
          processAllocs allocs
          processWrites writes
          traverseWriteLog memState'

-- | A wrapper around the symbolic backend that captures enough to inspect some
-- terms, but not enough to persist the online connection, which could disappear.
--
-- This is primarily here so that we can sink the 'WriteSummary' down into a
-- proof node, where referring to a symbolic backend is a bit tricky. Proofs in
-- "symbolic" mode can refer to symbolic backends in the type parameter, but
-- "grounded" proofs cannot.
--
-- By making this the proof payload, we can use the same type in both proof modes.
data SomeWriteSummary w where
  SomeWriteSummary :: (LCB.IsSymInterface sym) => sym -> WriteSummary sym w -> SomeWriteSummary w

data WriteSummary sym w =
  WriteSummary { _differingGlobalMemoryLocations :: [BVS.BV w]
               -- ^ Global memory locations that differ
               , _differingOrigHeapLocations :: [LCLM.LLVMPtr sym w]
               -- ^ Heap pointers that seem to be different
               , _differingPatchedHeapLocations :: [LCLM.LLVMPtr sym w]
               , _unhandledPointers :: [LCLM.SomePointer sym]
               -- ^ Pointers that the verifier cannot reason about effectively
               -- (e.g., fully symbolic writes)
               , _pointerWidth :: PN.NatRepr w
               }

$(LTH.makeLenses ''WriteSummary)

-- | Summarize global writes that are adjacent to one another as ranges
indexWriteAddresses
  :: PN.NatRepr w
  -> [BVS.BV w]
  -> [DII.Interval (BVS.BV w)]
indexWriteAddresses width =
  DI.elems . DI.flattenWith combine . F.foldl' addSingleton DI.empty
  where
    combine a b = DII.combine a b <|> adjacent a b
    adjacent (DII.ClosedInterval l1 h1) (DII.ClosedInterval l2 h2)
      | BVS.add width h1 (BVS.mkBV width 1) == l2 = Just (DII.ClosedInterval l1 h2)
      | otherwise = Nothing
    adjacent _ _ = Nothing
    addSingleton s i = DI.insert (DII.ClosedInterval i i) s


bvWidth
  :: (LCB.IsSymInterface sym)
  => sym
  -> WI.SymExpr sym (WT.BaseBVType w)
  -> PN.NatRepr w
bvWidth _ e =
  case WI.exprType e of
    WT.BaseBVRepr w -> w

-- | Returns 'True' if the two values read from memory are always equal
--
-- The two values have been read from memory, but are partial (or potentially
-- just straight up errors).  If either is an error, return False.  Otherwise,
-- assume the necessary predicates and compare.
proveBytesEqual
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth w
     , HasCallStack
     )
  => sym
  -> Partial.PartLLVMVal sym
  -> Partial.PartLLVMVal sym
  -> IO Bool
proveBytesEqual _ (Partial.Err _) _ = return False
proveBytesEqual _ _ (Partial.Err _) = return False
proveBytesEqual sym (Partial.NoErr p1 v1) (Partial.NoErr p2 v2) =
  case (v1, v2) of
    (LCLM.LLVMValInt _ b1, LCLM.LLVMValInt _ b2)
      | Just PC.Refl <- PC.testEquality (bvWidth sym b1) (bvWidth sym b2) -> do
          LCBO.withSolverProcess sym doPanic $ \sp -> WPO.inNewFrame sp $ do
            let conn = WPO.solverConn sp
            WPS.assume conn p1
            WPS.assume conn p2
            areEq <- WI.bvEq sym b1 b2
            goal <- WI.notPred sym areEq
            WPS.assume conn goal
            msat <- WPO.check sp "Prove byte equality"
            case msat of
              WSat.Unknown -> return False
              WSat.Sat {} -> return False
              WSat.Unsat {} -> return True
    _ -> PP.panic PP.InlineCallee "proveBytesEqual" ["Impossible value type"]
  where
    doPanic = PP.panic PP.Solver "inNewFrame" ["Online solving not enabled"]

compareWrite
  :: forall sym scope solver fs w
   . ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth w
     )
  => L.Lens' (WriteSummary sym w) [LCLM.LLVMPtr sym w]
  -> sym
  -> LCLM.MemImpl sym
  -> LCLM.MemImpl sym
  -> MemoryWrite sym
  -> CMS.StateT (WriteSummary sym w) IO ()
compareWrite whichHeap sym oMem pMem w =
  case w of
    UnboundedWrite p -> do
      -- There really isn't anything we can say about these, but they will be useful for diagnostics
      unhandledPointers %= (LCLM.SomePointer p:)
    MemoryWrite _rsn width ptr len -> do
      case WI.asBV len of
        Nothing -> return ()
        Just (BVS.asUnsigned -> lenBV)
          | Just PC.Refl <- PC.testEquality width ?ptrWidth -> do
              let ?recordLLVMAnnotation = \_ _ _ -> return ()
              let ?memOpts = LCLM.laxPointerMemOptions
              let byteRep = LCLM.bitvectorType 1
              F.forM_ [0..lenBV-1] $ \byteIdx -> do
                byteOff :: WI.SymBV sym w
                        <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (toInteger byteIdx))
                thisPtr :: LCLM.LLVMPtr sym w
                        <- liftIO $ LCLM.ptrAdd sym ?ptrWidth ptr byteOff

                oVal <- liftIO $ LCLM.loadRaw sym oMem thisPtr byteRep LCLD.noAlignment
                pVal <- liftIO $ LCLM.loadRaw sym pMem thisPtr byteRep LCLD.noAlignment

                areAlwaysEqual <- liftIO $ proveBytesEqual sym oVal pVal
                if | areAlwaysEqual -> return ()
                   | WI.asNat (fst (LCLM.llvmPointerView ptr)) == Just 1
                   , Just bvAddr <- WI.asBV (snd (LCLM.llvmPointerView thisPtr)) ->
                     differingGlobalMemoryLocations %= (bvAddr:)
                   | otherwise -> whichHeap %= (thisPtr:)
          | otherwise -> unhandledPointers %= (LCLM.SomePointer ptr:)

-- | Compare the locations written in both binaries
--
-- Try to prove that all locations written by both programs have the same value
-- for all possible executions.  For each location that does not have the same
-- value, record it in the 'WriteSummary'.
compareMemoryTraces
  :: forall sym scope solver fs w
   . ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , LCLM.HasPtrWidth w
     )
  => sym
  -> (LCLM.MemImpl sym, Footprint sym)
  -> (LCLM.MemImpl sym, Footprint sym)
  -> IO (WriteSummary sym w)
compareMemoryTraces sym (oMem, oWrites) (pMem, pWrites) =
  CMS.execStateT doAnalysis s0
  where
    s0 = WriteSummary { _differingGlobalMemoryLocations = []
                      , _differingOrigHeapLocations = []
                      , _differingPatchedHeapLocations = []
                      , _unhandledPointers = []
                      , _pointerWidth = ?ptrWidth
                      }
    doAnalysis = do
      mapM_ (compareWrite differingOrigHeapLocations sym oMem pMem) (oWrites ^. writtenLocations)
      mapM_ (compareWrite differingPatchedHeapLocations sym oMem pMem) (pWrites ^. writtenLocations)
