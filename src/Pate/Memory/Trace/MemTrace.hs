{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This module defines the core data structures for the trace memory model
-- used by the core compositional verifier
--
-- The intent is that the data types defined in this module can remain opaque
module Pate.Memory.Trace.MemTrace (
    TraceMemoryModel
  , newMemTrace
  , memTraceIntrinsicTypes
  , writeMemory
  ) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.SymbolRepr as PS
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( KnownNat, type (<=), type (*), type (-) )
import qualified Unsafe.Coerce as UC
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.Intrinsics as LCSI
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified Lang.Crucible.Types as LCT

import qualified Pate.Panic as PP

-- | The conditions under which a write occurs
data Condition sym = Unconditional
                   | Conditional (WI.Pred sym)

-- | The logical predicate corresponding to the condition
conditionPred
  :: (LCB.IsSymInterface sym)
  => sym
  -> Condition sym
  -> WI.Pred sym
conditionPred sym c =
  case c of
    Unconditional -> WI.truePred sym
    Conditional p -> p

-- | The set of information characterizing a memory write operation
data MemoryWrite sym ptrW numBytes =
  MemoryWrite { storeAddress :: LCLM.LLVMPtr sym ptrW
              -- ^ The address written to
              , storeCondition :: Condition sym
              -- ^ The conditions under which the write applies
              , numBytesRepr :: PN.NatRepr numBytes
              -- ^ A type repr for the number of bytes written
              , storeValue :: LCLM.LLVMPtr sym (8 * numBytes)
              -- ^ The value stored
              , storeEndianness :: DMM.Endianness
              -- ^ The endianness of the operation
              }

data MemoryOperation sym ptrW where
  MemoryWriteOperation :: (1 <= ptrW) => MemoryWrite sym ptrW bytes -> MemoryOperation sym ptrW

-- | The core data structure of the memory model
--
-- This is a symbolic structure that is a run-time value (of type 'MemTrace') in
-- the Crucible type system.  There is a single value of this type that is
-- stored in a global variable, very similar to the LLVM memory model
data MemoryTraceImpl sym ptrW =
  MemoryTraceImpl { memTraceOperations :: LCSS.SymSequence sym (MemoryOperation sym ptrW)
               -- ^ The (symbolic) trace of operations that were performed on
               -- this memory model instance.  Note that this is a symbolic
               -- sequence, and thus can contain symbolic branches
               , memTraceBytes :: WI.SymArray sym (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW) (WT.BaseBVType 8)
               -- ^ The symbolic array that contains the bytes of each LLVMPointer in memory
               }

-- | The intrinsic type in the Crucible type system
type MemoryTrace arch = LCT.IntrinsicType "memory_trace" (Ctx.EmptyCtx Ctx.::> LCT.BVType (DMC.ArchAddrWidth arch))

data TraceMemoryModel

instance DMS.IsMemoryModel TraceMemoryModel where
  type MemModelType TraceMemoryModel arch = MemoryTrace arch
  type MemModelConstraint TraceMemoryModel sym = ()

instance (WI.IsSymExprBuilder sym) => LCSI.IntrinsicClass sym "memory_trace" where
  type Intrinsic sym "memory_trace" (Ctx.EmptyCtx Ctx.::> LCT.BVType ptrW) = MemoryTraceImpl sym ptrW
  muxIntrinsic sym _ _ (Ctx.Empty Ctx.:> LCT.BVRepr _) p t f = do
    ops <- LCSS.muxSymSequence sym p (memTraceOperations t) (memTraceOperations f)
    arr <- WI.baseTypeIte sym p (memTraceBytes t) (memTraceBytes f)
    return MemoryTraceImpl { memTraceOperations = ops
                           , memTraceBytes = arr
                           }
  muxIntrinsic _ _ _ _ _ _ _ = PP.panic PP.MemoryModel "muxIntrinsic" ["Unexpected operands in memory_trace mux"]

newMemTrace
  :: (1 <= ptrW, KnownNat ptrW, LCB.IsSymInterface sym)
  => sym
  -> IO (MemoryTraceImpl sym ptrW)
newMemTrace sym = do
  opTrace <- LCSS.nilSymSequence sym
  byteArr <- WI.freshConstant sym (WS.safeSymbol "memory_trace_bytes") PC.knownRepr
  return MemoryTraceImpl { memTraceOperations = opTrace
                         , memTraceBytes = byteArr
                         }

memTraceIntrinsicTypes :: LCB.IsSymInterface sym => LCSI.IntrinsicTypes sym
memTraceIntrinsicTypes =
  MapF.fromList [ MapF.Pair (PS.knownSymbol @"memory_trace") LCSI.IntrinsicMuxFn
                , MapF.Pair (PS.knownSymbol @"LLVM_pointer") LCSI.IntrinsicMuxFn
                ]

-- Additional proof combinators

mulMono :: forall p q x w. (1 <= x, 1 <= w) => p x -> q w -> PN.LeqProof 1 (x*w)
mulMono _x w = UC.unsafeCoerce (PN.leqRefl w)

zeroSubEq :: forall p q w n. 0 ~ (w - n) => p w -> q n -> w PC.:~: n
zeroSubEq _w _n = UC.unsafeCoerce PC.Refl

-- | Annotate nat proofs with the associated inequality that
-- is being proven to provide documentation about
-- each proof step.
proveLeq :: forall c n m. c ~ (n <= m) => PN.LeqProof n m -> PN.LeqProof n m
proveLeq prf@PN.LeqProof = prf

oneSubEq :: forall p w. 1 <= w => 1 <= (w - 1) => p w -> PN.LeqProof 2 w
oneSubEq w = UC.unsafeCoerce (PN.leqRefl w)

-- Operations

ptrWidth :: (LCB.IsSymInterface sym) => LCLM.LLVMPtr sym w -> PN.NatRepr w
ptrWidth (LCLM.LLVMPointer _blk bv) = WI.bvWidth bv

-- | Compute a new array index as an offset from a base pointer
--
-- The index is suitable for indexing into the array(s) of the trace memory
-- implementation
arrayIdxFrom
  :: (1 <= ptrW, LCB.IsSymInterface sym)
  => sym
  -> LCLM.LLVMPtr sym ptrW
  -- ^ The base pointer we are calculating the index from
  -> Integer
  -- ^ The offset from the base pointer (in the same region)
  -> IO (Ctx.Assignment (WI.SymExpr sym) (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW))
arrayIdxFrom sym ptr@(LCLM.LLVMPointer baseBlock baseOff) off = do
  let w = ptrWidth ptr
  offBV <- WI.bvLit sym w (BVS.mkBV w off)
  bvIdx <- WI.bvAdd sym baseOff offBV
  blockID <- WI.natToInteger sym baseBlock
  return (Ctx.Empty Ctx.:> blockID Ctx.:> bvIdx)

-- | Split a bitvector by taking the byte off of the front or the end (according
-- to endianness) and return it along with the remaining bitvector
chunkBV
  :: forall sym w
   . (1 <= w, 2 <= w, LCB.IsSymInterface sym)
  => sym
  -> DMM.Endianness
  -> PN.NatRepr w
  -> WI.SymBV sym (8 * w)
  -> IO (WI.SymBV sym 8, WI.SymBV sym (8 * (w-1)))
chunkBV sym endianness w bv
  | PN.LeqProof <- proveLeq @(1 <= (w-1)) $ PN.leqSub2 (PN.leqProof (PN.knownNat @2) w) (PN.leqRefl (PN.knownNat @1))
  , sz' <- PN.natMultiply (PN.knownNat @8) (PN.decNat w)
  , PN.LeqProof <- proveLeq @(1 <= (8 * (w-1))) $ mulMono (PN.knownNat @8) (PN.decNat w)
  , _1_le_w <- PN.leqProof (PN.knownNat @1) w
  , _8_le_8 <- PN.leqRefl (PN.knownNat @8)
  , PN.LeqProof  <- proveLeq @(8 <= (w * 8)) $ PN.leqMulCongr _1_le_w _8_le_8
  , PC.Refl <- PN.mulComm (PN.knownNat @8) w
  , PC.Refl <- PN.mulComm (PN.knownNat @8) (PN.decNat w)
  , PC.Refl <- PN.lemmaMul (PN.knownNat @8) w
  , PC.Refl <- PN.plusComm (PN.knownNat @8) sz' = do
    case endianness of
      -- take from the least significant bits
      DMM.LittleEndian -> do
        hd <- WI.bvSelect sym (PN.knownNat @0) (PN.knownNat @8) bv
        tl <- WI.bvSelect sym (PN.knownNat @8) sz' bv
        return (hd, tl)
      -- take from the most significant bits
      DMM.BigEndian
        | _w_1_le_w <- PN.leqSub (PN.leqRefl w) _1_le_w
        , PN.LeqProof <- proveLeq @(8 * (w-1) <= (8 * w)) $ PN.leqMulCongr _w_1_le_w _8_le_8  -> do
        hd <- WI.bvSelect sym sz' (PN.knownNat @8) bv
        tl <- WI.bvSelect sym (PN.knownNat @0) sz' bv
        return (hd, tl)

-- | Break up a bitvector into individual bytes and write each one into memory,
-- returning an updated SMT array
--
-- See Note [Write Strategy] for details on how bitvectors are decomposed
--
-- FIXME: Note that @valBlock@ is not used right now. This is the next critical
-- feature: storing block IDs with pointers when they are written. As they are
-- currently not stored, the memory model is unsound, as the read operation
-- can't restore it.
writeBV
  :: forall sym ptrW bytes
   . ( LCB.IsSymInterface sym
     , 1 <= bytes
     , 1 <= ptrW
     )
  => sym
  -> LCLM.LLVMPtr sym ptrW
  -> DMM.Endianness
  -> LCLM.LLVMPtr sym (8 * bytes)
  -> PN.NatRepr bytes
  -> WI.SymArray sym (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW) (WT.BaseBVType 8)
  -> IO (WI.SymArray sym (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW) (WT.BaseBVType 8))
writeBV sym dstPtr endianness (LCLM.LLVMPointer valBlock valOff0) = go 0 valOff0
  where
    -- Number of bytes remaining, the bitvector to write, and the array to update
    go :: forall w
        . (1 <= w)
       => Integer
       -> WI.SymBV sym (8 * w)
       -> PN.NatRepr w
       -> WI.SymArray sym (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW) (WT.BaseBVType 8)
       -> IO (WI.SymArray sym (Ctx.EmptyCtx Ctx.::> WT.BaseIntegerType Ctx.::> WT.BaseBVType ptrW) (WT.BaseBVType 8))
    go byteIdx bitvec numBytes byteArr =
      case PN.isZeroOrGT1 (PN.decNat numBytes) of
        Left PC.Refl -> do
          -- In this case, numBytes is 1 (we decremented before the comparison),
          -- so we have just a single byte left and cannot split the bitvector
          -- any more. Just write it to the appropriate index (since we have a
          -- proof it is a bv8)
          PC.Refl <- return $ zeroSubEq numBytes (PN.knownNat @1)
          idx <- arrayIdxFrom sym dstPtr byteIdx
          WI.arrayUpdate sym byteArr idx bitvec
        Right PN.LeqProof -> do
          -- Otherwise, we have at least two bytes. Split the bitvector into one
          -- byte and the rest, write the singular byte, recurse
          PN.LeqProof <- return $ oneSubEq numBytes
          (thisByte, restBytes) <- chunkBV sym endianness numBytes bitvec
          idx <- arrayIdxFrom sym dstPtr byteIdx
          byteArr' <- WI.arrayUpdate sym byteArr idx thisByte
          go (byteIdx + 1) restBytes (PN.decNat numBytes) byteArr'


-- | Write a value to memory
writeMemory
  :: ( LCB.IsSymInterface sym
     , HasCallStack
     , 1 <= ptrW
     )
  => sym
  -> Condition sym
  -- ^ The condition under which the write occurs
  -> LCLM.LLVMPtr sym ptrW
  -- ^ The pointer written to
  -> DMC.MemRepr ty
  -- ^ The memory representation of the written value
  -> LCS.RegValue sym (DMS.ToCrucibleType ty)
  -- ^ The value to be written
  -> MemoryTraceImpl sym ptrW
  -- ^ The memory model value to update
  -> IO (MemoryTraceImpl sym ptrW)
writeMemory sym cond dstPtr memRepr value memTrace0 =
  case memRepr of
    DMC.BVMemRepr byteWidth endianness -> do
      let writeOp = MemoryWrite { storeAddress = dstPtr
                                , storeCondition = cond
                                , numBytesRepr = byteWidth
                                , storeValue = value
                                , storeEndianness = endianness
                                }
      let memOp = MemoryWriteOperation writeOp
      ops <- LCSS.consSymSequence sym memOp (memTraceOperations memTrace0)

      let origBytes = memTraceBytes memTrace0
      bytes' <- writeBV sym dstPtr endianness value byteWidth origBytes
      bytes'' <- WI.baseTypeIte sym (conditionPred sym cond) bytes' origBytes
      return MemoryTraceImpl { memTraceOperations = ops
                             , memTraceBytes = bytes''
                             }
    DMC.FloatMemRepr {} ->
      PP.panic PP.MemoryModel "writeMemory" ["Writing floating point values is not currently supported"]
    DMC.PackedVecMemRepr {} ->
      PP.panic PP.MemoryModel "writeMemory" ["Writing packed vector values is not currently supported"]

{- Note [Write Strategy]

This writeup describes how 'writeBV' is intended to work in conjunction with
'chunkBV', as it is not obvious.  At a high level, these functions work together
to take a multi-byte bitvector and write it into an SMT array byte-by-byte in
the correct order.

For the sake of the writeup, assume a little endian input for the sake of
discussion (endianness is taken care of in 'chunkBV', which either takes bytes
from the beginning or end).

             ---------------------
Value        | b3 | b2 | b1 | b0 |
             ---------------------

In memory, the least-significant bit is bit 0 (in byte 0, above).  Because this
is little endian, the input word has its least significant bits in b0 in the
array, below.

             ---------------------
SMT Array    | b0 | b1 | b2 | b3 |
             ---------------------
             ^
             |
             -- Base Pointer (write destination)

The arguments to 'writeBV' in this case, which writes a 4 byte value to memory, are:

- basePtr: The Base Pointer in the diagram
- value: The multi-byte Value above

> writeBV sym basePtr LittleEndian value (knownNat @4) byteArr

This immediately calls down to the loop function:

> go value (knownNat @4) byteArr

Since this bitvector is 4 bytes, we are in the second case of the recursive
worker where we split the word into chunks using 'chunkBV'.  Because it this
example is little endian, 'chunkBV' returns

  (bit 0 - bit 8, bit 8 - bit sz)

which corresponds to

  (b0, rest)

in the Value diagram at the top.  The recursive worker then needs to write that
byte *at the base pointer* (i.e., at offset 0).  Note that this structure
requires us to track the byte offset separately from the width.

The recursion continues in the obvious way until it bottoms out with a single
byte left, which is just written in the last designated array slot.

-}
