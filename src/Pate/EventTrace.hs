{-|
Module           : Pate.EventTrace
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Defines data structures relating to collecting traces of events during
symbolic execution.

-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}



{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE KindSignatures #-}

module Pate.EventTrace
( MemEvent(..)
, MemOp(..)
, MemOpCondition(..)
, MemOpDirection(..)
, getCond
, RegOp(..)
, SymBV'(..)
, TraceEvent(..)
, EventTrace
, InstructionEvent(..)
, InstructionTrace
, ppPtr'
, prettyMemOp
, prettyMemEvent
, filterEvent
, groundExternalCallData
, printExternalCallData
, compareExternalCallData
, ExternalCallData(..)
, MemChunk(..)
, copyMemChunkInto
, concreteMemChunk
, muxMemChunk

) where

import           Prettyprinter
import qualified Data.BitVector.Sized as BV
import           Data.Text ( Text )
import qualified Control.Monad.IO.Class as IO
import           Data.Functor.Const ( Const(..) )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface hiding ( integerToNat )

import           Lang.Crucible.LLVM.MemModel (LLVMPtr, pattern LLVMPointer, ppPtr)
import           Lang.Crucible.Utils.MuxTree ( MuxTree, viewMuxTree )
import           Lang.Crucible.Simulator.SymSequence ( SymSequence(..), muxSymSequence, evalWithFreshCache, nilSymSequence, consSymSequence, appendSymSequence, isNilSymSequence, traverseSymSequence )

import           Data.Macaw.Memory (Endianness(..), MemSegmentOff, MemWidth, MemAddr (..), segoffAddr, memWidthNatRepr)
import           Data.Macaw.CFG.AssignRhs (ArchAddrWidth, ArchReg)
import           Data.Macaw.CFG (ArchSegmentOff, RegAddrWidth)

import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON
import           What4.JSON ((.=), (.==), (.=~))
import           What4.SymSequence

import           Data.Parameterized.SetF (AsOrd(..))
import qualified Pate.ExprMappable as PEM
import qualified Pate.SimulatorRegisters as PSr
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Pate.Pointer as Ptr
import Control.Monad (forM, foldM)
import Data.Maybe (catMaybes)
import What4.Partial (PartExpr, pattern Unassigned, pattern PE)
import qualified Data.IORef as IO
import qualified Data.Map as Map
import Data.Parameterized.Nonce
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified Pate.Verification.Concretize as PVC
import qualified What4.Expr.ArrayUpdateMap as AUM
import Data.Data (Typeable)
import GHC.TypeLits
import qualified Data.Macaw.Memory as MC
import qualified What4.Concrete as W4C
import Data.Foldable (foldlM)
import Data.Parameterized (Some(..))

-- Needed since SymBV is a type alias
newtype SymBV' sym w = SymBV' { unSymBV :: SymBV sym w }

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (SymBV' sym w) where
  w4Serialize (SymBV' bv) = W4S.w4SerializeF bv

instance W4S.SerializableExprs sym => W4S.W4SerializableF sym (SymBV' sym)

instance OrdF (SymExpr sym) => TestEquality (SymBV' sym) where
  testEquality a b = case compareF a b of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF (SymExpr sym) => OrdF (SymBV' sym) where
  compareF (SymBV' a) (SymBV' b) = case compareF a b of
    EQF -> EQF
    LTF -> LTF
    GTF -> GTF

instance OrdF (SymExpr sym) => Eq (SymBV' sym w) where
  a == b | Just{} <- testEquality a b = True
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (SymBV' sym w) where
  compare a b = toOrdering $ compareF a b

instance PEM.ExprMappable sym (SymBV' sym w) where
  mapExpr _sym f (SymBV' bv) = SymBV' <$> f bv

instance IsExpr (SymExpr sym) => Pretty (SymBV' sym w) where
  pretty (SymBV' bv) = printSymExpr bv

instance IsExpr (SymExpr sym) => Show (SymBV' sym w) where
  show (SymBV' bv) = show (printSymExpr bv)

instance IsExpr (SymExpr sym) => ShowF (SymBV' sym) where


data MemOpCondition sym
  = Unconditional
  | Conditional (Pred sym)

getCond ::
  IsExprBuilder sym =>
  sym ->
  MemOpCondition sym ->
  Pred sym
getCond sym Unconditional = truePred sym
getCond _sym (Conditional p) = p

instance TestEquality (SymExpr sym) => Eq (MemOpCondition sym) where
  Unconditional == Unconditional = True
  Conditional p == Conditional p' | Just Refl <- testEquality p p' = True
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemOpCondition sym) where
  compare Unconditional Unconditional = EQ
  compare (Conditional p) (Conditional p') = toOrdering $ compareF p p'
  compare Unconditional _ = GT
  compare _ Unconditional = LT

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MemOpCondition sym) where
  w4Serialize = \case
    Unconditional -> W4S.w4SerializeString ("unconditional" :: String)
    Conditional p -> W4S.object ["condition" .== p]

instance PEM.ExprMappable sym (MemOpCondition sym) where
  mapExpr _sym f = \case
    Conditional p -> Conditional <$> f p
    Unconditional -> return Unconditional

data MemOpDirection =
    Read
  | Write
  deriving (Eq, Ord, Show)

instance W4S.W4Serializable sym MemOpDirection where
  w4Serialize = W4S.w4SerializeString

deriving instance Show (Pred sym) => Show (MemOpCondition sym)

data MemOp sym ptrW where
  MemOp ::
    1 <= w =>
    -- The address of the operation
    LLVMPtr sym ptrW ->
    MemOpDirection ->
    MemOpCondition sym ->
    -- The size of the operation in bytes
    NatRepr w ->
    -- The value read or written during the operation
    LLVMPtr sym (8*w) ->
    Endianness ->
    MemOp sym ptrW


instance TestEquality (SymExpr sym) => Eq (MemOp sym ptrW) where
  MemOp (LLVMPointer addrR addrO) dir cond repr (LLVMPointer valR valO) end
    == MemOp (LLVMPointer addrR' addrO') dir' cond' repr' (LLVMPointer valR' valO') end'
     | Just Refl <- testEquality repr repr'
     , addrR == addrR'
     , Just Refl <- testEquality addrO addrO'
     , valR == valR'
     , Just Refl <- testEquality valO valO'
    = cond == cond' && dir == dir' && end == end'
  _ == _ = False

instance OrdF (SymExpr sym) => Ord (MemOp sym ptrW) where
  compare (MemOp (LLVMPointer reg1 off1) dir1 cond1 sz1 (LLVMPointer vr1 vo1) end1)
          (MemOp (LLVMPointer reg2 off2) dir2 cond2 sz2 (LLVMPointer vr2 vo2) end2) =
    case compareF sz1 sz2 of
      LTF -> LT
      GTF -> GT
      EQF ->
        (compare reg1 reg2) <>
        (toOrdering $ compareF off1 off2) <>
        compare dir1 dir2 <>
        (compare cond1 cond2) <>
        (compare vr1 vr2) <>
        (toOrdering $ compareF vo1 vo2) <>
        compare end1 end2

instance PEM.ExprMappable sym (MemOp sym w) where
  mapExpr sym f = \case
    MemOp ptr dir cond w val endian -> do
      ptr' <- WEH.mapExprPtr sym f ptr
      val' <- WEH.mapExprPtr sym f val
      cond' <- PEM.mapExpr sym f cond
      return $ MemOp ptr' dir cond' w val' endian

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MemOp sym ptrW) where
  w4Serialize (MemOp addr dir cond n val end) =
    W4S.object
      [ "addr" .= Ptr.fromLLVMPointer addr
      , "direction" .= dir
      , "condition" .= cond
      , "size" .= n
      , "value" .= Ptr.fromLLVMPointer val
      , "endianness" .=~ end
      ]

ppPtr' :: IsExpr (SymExpr sym) => LLVMPtr sym arch -> Doc ann
ppPtr' ptr@(LLVMPointer r off) 
  | BaseBVRepr w <- exprType off
  = case (asNat r, asBV off) of
  (Just 1, Just off') -> "Stack Slot:" <+> viaShow (BV.asSigned w off')
  _ -> ppPtr ptr

prettyMemOp :: IsExpr (SymExpr sym) => MemOp sym ptrW -> Doc ann
prettyMemOp (MemOp ptr dir cond _sz val _end) =
  viaShow dir <+>
  ppPtr' ptr <+>
  (case dir of Read -> "->" ; Write -> "<-") <+>
  ppPtr val <+>
  case cond of
    Unconditional -> mempty
    Conditional p -> "when" <+> printSymExpr p

data RegOp sym arch =
  RegOp (MapF.MapF (ArchReg arch) (PSr.MacawRegEntry sym))

instance (W4S.W4SerializableFC (ArchReg arch), W4S.SerializableExprs sym)
  => W4S.W4Serializable sym (RegOp sym arch) where
  w4Serialize (RegOp m) = W4S.object ["reg_op" .= m]

instance PEM.ExprMappable sym (RegOp sym arch) where
  mapExpr sym f (RegOp m) = (RegOp . PEM.unExprMapFElems) <$> PEM.mapExpr sym f (PEM.ExprMapFElems m)


data MemEvent sym ptrW where
  MemOpEvent :: MemOp sym ptrW -> MemEvent sym ptrW
  SyscallEvent :: forall sym ptrW w.
    (1 <= w) =>
    MuxTree sym (Maybe (MemSegmentOff ptrW, Text))
      {- ^ location and dissassembly of the instruction generating this system call -} ->
    SymBV sym w
      {- ^ Value of r0 during this syscall -} ->
    MemEvent sym ptrW
  ExternalCallEvent :: forall sym ptrW.
    Text ->
    [ExternalCallData sym ptrW] {- ^ relevant data for this visible call -} ->
    MemEvent sym ptrW

data ExternalCallData sym ptrW =
    forall tp. ExternalCallDataExpr (SymExpr sym tp)
  | ExternalCallDataChunk (MemChunk sym ptrW)

instance PEM.ExprMappable sym (ExternalCallData sym ptrW) where
  mapExpr sym f = \case
    ExternalCallDataExpr e -> ExternalCallDataExpr <$> f e
    ExternalCallDataChunk c -> ExternalCallDataChunk <$> PEM.mapExpr sym f c

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (ExternalCallData sym ptrW) where
  w4Serialize (ExternalCallDataExpr e) = W4S.object ["data_expr" .== e]
  w4Serialize (ExternalCallDataChunk c) = W4S.object ["mem_chunk" .= c]

instance OrdF (SymExpr sym) => Eq (ExternalCallData sym ptrW) where
  a == b = (compare a b == EQ)

instance OrdF (SymExpr sym) => Ord (ExternalCallData sym ptrW) where
  compare (ExternalCallDataExpr e1) (ExternalCallDataExpr e2) = toOrdering $ compareF e1 e2
  compare (ExternalCallDataChunk c1) (ExternalCallDataChunk c2) = compare c1 c2
  compare (ExternalCallDataExpr{}) (ExternalCallDataChunk{}) = LT
  compare (ExternalCallDataChunk{}) (ExternalCallDataExpr{})  = GT

groundExternalCallData ::
  forall sym ptrW t st fs. sym ~ W4B.ExprBuilder t st fs =>
  MemWidth ptrW =>
  sym ->
  W4G.GroundEvalFn t ->
  ExternalCallData sym ptrW ->
  IO (ExternalCallData sym ptrW)
groundExternalCallData sym evalFn = \case
  ExternalCallDataExpr e -> ExternalCallDataExpr <$> do
    e_g <- W4G.groundEval evalFn e
    PVC.symbolicFromConcrete sym e_g e
  ExternalCallDataChunk (MemChunk mem base len) -> ExternalCallDataChunk <$> do
    let ptrW = memWidthNatRepr @ptrW
    base_g <- W4G.groundEval evalFn base
    len_g <- W4G.groundEval evalFn len
    base' <- PVC.symbolicFromConcrete sym base_g base
    len' <- PVC.symbolicFromConcrete sym len_g len
    idxs <- forM [0..(max fIXME_MAX_SYMBOLIC_WRITE (BV.asUnsigned len_g))] $ \i -> do
      let bv_idx = BV.add ptrW base_g (BV.mkBV ptrW i)
      bv_idx_lit <- bvLit sym ptrW bv_idx
      byte <- arrayLookup sym mem (Ctx.empty Ctx.:> bv_idx_lit)
      return $ (Ctx.empty Ctx.:> BVIndexLit ptrW bv_idx, byte)
    let aum = AUM.fromAscList (BaseBVRepr (knownNat @8)) idxs
    zero <- bvLit sym (knownNat @8) (BV.mkBV (knownNat @8) 0)
    mem' <- arrayFromMap sym (Ctx.empty Ctx.:> BaseBVRepr ptrW) aum zero
    return $ MemChunk mem' base' len'

fIXME_MAX_SYMBOLIC_WRITE :: Integer
fIXME_MAX_SYMBOLIC_WRITE = 1

compareExternalCallData ::
  forall sym ptrW.
  IsSymExprBuilder sym =>
  MemWidth ptrW =>
  sym ->
  ExternalCallData sym ptrW ->
  ExternalCallData sym ptrW ->
  IO (Pred sym)
compareExternalCallData sym ec1 ec2 = case (ec1, ec2) of
  (ExternalCallDataExpr e1, ExternalCallDataExpr e2) | Just Refl <- testEquality (exprType e1) (exprType e2) ->
    isEq sym e1 e2
  (ExternalCallDataChunk (MemChunk mem1 base1 len1), ExternalCallDataChunk (MemChunk mem2 base2 len2)) -> do
    len_eq <- isEq sym len1 len2
    let ptrW = MC.memWidthNatRepr @ptrW
    -- FIXME: we only compare a fixed number of elements due to
    -- some incompatibility with arrayCopy and arrayRangeEq that
    -- needs further investigation
    -- also check the last byte, which has a symbolic offset into
    -- the array
    one <- bvLit sym ptrW (BV.mkBV ptrW 1)
    len_minus_one <- bvSub sym len1 one
    last_idx1 <- bvAdd sym base1 len_minus_one
    last_idx2 <- bvAdd sym base1 len_minus_one
    last_byte1 <- arrayLookup sym mem1 (Ctx.empty Ctx.:> last_idx1)
    last_byte2 <- arrayLookup sym mem2 (Ctx.empty Ctx.:> last_idx2)
    last_bytes_eq <- isEq sym last_byte1 last_byte2

    elems_eq <- forM [0..fIXME_MAX_SYMBOLIC_WRITE] $ \i -> do
      bv_off_lit <- bvLit sym ptrW (BV.mkBV ptrW i)
      bv_idx1 <- bvAdd sym base1 bv_off_lit
      bv_idx2 <- bvAdd sym base2 bv_off_lit
      byte1 <- arrayLookup sym mem1 (Ctx.empty Ctx.:> bv_idx1)
      byte2 <- arrayLookup sym mem2 (Ctx.empty Ctx.:> bv_idx2)
      in_range <- bvUle sym bv_off_lit len1
      eq_bytes <- isEq sym byte1 byte2
      impliesPred sym in_range eq_bytes
    foldM (andPred sym) len_eq (last_bytes_eq:elems_eq)
    {-
    arr_eq <- arrayRangeEq sym mem1 base1 mem2 base2 len1
    andPred sym len_eq arr_eq
    -}
  _ -> return $ falsePred sym

printExternalCallData ::
  IsExpr (SymExpr sym) =>
  MemWidth ptrW =>
  ExternalCallData sym ptrW ->
  Doc a
printExternalCallData (ExternalCallDataExpr e) = printSymExpr e
printExternalCallData (ExternalCallDataChunk (MemChunk mem1 base1 len1)) =
  "TODO print mem chunk: " <+> printSymExpr mem1 <+> printSymExpr base1 <+> printSymExpr len1

data MemChunk sym ptrW = MemChunk
  { memChunkArr :: SymExpr sym (BaseArrayType (Ctx.EmptyCtx Ctx.::> BaseBVType ptrW) (BaseBVType 8))
  , memChunkBase :: SymExpr sym (BaseBVType ptrW)
  , memChunkLen :: SymExpr sym (BaseBVType ptrW)
  }

instance OrdF (SymExpr sym) => Eq (MemChunk sym ptrW) where
  a == b = (compare a b == EQ)

instance OrdF (SymExpr sym) => Ord (MemChunk sym ptrW) where
  compare (MemChunk a1 b1 c1) (MemChunk a2 b2 c2) =
    (toOrdering $ compareF a1 a2) <> (toOrdering $ compareF b1 b2) <>(toOrdering $ compareF c1 c2)

instance OrdF (SymExpr sym) => Eq (MemEvent sym ptrW) where
  a == b = case compare a b of
    EQ -> True
    _ -> False

instance PEM.ExprMappable sym (MemChunk sym ptrW) where
  mapExpr _sym f (MemChunk a b c) = MemChunk <$> f a <*> f b <*> f c

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MemChunk sym ptrW) where
  w4Serialize (MemChunk a b c) = W4S.object ["mem_arr" .== a, "base" .== b, "len" .== c]

-- | Overwrite the contents of a base memory chunk with new contents at a
--   given offset.
copyMemChunkInto :: 
  IsSymExprBuilder sym =>
  1 <= ptrW =>
  sym ->
  MemChunk sym ptrW {- ^ base chunk -} ->
  SymBV sym ptrW {- ^ index into base chunk to copy contents -} ->
  MemChunk sym ptrW {- ^ new contents -} ->
  IO (MemChunk sym ptrW)
copyMemChunkInto sym baseChunk startIdx srcChunk = do
  baseIdx <- bvAdd sym (memChunkBase baseChunk) startIdx
  arr' <- case asConcrete (memChunkLen srcChunk) of
    Just (W4C.ConcreteBV ptrW srcLenBV) -> do
      let srcLen = BV.asUnsigned srcLenBV
      upds <- forM [0 .. srcLen] $ \idx -> do
        idxSym <- bvLit sym ptrW (BV.mkBV ptrW idx)
        srcIdx <- bvAdd sym (memChunkBase srcChunk) idxSym
        -- chunk base + starting index + byte index
        baseIdx' <- bvAdd sym baseIdx idxSym
        srcByte <- arrayLookup sym (memChunkArr srcChunk) (Ctx.singleton srcIdx)
        return (Ctx.singleton baseIdx', srcByte)
      foldlM (\a (baseIdx', srcByte) -> arrayUpdate sym a baseIdx' srcByte) (memChunkArr baseChunk) upds
    _ ->
      arrayCopy sym (memChunkArr baseChunk) baseIdx (memChunkArr baseChunk) (memChunkBase baseChunk) (memChunkLen srcChunk)
  baseTop <- bvAdd sym baseIdx (memChunkLen srcChunk)
  -- we may extend the size of the base chunk if we write bytes past the top of
  -- its contents
  len' <- WEH.bvUMax sym (memChunkLen baseChunk) baseTop
  return $ baseChunk { memChunkArr = arr', memChunkLen = len'}


-- | Create a 'MemChunk' with concrete contents.
concreteMemChunk ::
  IsSymExprBuilder sym =>
  Integral x =>
  1 <= ptrW =>
  sym ->
  MC.Endianness ->
  NatRepr ptrW ->
  x {- ^ concrete contents (clamped to number of bytes ) -} ->
  Natural {- ^ number of bytes  -} ->
  IO (MemChunk sym ptrW)
concreteMemChunk sym endianness ptrW contents bytesLen = do
  Some bitsLen <- return $ mkNatRepr (bytesLen * 8)
  let contentsBV = BV.unsignedClamp bitsLen (fromIntegral contents)
  let mbytes = case endianness of
        MC.BigEndian -> BV.asBytesBE bitsLen contentsBV
        MC.LittleEndian -> BV.asBytesLE bitsLen contentsBV
  bytes <- case mbytes of
    Just bytes -> return bytes
    Nothing -> fail "concreteMemChunk: impossible"
  let arrTp = Ctx.singleton (BaseBVRepr ptrW)
  let indices = map (Ctx.singleton . BVIndexLit ptrW . BV.mkBV ptrW . fromIntegral) [0 .. bytesLen]
  bytesSym <- mapM (bvLit sym (knownNat @8) . BV.word8) bytes
  let contentsBytes = AUM.fromAscList (BaseBVRepr (knownNat @8)) (zip indices bytesSym)
  zeroByte <- bvLit sym (knownNat @8) (BV.zero (knownNat @8))
  arr <- arrayFromMap sym arrTp contentsBytes zeroByte
  zeroIndex <- bvLit sym ptrW (BV.zero ptrW)
  lenSymBV <- bvLit sym ptrW (BV.mkBV ptrW (fromIntegral bytesLen))
  return $ MemChunk arr zeroIndex lenSymBV

muxMemChunk ::
  IsSymExprBuilder sym =>
  sym ->
  Pred sym ->
  MemChunk sym ptrW ->
  MemChunk sym ptrW ->
  IO (MemChunk sym ptrW)
muxMemChunk sym p chunkT chunkF = do
  arr <- baseTypeIte sym p (memChunkArr chunkT) (memChunkArr chunkF)
  base <- baseTypeIte sym p (memChunkBase chunkT) (memChunkBase chunkF)
  len <- baseTypeIte sym p (memChunkLen chunkT) (memChunkLen chunkF)
  return $ MemChunk arr base len

compareTrees :: OrdF (SymExpr sym) => Ord tp => MuxTree sym tp -> MuxTree sym tp -> Ordering
compareTrees mt1 mt2 = 
  let 
    es1 = map (\(x, p) -> (x, AsOrd p)) $ viewMuxTree mt1
    es2 = map (\(x, p) -> (x, AsOrd p)) $ viewMuxTree mt2
  in compare es1 es2

instance OrdF (SymExpr sym) => Ord (MemEvent sym ptrW) where
  compare a b = case (a,b) of
    (MemOpEvent op1, MemOpEvent op2) -> compare op1 op2
    (SyscallEvent mt1 bv1, SyscallEvent mt2 bv2) -> compareTrees mt1 mt2 <> (toOrdering $ compareF bv1 bv2)
    (ExternalCallEvent nm1 vs1, ExternalCallEvent nm2 vs2) -> 
      compare nm1 nm2 <> (compare vs1 vs2)
    (MemOpEvent{}, _) -> GT
    (SyscallEvent{}, ExternalCallEvent{}) -> GT
    (ExternalCallEvent{}, _) -> LT
    (SyscallEvent{}, MemOpEvent{}) -> LT

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (MemEvent sym ptrW) where
  w4Serialize = \case
    MemOpEvent mop -> W4S.object ["mem_op" .= mop]
    SyscallEvent i r0 -> W4S.object ["syscall" .= i, "r0" .== r0]
    ExternalCallEvent nm bvs -> W4S.object ["external_call" .= nm, "args" .= bvs]

prettyMemEvent :: (MemWidth ptrW, IsExpr (SymExpr sym)) => MemEvent sym ptrW -> Doc ann
prettyMemEvent (MemOpEvent op) = prettyMemOp op
prettyMemEvent (SyscallEvent i v) =
  case viewMuxTree i of
    [(Just (addr, dis), _)] -> "Syscall At:" <+> viaShow addr <+> pretty dis <> line <> printSymExpr v
    _ -> "Syscall" <+> printSymExpr v
prettyMemEvent (ExternalCallEvent nm vs) = "External Call At:" <+> pretty nm <+> vsep (map printExternalCallData vs)


instance (MemWidth ptrW, IsExpr (SymExpr sym)) => Pretty (MemEvent sym ptrW) where
  pretty ev = prettyMemEvent ev

instance PEM.ExprMappable sym (MemEvent sym w) where
  mapExpr sym f = \case
    MemOpEvent op -> MemOpEvent <$> PEM.mapExpr sym f op
    SyscallEvent i arg -> SyscallEvent i <$> f arg
    -- MuxTree is unmodified since it has no symbolic expressions
    ExternalCallEvent nm vs -> ExternalCallEvent nm <$> PEM.mapExpr sym f vs


filterEvent ::
  IsExprBuilder sym =>
  sym ->
  (MemOp sym ptrW -> IO (Pred sym)) ->
  MemEvent sym ptrW ->
  IO (Maybe (MemEvent sym ptrW), Pred sym)
filterEvent sym f x = case x of
    -- always include system call events
    SyscallEvent{} -> return $ (Nothing, truePred sym)
    -- always include external call events
    ExternalCallEvent{} -> return $ (Nothing, truePred sym)
    
    -- Include memory operations only if they acutally
    -- happen (their condition is true) and if they are
    -- deemed observable by the given filtering function.
    MemOpEvent op@(MemOp ptr dir cond w val end) -> do
      opObservable <- f op
      p <- andPred sym opObservable (getCond sym cond)
      let x' = MemOpEvent (MemOp ptr dir Unconditional w val end)
      return $ (Just x', p)


-- | Used for presenting counter-examples that contain all register updates
data TraceEvent sym arch =
    RegOpEvent { traceInstr :: MuxTree sym (Maybe (ArchSegmentOff arch, Text)), _traceRegOp :: RegOp sym arch }
  | TraceMemEvent { traceInstr :: MuxTree sym (Maybe (ArchSegmentOff arch, Text)), _traceMemEvent :: MemEvent sym (ArchAddrWidth arch)}

instance W4S.W4Serializable sym  (MemSegmentOff w) where
  w4Serialize segOff = W4S.w4Serialize $ segoffAddr segOff

instance PEM.ExprMappable sym (MemSegmentOff w) where
  mapExpr _ _ = return

instance PEM.ExprMappable sym (TraceEvent sym arch) where
  mapExpr sym f e = case e of
    RegOpEvent i rop -> RegOpEvent <$> PEM.mapExpr sym f i <*> PEM.mapExpr sym f rop
    TraceMemEvent i mop -> TraceMemEvent <$> PEM.mapExpr sym f i <*> PEM.mapExpr sym f mop

instance W4S.W4Serializable sym  (MemAddr w) where
  w4Serialize addr = do
    base_json <- return $ JSON.toJSON (addrBase addr)
    off_json <- return $ JSON.toJSON (show (addrOffset addr))
    return $ JSON.object ["base" JSON..= base_json, "offset" JSON..= off_json]

instance (W4S.W4SerializableFC (ArchReg arch), W4S.SerializableExprs sym)
  => W4S.W4Serializable sym (TraceEvent sym arch) where
    w4Serialize = \case
      RegOpEvent i rop -> W4S.object ["instruction" .= i, "register_op" .= rop]
      TraceMemEvent i mop -> W4S.object ["instruction" .= i, "memory_op" .= mop]



type EventTrace sym arch = SymSequence sym (TraceEvent sym arch)

data InstructionEvent arch = InstructionEvent { instrAddr :: ArchSegmentOff arch, instrDisassembled :: Text }
  deriving (Eq, Ord)

-- trivial instance - no symbolic data
instance PEM.ExprMappable sym (InstructionEvent arch) where
  mapExpr _sym _f e = return e

instance W4S.W4Serializable sym (InstructionEvent arch) where
  w4Serialize (InstructionEvent addr dis) = W4S.object ["address" .= addr, "disassembled" .= dis]

deriving instance MemWidth (RegAddrWidth (ArchReg arch)) => Show (InstructionEvent arch)

type InstructionTrace sym arch = SymSequence sym (InstructionEvent arch)



