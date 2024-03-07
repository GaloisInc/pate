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
, asInstructionTrace
, takeMatchingPrefix
, takeMatchingPrefix2
, reverseSeq
, collapsePartialSeq
, compareSymSeq
, concatSymSequence
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

import           Data.Macaw.Memory (Endianness(..), MemSegmentOff, MemWidth, MemAddr (..), segoffAddr)
import           Data.Macaw.CFG.AssignRhs (ArchAddrWidth, ArchReg)
import           Data.Macaw.CFG (ArchSegmentOff, RegAddrWidth)

import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON
import           What4.JSON ((.=), (.==), (.=~))

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
  ExternalCallEvent :: forall sym ptrW ctx.
    Text ->
    Ctx.Assignment (SymExpr sym) ctx
      {- ^ relevant data for this visible call -} ->
    MemEvent sym ptrW

instance OrdF (SymExpr sym) => Eq (MemEvent sym ptrW) where
  a == b = case compare a b of
    EQ -> True
    _ -> False

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
      compare nm1 nm2 <> (toOrdering $ (compareF vs1 vs2))
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
prettyMemEvent (ExternalCallEvent nm vs) = "External Call At:" <+> pretty nm <+> vsep (TFC.toListFC printSymExpr vs)


instance (MemWidth ptrW, IsExpr (SymExpr sym)) => Pretty (MemEvent sym ptrW) where
  pretty ev = prettyMemEvent ev

instance PEM.ExprMappable sym (MemEvent sym w) where
  mapExpr sym f = \case
    MemOpEvent op -> MemOpEvent <$> PEM.mapExpr sym f op
    SyscallEvent i arg -> SyscallEvent i <$> f arg
    -- MuxTree is unmodified since it has no symbolic expressions
    ExternalCallEvent nm vs -> ExternalCallEvent nm <$> TFC.traverseFC f vs


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

-- | FIXME: move somewhere more general
instance PEM.ExprMappable sym a => PEM.ExprMappable sym (SymSequence sym a) where
  mapExpr sym f = evalWithFreshCache $ \rec -> \case
    SymSequenceNil -> IO.liftIO $ nilSymSequence sym
    SymSequenceCons _ x xs ->
      do x'  <- PEM.mapExpr sym f x
         xs' <- rec xs
         IO.liftIO $ consSymSequence sym x' xs'
    SymSequenceAppend _ xs ys ->
     do xs' <- rec xs
        ys' <- rec ys
        IO.liftIO $ appendSymSequence sym xs' ys'
    SymSequenceMerge _ p xs ys ->
     do p' <- f p
        case asConstantPred p' of
          Just True -> rec xs
          Just False -> rec ys
          Nothing -> do
            xs' <- rec xs
            ys' <- rec ys
            IO.liftIO $ muxSymSequence sym p' xs' ys'

type EventTrace sym arch = SymSequence sym (TraceEvent sym arch)

data InstructionEvent arch = InstructionEvent { instrAddr :: ArchSegmentOff arch, instrDisassembled :: Text }
  deriving (Eq, Ord)

deriving instance MemWidth (RegAddrWidth (ArchReg arch)) => Show (InstructionEvent arch)

type InstructionTrace sym arch = SymSequence sym (InstructionEvent arch)


singleSeq ::
  forall sym a.
  IsExprBuilder sym =>
  sym ->
  a ->
  IO (SymSequence sym a)
singleSeq sym a = do
  n <- nilSymSequence sym
  consSymSequence sym a n

-- | Convert a 'MuxTree' into a sequence with length at most 1, collapsing all 'Nothing' results
--   from the given function into an empty sequence.
muxTreeToSeq ::
  forall sym a b.
  IsExprBuilder sym =>
  sym ->
  (a -> IO (Maybe b)) ->
  MuxTree sym a ->
  IO (SymSequence sym b)
muxTreeToSeq sym f mt = do
  es <- fmap catMaybes $ forM (viewMuxTree mt) $ \(x, p) -> f x >>= \case
    Just y -> return $ Just (p, y)
    Nothing -> return Nothing
  collect es
  where
    collect :: [(Pred sym, b)] -> IO (SymSequence sym b)
    collect [] = nilSymSequence sym
    collect ((p,y):ys) = do
      y_seq <- singleSeq sym y
      ys_seq <- collect ys
      muxSymSequence sym p y_seq ys_seq

asInstructionTrace ::
  forall sym arch.
  IsExprBuilder sym =>
  sym ->
  EventTrace sym arch ->
  IO (InstructionTrace sym arch)
asInstructionTrace sym e_seq = mapConcatSeq sym g e_seq
  where
    g :: TraceEvent sym arch -> IO (InstructionTrace sym arch)
    g e@RegOpEvent{} = muxTreeToSeq sym (\x -> return $ fmap (\(addr,dis) -> InstructionEvent addr dis) x) (traceInstr e)
    -- NB: we ignore memory events under the assumption that every memory event will be paired with a register event
    -- that at least updates the PC afterwards
    g _ = nilSymSequence sym

-- TODO: These are general functions over symbolic sequences that should probably be
-- moved into What4
-- Likely will want some low-level testing since their semantics are somewhat non-trivial
-- The intention is that they should be useful for matching up control flow by investigating InstructionEvent sequences

-- | Smarter mux that checks for predicate concreteness
muxSymSequence' ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  SymSequence sym a ->
  SymSequence sym a ->
  m (SymSequence sym a)
muxSymSequence' sym p sT sF = case asConstantPred p of
  Just True -> return sT
  Just False -> return sF
  Nothing -> IO.liftIO $ muxSymSequence sym p sT sF

appendSingle ::
  IO.MonadIO m =>
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  a ->
  m (SymSequence sym a)
appendSingle sym s a = IO.liftIO $ do
  a_seq <- consSymSequence sym a =<< nilSymSequence sym
  appendSymSequence sym s a_seq

muxSeqM ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a) ->
  m (SymSequence sym a) ->
  m (SymSequence sym a)
muxSeqM sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    aT <- f_s1
    aF <- f_s2
    muxSymSequence' sym p aT aF

muxSeqM2 ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a, SymSequence sym b) ->
  m (SymSequence sym a, SymSequence sym b) ->
  m (SymSequence sym a, SymSequence sym b)
muxSeqM2 sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    (a1,b1) <- f_s1
    (a2,b2) <- f_s2
    a <- muxSymSequence' sym p a1 a2
    b <- muxSymSequence' sym p b1 b2
    return $ (a,b)

-- | Apply a partial function to a sequence, returning the longest
--   prefix of nonempty results.
--   For example, given any predicate 'p' and 'f a :=  if p a then Just a else Nothing'
--   Then we expect the following to hold:
--     let (result, as_suffix) = takeMatchingPrefix f as
--     in   result ++ as_suffix == as
--       && all r result
--       && not (p (head as_suffix))
--   Notably this is semantic equality since 'p' is a symbolic predicate
--   TODO: caching?
--   TODO: if 'a' and 'b' are the same type there are a few optimizations
--     that could be made to avoid re-creating sub-sequences
takeMatchingPrefix ::
  forall sym m a b.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> m (PartExpr (Pred sym) b)) ->
  SymSequence sym a ->
  m (SymSequence sym b, SymSequence sym a)
takeMatchingPrefix sym f s_a_outer = go SymSequenceNil s_a_outer
  where
    go :: SymSequence sym b -> SymSequence sym a -> m (SymSequence sym b, SymSequence sym a)
    go acc s_a = case s_a of
      SymSequenceNil -> return $ (acc, s_a)
      (SymSequenceCons _ a s_a') -> do
        f a >>= \case
          Unassigned -> return $ (acc, s_a)
          PE p v -> muxSeqM2 sym p
            -- for a 'Just' result we add it to the accumulated prefix and continue
            ((IO.liftIO $ appendSingle sym acc v) >>= \acc' -> go acc' s_a')
            -- otherwise we return the current accumulated prefix and stop
            (return (acc, s_a))
      (SymSequenceAppend _ a1 a2) -> do
        (acc', a1_suf) <- go acc a1
        p <- IO.liftIO $ isNilSymSequence sym a1_suf
        muxSeqM2 sym p
          (go acc' a2) $ do
            a2_suf <- if a1 == a1_suf then return s_a
              else IO.liftIO $ appendSymSequence sym a1_suf a2
            return (acc', a2_suf)
      (SymSequenceMerge _ p a_T a_F) -> muxSeqM2 sym p (go acc a_T) (go acc a_F)

muxSeqM3 ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c) ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c) ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c)
muxSeqM3 sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    (a1,b1,c1) <- f_s1
    (a2,b2,c2) <- f_s2
    a <- muxSymSequence' sym p a1 a2
    b <- muxSymSequence' sym p b1 b2
    c <- muxSymSequence' sym p c1 c2
    return $ (a,b,c)


-- TODO: This is a duplicate of Pate.Verification.StrongestPosts.SeqPairCache
-- Replacing 'equivalentSequences' in that module with 'compareSymSeq' will also
-- let us remove the duplicates there
data SeqPairCache a b c = SeqPairCache (IO.IORef (Map.Map (Maybe (Nonce GlobalNonceGenerator a), Maybe (Nonce GlobalNonceGenerator b)) c))

newSeqPairCache :: IO (SeqPairCache a b c)
newSeqPairCache = SeqPairCache <$> IO.newIORef Map.empty

-- TODO: clagged from SymSequence module, should probably be exported, either
-- directly or with some abstraction for the nonces
symSequenceNonce :: SymSequence sym a -> Maybe (Nonce GlobalNonceGenerator a)
symSequenceNonce SymSequenceNil = Nothing
symSequenceNonce (SymSequenceCons n _ _ ) = Just n
symSequenceNonce (SymSequenceAppend n _ _) = Just n
symSequenceNonce (SymSequenceMerge n _ _ _) = Just n

-- TODO: duplicated in Pate.Verification.StrongestPosts, see above
evalWithPairCache :: IO.MonadIO m =>
  SeqPairCache a b c ->
  SymSequence sym a ->
  SymSequence sym b ->
  m c ->
  m c
evalWithPairCache (SeqPairCache ref) seq1 seq2 f = do
  m <- IO.liftIO (IO.readIORef ref)
  let k = (symSequenceNonce seq1, symSequenceNonce seq2)
  case Map.lookup k m of
    Just v -> return v
    Nothing -> do
      v <- f
      IO.liftIO (IO.modifyIORef ref (Map.insert k v))
      return v

zipSeq' ::
  forall sym a b.
  IsSymExprBuilder sym =>
  sym ->
  SeqPairCache a b (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b) ->
  SymSequence sym a ->
  SymSequence sym b ->
  IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
zipSeq' sym cache as_outer bs_outer = go as_outer bs_outer
  where
    handle_append :: forall x y.
      (SymSequence sym x -> SymSequence sym y -> IO (SymSequence sym (a,b), SymSequence sym x, SymSequence sym y)) ->
      SymSequence sym x ->
      SymSequence sym y ->
      Maybe (IO (SymSequence sym (a,b), SymSequence sym x, SymSequence sym y))
    handle_append rec xs@(SymSequenceAppend _ xs_1 xs_2) ys = Just $ do
      (acc, xs_suf', ys_suf) <- rec xs_1 ys
      p <- isNilSymSequence sym xs_suf'
      (acc', xs_fin, ys_fin) <- muxSeqM3 sym p
        -- if xs_suf' is nil then it means we consumed all of the first
        -- and thus we can continue zipping elements
        (do
          (acc', xs_fin, ys_fin) <- rec xs_2 ys_suf
          return (acc', xs_fin, ys_fin)
          ) $ do
          -- otherwise, we append the tail to the found suffix and return
          -- as a small optimization, if the suffix is the same as the input
          -- then we don't need to create a new sequence for appended suffix
        xs_suf'' <- if xs_suf' == xs_1 then return xs
          else appendSymSequence sym xs_suf' xs_2
        return $ (SymSequenceNil, xs_suf'', ys_suf)
      acc'' <- appendSymSequence sym acc acc'
      return (acc'', xs_fin, ys_fin)

    handle_append _ _ _ = Nothing
    go' :: SymSequence sym b -> SymSequence sym a -> IO (SymSequence sym (a,b), SymSequence sym b, SymSequence sym a)
    go' s_b s_a = go s_a s_b >>= \(acc, s_a', s_b') -> return (acc, s_b', s_a')

    go :: SymSequence sym a -> SymSequence sym b -> IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
    go s_a s_b = evalWithPairCache cache s_a s_b $ case (s_a, s_b) of
      -- if either sequence is nil that we can't extend the matching prefix any more
      -- and so we return
      (_, SymSequenceNil) -> return $ (SymSequenceNil, s_a, s_b)
      (SymSequenceNil, _) -> return $ (SymSequenceNil, s_a, s_b)
      (SymSequenceCons _ a s_a', SymSequenceCons _ b s_b') -> do

        (acc, suf_a, suf_b) <- go s_a' s_b'
        acc' <- IO.liftIO $ appendSingle sym acc (a,b)
        return (acc', suf_a, suf_b)
      _ | Just g <- handle_append go s_a s_b -> g
      _ | Just g <- handle_append go' s_b s_a -> g >>= \(acc', s_b', s_a') -> return (acc', s_a', s_b')
      (SymSequenceMerge _ p_a a_T a_F, SymSequenceMerge _ p_b b_T b_F)
        | Just Refl <- testEquality p_a p_b -> muxSeqM3 sym p_a (go a_T b_T)  (go a_F b_F)
      (SymSequenceMerge _ p_a a_T a_F, SymSequenceMerge _ p_b b_T b_F) -> do
        p_a_p_b <- andPred sym p_a p_b
        not_p_a <- notPred sym p_a
        not_p_b <- notPred sym p_b
        not_p_a_not_p_b <- andPred sym not_p_a not_p_b

        muxSeqM3 sym p_a_p_b (go a_T b_T) $
          muxSeqM3 sym not_p_a_not_p_b (go a_F b_F) $
            muxSeqM3 sym p_a (go a_T b_F) (go a_F b_T)

      (SymSequenceMerge _ p a_T a_F, _) -> muxSeqM3 sym p (go a_T s_b) (go a_F s_b)
      (_, SymSequenceMerge _ p b_T b_F) -> muxSeqM3 sym p (go s_a b_T) (go s_a b_F)
      (SymSequenceAppend{}, _) -> error "zipSeq: handle_append unexpectedly failed"
      (_, SymSequenceAppend{}) -> error "zipSeq: handle_append unexpectedly failed"


-- | Zip two sequences pointwise. If one is longer than the other, return
--   the suffix of elements.
--   Notably this is not an 'Either' result (i.e. returning only the suffix of the longer sequence),
--   as both suffixes may be nontrivial and symbolic.
zipSeq ::
  forall sym a b.
  IsSymExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  SymSequence sym b ->
  IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
zipSeq sym as bs = newSeqPairCache >>= \cache -> zipSeq' sym cache as bs

unzipSeq ::
  forall sym a b.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym (a,b) ->
  IO (SymSequence sym a, SymSequence sym b)
unzipSeq sym s = do
  s_a <- traverseSymSequence sym (\(a, _) -> return a) s
  s_b <- traverseSymSequence sym (\(_, b) -> return b) s
  return (s_a, s_b)

-- | Same as 'evalWithFreshCache' but without the result type depending on 'a'
evalWithFreshCache' ::
  forall sym m a b.
  IO.MonadIO m =>
  ((SymSequence sym a -> m b) -> SymSequence sym a -> m b) ->
  (SymSequence sym a -> m b)
evalWithFreshCache' f s_outer = getConst <$> evalWithFreshCache (\rec s -> Const <$> f (do_wrap rec) s) s_outer
  where
    do_wrap :: (SymSequence sym a -> m (Const b a)) -> (SymSequence sym a -> m b)
    do_wrap g = \s -> getConst <$> g s

mapConcatSeq ::
  forall sym m a b.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> m (SymSequence sym b)) ->
  SymSequence sym a ->
  m (SymSequence sym b)
mapConcatSeq sym f s_a_outer = evalWithFreshCache' go s_a_outer
  where
    go :: (SymSequence sym a -> m (SymSequence sym b)) -> SymSequence sym a -> m (SymSequence sym b)
    go _ SymSequenceNil = IO.liftIO $ nilSymSequence sym
    go rec (SymSequenceCons _ a as) = do
      bs <- f a
      bs' <- rec as
      IO.liftIO $ appendSymSequence sym bs bs'
    go rec (SymSequenceAppend _ as1 as2) = do
      bs1 <- rec as1
      bs2 <- rec as2
      IO.liftIO $ appendSymSequence sym bs1 bs2
    go rec (SymSequenceMerge _ p asT asF) =
      muxSeqM sym p (rec asT) (rec asF)

partToSeq ::
  forall sym c.
  IsExprBuilder sym =>
  sym ->
  PartExpr (Pred sym) c ->
  IO (SymSequence sym c)
partToSeq sym = \case
  Unassigned -> nilSymSequence sym
  PE p c -> muxSeqM sym p (singleSeq sym c) (nilSymSequence sym)

-- | Collapses partial elements into empty sub-sequences
collapsePartialSeq ::
  forall sym c.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym (PartExpr (Pred sym) c) ->
  IO (SymSequence sym c)
collapsePartialSeq sym s_outer = mapConcatSeq sym (partToSeq sym) s_outer

-- | Apply a partial function pairwise to two sequences, returning the longest
--   prefix of nonempty results.
--   For example, given any relation 'r' and 'f a b :=  if r (a, b) then Just (a, b) else Nothing'
--   Then we expect the following to hold:
--     let (result, as_suffix, bs_suffix) = takeMatchingPrefix2 f as bs
--     in   (map fst result) ++ as_suffix == as
--       && (map snd result) ++ bs_suffix == bs
--       && all r result
--       && not (r (head as_suffix, head bs_suffix))
--   Notably this is semantic equality since 'r' is a symbolic relation
--   TODO: caching?
takeMatchingPrefix2 ::
  forall sym m a b c.
  IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> b -> m (PartExpr (Pred sym) c)) ->
  SymSequence sym a ->
  SymSequence sym b ->
  m (SymSequence sym c, SymSequence sym a, SymSequence sym b)
takeMatchingPrefix2 sym f s_a_outer s_b_outer = do
  (zipped, as_suffix, bs_suffix) <- IO.liftIO $ zipSeq sym s_a_outer s_b_outer
  (matching_prefix, as_bs_suffix) <- takeMatchingPrefix sym (\(a,b) -> f a b) zipped
  (as_suffix', bs_suffix') <- IO.liftIO $ unzipSeq sym as_bs_suffix
  as_suffix'' <- IO.liftIO $ appendSymSequence sym as_suffix' as_suffix
  bs_suffix'' <- IO.liftIO $ appendSymSequence sym bs_suffix' bs_suffix
  return (matching_prefix, as_suffix'', bs_suffix'')

-- | Reverse the order of elements in a sequence
--   TODO: caching?
reverseSeq ::
  forall sym a.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  IO (SymSequence sym a)
reverseSeq sym s_outer = evalWithFreshCache go s_outer
  where
    go :: (SymSequence sym a -> IO (SymSequence sym a)) -> SymSequence sym a -> IO (SymSequence sym a)
    go _ SymSequenceNil = nilSymSequence sym
    go rec (SymSequenceCons _ a as) = rec as >>= \as_rev -> appendSingle sym as_rev a
    go rec (SymSequenceAppend _ as bs) = do
      as_rev <- rec as
      bs_rev <- rec bs
      appendSymSequence sym bs_rev as_rev
    go rec (SymSequenceMerge _ p sT sF) = do
      sT_rev <- rec sT
      sF_rev <- rec sF
      muxSymSequence sym p sT_rev sF_rev

-- | Concatenate the elements of a 'SymSequence' together
--   using the provided combine and mux operations and
--   empty value.
concatSymSequence ::
  forall sym m c.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (Pred sym -> c -> c -> m c) {-^ mux for 'c' -} ->
  (c -> c -> m c) {-^ combining 'c' values -} ->
  c {-^ empty c -} ->
  SymSequence sym c ->
  m c
concatSymSequence _sym f g c_init s_outer = getConst <$> evalWithFreshCache go s_outer
  where
    go :: (SymSequence sym c -> m ((Const c) c)) -> SymSequence sym c -> m ((Const c) c)
    go rec s = fmap Const $ case s of
      SymSequenceNil -> return $ c_init
      SymSequenceCons _ c1 sa -> do
        Const c2 <- rec sa
        g c1 c2
      SymSequenceAppend _ sa1 sa2 -> do
        Const c1 <- rec sa1
        Const c2 <- rec sa2
        g c1 c2
      SymSequenceMerge _ p' saT saF -> do
        Const cT <- rec saT
        Const cF <- rec saF
        f p' cT cF

-- | Pointwise comparison of two sequences. When they are (semantically) not
--   the same length, the resulting predicate is False. Otherwise it is
--   the result of 'f' on each pair of values.
--   TODO: Pate.Verification.StrongestPosts.equivalentSequences should be
--   replaced with this. They are semantically equivalent, however
--   'zipSeq' creates more concise terms in cases where the predicates
--   for sequence merges aren't exactly equivalent between the two sequences.

compareSymSeq ::
  forall sym a b m.
  IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  SymSequence sym a ->
  SymSequence sym b ->
  (a -> b -> m (Pred sym)) ->
  m (Pred sym)
compareSymSeq sym sa sb f = do
  (matching_pfx, suf_a, suf_b) <- IO.liftIO $ zipSeq sym sa sb
  f_seq <- traverseSymSequence sym (\(a,b) -> f a b) matching_pfx
  nil_a <- IO.liftIO $ isNilSymSequence sym suf_a
  nil_b <- IO.liftIO $ isNilSymSequence sym suf_b

  matching_head <- concatSymSequence sym
    (\p a b -> IO.liftIO $ baseTypeIte sym p a b)
    (\a b -> IO.liftIO $ andPred sym a b)
    (truePred sym)
    f_seq
  IO.liftIO $ andPred sym matching_head nil_a >>= andPred sym nil_b
