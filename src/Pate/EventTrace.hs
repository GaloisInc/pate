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

{-|
Module           : Pate.EventTrace
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Defines data structures relating to collecting traces of events during
symbolic execution.

-}

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
, ppPtr'
, prettyMemOp
, prettyMemEvent
, filterEvent
) where

import           Prettyprinter
import qualified Data.BitVector.Sized as BV
import           Data.Text ( Text )
import qualified Control.Monad.IO.Class as IO

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface hiding ( integerToNat )

import           Lang.Crucible.LLVM.MemModel (LLVMPtr, pattern LLVMPointer, ppPtr)
import           Lang.Crucible.Utils.MuxTree ( MuxTree, viewMuxTree )
import           Lang.Crucible.Simulator.SymSequence ( SymSequence(..), muxSymSequence, evalWithFreshCache, nilSymSequence, consSymSequence, appendSymSequence )

import           Data.Macaw.Memory (Endianness(..), MemSegmentOff, MemWidth, MemAddr (..), segoffAddr)
import           Data.Macaw.CFG.AssignRhs (ArchAddrWidth, ArchReg)
import           Data.Macaw.CFG (ArchSegmentOff)

import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON
import           What4.JSON ((.=), (.==), (.=~))

import           Data.Parameterized.SetF (AsOrd(..))
import qualified Pate.ExprMappable as PEM
import qualified Pate.SimulatorRegisters as PSr
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Pate.Pointer as Ptr


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
    Ctx.Assignment (SymBV' sym) ctx
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
prettyMemEvent (ExternalCallEvent nm vs) = "External Call At:" <+> pretty nm <+> pretty (show vs)


instance (MemWidth ptrW, IsExpr (SymExpr sym)) => Pretty (MemEvent sym ptrW) where
  pretty ev = prettyMemEvent ev

instance PEM.ExprMappable sym (MemEvent sym w) where
  mapExpr sym f = \case
    MemOpEvent op -> MemOpEvent <$> PEM.mapExpr sym f op
    SyscallEvent i arg -> SyscallEvent i <$> f arg
    -- MuxTree is unmodified since it has no symbolic expressions
    ExternalCallEvent nm vs -> ExternalCallEvent nm <$> TFC.traverseFC (PEM.mapExpr sym f) vs


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