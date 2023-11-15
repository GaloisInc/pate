{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}


{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Verification.StrongestPosts.CounterExample
  ( TotalityCounterexample(..)
  , ObservableCounterexample(..)
  , RegsCounterExample(..)
  , prettyRegsCE
  , ObservableCheckResult(..)
  , groundObservableSequence
  , groundMuxTree
  , groundMemEvent
  ) where


import           Data.Text (Text)
import           Numeric (showHex)

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.Memory.MemTrace as MT
import           Pate.TraceTree
import qualified Pate.Proof.Instances as PPI
import qualified Pate.Solver as PSo
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.PatchPair as PPa
import Control.Monad.Identity
import Control.Monad.Trans.Writer
import Pate.Register.Traversal (zipWithRegStatesM)
import qualified Pate.Arch as PA
import qualified What4.Expr as W4
import Data.Parameterized.NatRepr
import qualified What4.Interface as W4
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Lang.Crucible.LLVM.MemModel as CLM
import           Lang.Crucible.Simulator.SymSequence

-- | A totality counterexample represents a potential control-flow situation that represents
--   desynchronization of the original and patched program. The first tuple represents
--   the control-flow of the original program, and the second tuple represents the patched
--   program.  Each tuple contains the target address of the control-flow instruction,
--   the type of control-flow it represents, and the address and dissassembly of the
--   instruction causing the control flow. The final node is a Maybe because we cannot
--   entirely guarantee that the information on the instruction causing control flow is
--   avaliable, although we expect that it always should be.
--
--   Note that because of the overapproximation implied by the abstract domains, the
--   computed counterexamples may actually not be realizable.
data TotalityCounterexample ptrW =
  TotalityCounterexample
    (Integer, MCS.MacawBlockEndCase, Maybe (MM.MemSegmentOff ptrW, Text))
    (Integer, MCS.MacawBlockEndCase, Maybe (MM.MemSegmentOff ptrW, Text))


instance MM.MemWidth (MM.RegAddrWidth (MM.ArchReg arch)) => IsTraceNode '(sym,arch) "totalityce" where
  type TraceNodeType '(sym,arch) "totalityce" = TotalityCounterexample (MM.ArchAddrWidth arch)
  prettyNode () (TotalityCounterexample (oIP,oEnd,oInstr) (pIP,pEnd,pInstr)) = PP.vsep $
      ["Found extra exit while checking totality:"
      , PP.pretty (showHex oIP "") <+> PP.pretty (PPI.ppExitCase oEnd) <+> PP.pretty (show oInstr)
      , PP.pretty (showHex pIP "") <+> PP.pretty (PPI.ppExitCase pEnd) <+> PP.pretty (show pInstr)
      ]
  nodeTags = [(Summary, \_ _ -> "Not total") ]

data RegsCounterExample sym arch =
  RegsCounterExample 
    (MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym))
    (MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym))

prettyRegsCE ::
  (PA.ValidArch arch, PSo.ValidSym sym) =>
  RegsCounterExample sym arch -> PP.Doc a
prettyRegsCE (RegsCounterExample rsO rsP) = runIdentity $ do
  ps <- execWriterT $ do
    _ <- zipWithRegStatesM rsO rsP $ \r rO rP -> 
      case rO == rP of
        False | PA.Normal ppreg <- fmap PP.pretty (PA.displayRegister r) -> tell [ppreg] >> return rO
        _ -> return rO
    return ()
  return $ PP.braces $ PP.fillSep $ PP.punctuate "," ps

-- | An observable counterexample consists of a sequence of observable events
--   that differ in some way.  The first sequence is generated by the
--   original program, and the second is from the patched program.
--
--   Note that because of the overapproximation implied by the abstract domains, the
--   computed counterexamples may actually not be realizable.
data ObservableCounterexample sym arch =
  ObservableCounterexample
    (RegsCounterExample sym arch)
    [MT.MemEvent sym (MM.ArchAddrWidth arch)]
    [MT.MemEvent sym (MM.ArchAddrWidth arch)]

data ObservableCheckResult sym arch
  = ObservableCheckEq
  | ObservableCheckCounterexample
    (ObservableCounterexample sym arch)
  | ObservableCheckError String

instance (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "observable_result" where
  type TraceNodeType '(sym,arch) "observable_result" = ObservableCheckResult sym arch
  prettyNode () = \case
    ObservableCheckEq -> "Observably Equivalent"
    ObservableCheckCounterexample (ObservableCounterexample regsCE oSeq pSeq) -> PP.vsep $ 
       ["Observable Inequivalence Detected:"
       -- FIXME: this is useful but needs better presentation
       , "== Diverging Registers =="
       , prettyRegsCE regsCE
       , "== Original sequence =="
       ] ++ (map MT.prettyMemEvent oSeq) ++
       [ "== Patched sequence ==" ]
       ++ (map MT.prettyMemEvent pSeq)

    ObservableCheckError msg -> PP.vsep $
      [ "Error during observability check"
      , PP.pretty msg
      ]
  nodeTags =
    [ (tag, \() res -> case res of
                  ObservableCheckEq -> "Observably Equivalent"
                  ObservableCheckCounterexample{} -> "Observable Inequivalence Detected"
                  ObservableCheckError{} -> "Error during observability check")
      | tag <- [Simplified, Summary, JSONTrace]
    ]

groundObservableSequence ::
  (sym ~ W4.ExprBuilder t st fs, 1 <= ptrW) =>
  sym ->
  W4.GroundEvalFn t ->
  MT.MemTraceSeq sym ptrW ->
  IO [ MT.MemEvent sym ptrW ]
groundObservableSequence sym evalFn =
  concreteizeSymSequence (\p -> W4.groundEval evalFn p) (groundMemEvent sym evalFn)

groundMemEvent ::
  (sym ~ W4.ExprBuilder t st fs, 1 <= ptrW) =>
  sym ->
  W4.GroundEvalFn t ->
  MT.MemEvent sym ptrW ->
  IO (MT.MemEvent sym ptrW)
groundMemEvent sym evalFn (MT.MemOpEvent op) =
  MT.MemOpEvent <$> groundMemOp sym evalFn op
groundMemEvent sym evalFn (MT.SyscallEvent i x) =
  do i' <- MT.toMuxTree sym <$> groundMuxTree sym evalFn i
     x' <- W4.bvLit sym (W4.bvWidth x) =<< W4.groundEval evalFn x
     return (MT.SyscallEvent i' x')
groundMemEvent sym evalFn (MT.ExternalCallEvent nm xs) =
  do xs' <- TFC.traverseFC (\(MT.SymBV' x) ->
                              case W4.exprType x of
                                W4.BaseBVRepr w ->
                                  MT.SymBV' <$> (W4.groundEval evalFn x >>= W4.bvLit sym w)) xs
     return (MT.ExternalCallEvent nm xs')

groundMemOp ::
  (sym ~ W4.ExprBuilder t st fs, 1 <= ptrW) =>
  sym ->
  W4.GroundEvalFn t ->
  MT.MemOp sym ptrW ->
  IO (MT.MemOp sym ptrW)
groundMemOp sym evalFn (MT.MemOp ptr dir cond w val end) =
  do LeqProof <- return (leqMulPos (knownNat @8) w)
     ptr' <- CLM.concPtr sym (\x -> W4.groundEval evalFn x) ptr
     b <- W4.groundEval evalFn (MT.getCond sym cond)
     let cond' = if b then MT.Unconditional else MT.Conditional (W4.falsePred sym)
     val' <- CLM.concPtr sym (\x -> W4.groundEval evalFn x) val
     return (MT.MemOp ptr' dir cond' w val' end)

groundMuxTree ::
  (sym ~ W4.ExprBuilder t st fs) =>
  sym ->
  W4.GroundEvalFn t ->
  MT.MuxTree sym a ->
  IO a
groundMuxTree sym evalFn = MT.collapseMuxTree sym ite
  where
    ite p x y =
      do b <- W4.groundEval evalFn p
         if b then return x else return y