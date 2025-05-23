{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module Pate.Verification.StrongestPosts.CounterExample
  ( TotalityCounterexample(..)
  , ObservableCounterexample(..)
  , RegsCounterExample(..)
  , prettyRegsCE
  , ObservableCheckResult(..)
  , groundObservableSequence
  , groundMuxTree
  , groundMemEvent
  , ppTraceEvents
  , TraceEvents(..)
  , TraceEventsOne(..)
  , groundTraceEvent
  , groundTraceEventSequence
  , groundRegOp
  , TraceFootprint(..)
  , mkFootprint
  ) where


import           Data.Text (Text)
import           Numeric (showHex)
import qualified Data.Set as Set


import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.Memory.MemTrace as MT
import           Pate.TraceTree
import qualified Pate.Solver as PSo
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.PatchPair as PPa
import qualified Pate.Verification.Concretize as PVC
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
import qualified Lang.Crucible.Types as CT
import qualified Data.Parameterized.TraversableF as TF
import qualified What4.Concrete as W4
import qualified What4.SymSequence as W4

import Data.Functor.Const
import qualified Data.Parameterized.Map as MapF
import Data.Maybe (mapMaybe)
import qualified What4.JSON as W4S
import What4.JSON
import Pate.Equivalence (StatePostCondition)
import qualified Pate.Binary as PB
import GHC.Stack (HasCallStack)
import qualified Data.Aeson as JSON
import qualified Data.Text.Lazy.Encoding as Text
import qualified Data.Text.Encoding.Error as Text

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
      , PP.pretty (showHex oIP "") <+> PP.pretty (MCS.ppExitCase oEnd) <+> PP.pretty (show oInstr)
      , PP.pretty (showHex pIP "") <+> PP.pretty (MCS.ppExitCase pEnd) <+> PP.pretty (show pInstr)
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

obsResultSummary :: ObservableCheckResult sym arch -> String
obsResultSummary res = case res of
  ObservableCheckEq -> "Observably Equivalent"
  ObservableCheckCounterexample{} -> "Observable Inequivalence Detected"
  ObservableCheckError{} -> "Error during observability check"

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4Serializable sym (ObservableCounterexample sym arch) where
  w4Serialize r = w4SerializeString (show (ppObservableCounterexample r))

instance W4Serializable sym (ObservableCheckResult sym arch) where
  w4Serialize r = w4SerializeString (show (obsResultSummary r))

instance (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "observable_result" where
  type TraceNodeType '(sym,arch) "observable_result" = ObservableCheckResult sym arch
  prettyNode () = \case
    ObservableCheckEq -> "Observably Equivalent"
    ObservableCheckCounterexample ocex -> ppObservableCounterexample ocex 
    ObservableCheckError msg -> PP.vsep $
      [ "Error during observability check"
      , PP.pretty msg
      ]
  nodeTags =
    [ (tag, \() res -> PP.viaShow $ obsResultSummary res)
      | tag <- [Simplified, Summary]
    ]

ppObservableCounterexample ::
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  ObservableCounterexample sym arch ->
  PP.Doc a
ppObservableCounterexample (ObservableCounterexample regsCE oSeq pSeq) = PP.vsep $ 
  ["Observable Inequivalence Detected:"
  -- FIXME: this is useful but needs better presentation
  , "== Diverging Registers =="
  , prettyRegsCE regsCE
  , "== Original sequence =="
  ] ++ (map MT.prettyMemEvent oSeq) ++
  [ "== Patched sequence ==" ]
  ++ (map MT.prettyMemEvent pSeq)


instance (PA.ValidArch arch, PSo.ValidSym sym) => PP.Pretty (ObservableCounterexample sym arch) where
  pretty = ppObservableCounterexample

groundObservableSequence ::
  HasCallStack =>
  (sym ~ W4.ExprBuilder t st fs, 1 <= ptrW) =>
  MM.MemWidth ptrW =>
  sym ->
  W4.GroundEvalFn t ->
  MT.MemTraceSeq sym ptrW ->
  IO [ MT.MemEvent sym ptrW ]
groundObservableSequence sym evalFn =
  concreteizeSymSequence (\p -> W4.groundEval evalFn p) (groundMemEvent sym evalFn)

groundMemEvent ::
  HasCallStack =>
  (sym ~ W4.ExprBuilder t st fs, 1 <= ptrW) =>
  MM.MemWidth ptrW =>
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
groundMemEvent sym evalFn (MT.ExternalCallEventGen nm xs obs) = do
  xs' <- mapM (MT.groundExternalCallData sym evalFn) xs
  return (MT.ExternalCallEventGen nm xs' obs)

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

data TraceEvents sym arch =
  TraceEvents 
    { traceEvents :: PPa.PatchPair (TraceEventsOne sym arch)
    , preCond :: Some (StatePostCondition sym arch)
    , postCond :: Maybe (Some (StatePostCondition sym arch))
    }

data TraceEventsOne sym arch (bin :: PB.WhichBinary) = TraceEventsOne
  { initialRegs :: MT.RegOp sym arch
  , traceEventGroups :: [TraceEventGroup sym arch]
  }

-- | Partial symbolic spec for the initial state
data TraceFootprint sym arch = TraceFootprint
  { fpInitialRegs :: MT.RegOp sym arch 
  , fpMem :: [(MM.ArchSegmentOff arch, (MT.MemOp sym (MM.ArchAddrWidth arch)))]
  }

instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "trace_footprint" where
  type TraceNodeType '(sym,arch) "trace_footprint" = TraceFootprint sym arch
  type TraceNodeLabel "trace_footprint" = JSON.Value
  prettyNode json _ = PP.pretty $ Text.decodeUtf8With Text.lenientDecode $ JSON.encode json
  nodeTags = mkTags @'(sym,arch) @"trace_footprint" ["debug"]
  jsonNode _ json _ = return json

mkFootprint ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  sym ->
  MT.RegOp sym arch ->
  SymSequence sym (MT.TraceEvent sym arch) -> 
  IO (TraceFootprint sym arch)
mkFootprint sym init_regs s = do
  init_mems <- W4.concatSymSequence sym go (\_ a b -> return $ a ++ b) (\a b -> return $ a ++ b) [] s
  return $ TraceFootprint init_regs (Set.toList (Set.fromList init_mems))
  where
    go :: MT.TraceEvent sym arch -> IO [(MM.ArchSegmentOff arch, (MT.MemOp sym (MM.ArchAddrWidth arch)))]
    go = \case
      MT.TraceMemEvent instr (MT.MemOpEvent mop@(MT.MemOp ptr _ _ _ _ _))
        | [(Just (instr1, _), _)] <- MT.viewMuxTree instr
        , CLM.LLVMPointer reg off <- ptr
        , Just{} <- W4.asNat reg
        , Just{} <- W4.asConcrete off
        -> return $ [(instr1, mop)]
      _ -> return []

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (TraceFootprint sym arch) where
  w4Serialize fp = W4S.object [  "fp_mem" .= fpMem fp, "fp_initial_regs" .= fpInitialRegs fp]

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (TraceEvents sym arch) where
  w4Serialize (TraceEvents p pre post) = do
    trace_pair <- PB.w4SerializePair p $ \(TraceEventsOne rop evs) -> 
      W4S.object [ "initial_regs" .= rop, "events" .= evs]
    W4S.object [ "precondition" .= pre, "postcondition" .= post, "traces" .= trace_pair ]

data TraceEventGroup sym arch =
  TraceEventGroup (Maybe (MM.ArchSegmentOff arch)) [MT.TraceEvent sym arch]

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (TraceEventGroup sym arch) where
  w4Serialize (TraceEventGroup mi evs) =
    W4S.object [ "instruction_addr" .= mi, "events" .= evs]

ppRegOp :: forall sym arch ann. (PA.ValidArch arch, PSo.ValidSym sym) => MT.RegOp sym arch -> [PP.Doc ann]
ppRegOp (MT.RegOp m) = mapMaybe (\(MapF.Pair r v) -> 
  case PA.displayRegister r of
  PA.Normal pr -> Just $ PP.pretty pr <+> "<-" <+> (prettyVal v)
  _ | Just Refl <- testEquality MM.ip_reg r -> Just $ "pc" <+> "<-" <+> (prettyVal v)
  _ -> Nothing) (MapF.toList m)
  where
    prettyVal :: forall tp. PSR.MacawRegEntry sym tp -> PP.Doc ann
    prettyVal r = case PSR.macawRegRepr r of
      CLM.LLVMPointerRepr{} -> MT.ppPtr' (PSR.macawRegValue r)
      _ -> PP.pretty $ show r


ppTraceEvent :: (PA.ValidArch arch, PSo.ValidSym sym) => MT.TraceEvent sym arch -> [PP.Doc ann]
ppTraceEvent ev = case ev of
  MT.RegOpEvent _ rop -> ppRegOp rop
  MT.TraceMemEvent _ mev -> [MT.prettyMemEvent mev]

ppTraceEventGroup ::
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  TraceEventGroup sym arch ->
  Maybe (PP.Doc a)  
ppTraceEventGroup evg = case evg of
  (TraceEventGroup (Just addr) evs) -> Just $ case concat (map ppTraceEvent evs) of
    [] -> PP.parens (PP.viaShow addr)
    [pretty_ev] -> PP.parens (PP.viaShow addr) <+> pretty_ev
    pretty_evs -> PP.parens (PP.viaShow addr) <> PP.line <> PP.indent 2 (PP.vsep pretty_evs)
  (TraceEventGroup Nothing evs) -> case concat (map ppTraceEvent evs) of
    [] -> Nothing
    [pretty_ev] -> Just pretty_ev
    pretty_evs -> Just $ PP.indent 2 (PP.vsep pretty_evs)

instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "trace_events" where
  type TraceNodeType '(sym,arch) "trace_events" = TraceEvents sym arch
  prettyNode () = ppTraceEvents
  nodeTags = 
    map (\tag -> (tag, \_ (TraceEvents evs _ _) -> 
      "Event Trace:" PP.<+> PPa.ppPatchPair' (\(TraceEventsOne _init_regs s) ->
        ppTraceEventSummary s) evs))
    [Summary, Simplified]
  jsonNode sym () v = W4S.w4ToJSON sym v

ppTraceEventSummary ::
  forall sym arch a.
  PA.ValidArch arch =>
  [TraceEventGroup sym arch] -> 
  PP.Doc a
ppTraceEventSummary [] = ""
ppTraceEventSummary tr@(t:tr_tail) = case (t, last tr) of
  (TraceEventGroup Nothing _, _) -> ppTraceEventSummary tr_tail
  (TraceEventGroup (Just addr_head) _, TraceEventGroup (Just addr_last) _) ->
    PP.viaShow addr_head PP.<+> ".." <+> PP.viaShow addr_last
  _ -> ""

ppTraceEvents ::
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  TraceEvents sym arch ->
  PP.Doc a
ppTraceEvents (TraceEvents tr _ _) = case tr of
  PPa.PatchPairOriginal (TraceEventsOne init_regsO trO) ->
    PP.vsep $ [ "== Initial Registers ==" ] ++ ppRegOp init_regsO ++ mapMaybe ppTraceEventGroup trO
  PPa.PatchPairPatched (TraceEventsOne init_regsP trP) ->
    PP.vsep $ [ "== Initial Registers ==" ] ++ ppRegOp init_regsP ++ mapMaybe ppTraceEventGroup trP
  PPa.PatchPair (TraceEventsOne init_regsO trO) (TraceEventsOne init_regsP trP)-> PP.vsep $
       [ "== Initial Original Registers ==" ]
    ++ ppRegOp init_regsO
    ++ [ "== Original sequence ==" ]
    ++ mapMaybe ppTraceEventGroup trO
    ++ [ "== Initial Patched Registers ==" ]
    ++ ppRegOp init_regsP
    ++ [ "== Patched sequence ==" ]
    ++ mapMaybe ppTraceEventGroup trP

instance (PA.ValidArch arch, PSo.ValidSym sym) => PP.Pretty (TraceEvents sym arch) where
  pretty = ppTraceEvents

groundRegOp ::
  (sym ~ W4.ExprBuilder t st fs) =>
  1 <= MM.ArchAddrWidth arch =>
  sym ->
  W4.GroundEvalFn t ->
  MT.RegOp sym arch ->
  IO (MT.RegOp sym arch)
groundRegOp sym evalFn (MT.RegOp m) = 
  MT.RegOp <$> TF.traverseF (groundRegEntry sym evalFn) m

groundRegEntry :: 
  (sym ~ W4.ExprBuilder t st fs) =>
  sym ->
  W4.GroundEvalFn t ->
  PSR.MacawRegEntry sym tp ->
  IO (PSR.MacawRegEntry sym tp)  
groundRegEntry sym evalFn (PSR.MacawRegEntry repr v) = PSR.MacawRegEntry repr <$> case repr of
  CLM.LLVMPointerRepr{} -> CLM.concPtr sym (\x -> W4.groundEval evalFn x) v
  CT.BoolRepr -> W4.groundEval evalFn v >>= (W4.concreteToSym sym . W4.ConcreteBool)
  _ -> return v

groundTraceEvent ::
  (sym ~ W4.ExprBuilder t st fs) =>
  1 <= MM.ArchAddrWidth arch =>
  MM.MemWidth (MM.ArchAddrWidth arch) =>
  sym ->
  W4.GroundEvalFn t ->
  MT.TraceEvent sym arch ->
  IO (MT.TraceEvent sym arch)
groundTraceEvent sym evalFn = \case
  MT.RegOpEvent i rop -> MT.RegOpEvent <$> (MT.toMuxTree sym <$> groundMuxTree sym evalFn i) <*> groundRegOp sym evalFn rop
  MT.TraceMemEvent i mop -> MT.TraceMemEvent <$> (MT.toMuxTree sym <$> groundMuxTree sym evalFn i)  <*> groundMemEvent sym evalFn mop


dropPCReg :: PA.ValidArch arch => MT.TraceEvent sym arch -> MT.TraceEvent sym arch
dropPCReg = \case
  MT.RegOpEvent i (MT.RegOp m) -> MT.RegOpEvent i (MT.RegOp (MapF.delete (MM.ip_reg) m))
  x -> x

-- NB: events are reversed in the ground list so they appear in the natural order 
-- (i.e. first event is the head of the list)
groundTraceEventSequence ::
  forall sym arch t st fs. 
  (sym ~ W4.ExprBuilder t st fs) =>
  PA.ValidArch arch =>
  sym ->
  W4.GroundEvalFn t ->
  SymSequence sym (MT.TraceEvent sym arch) ->
  IO [TraceEventGroup sym arch]
groundTraceEventSequence sym evalFn s = do
  l <- reverse <$> concreteizeSymSequence (\p -> W4.groundEval evalFn p) return s
  go Nothing [] l
  where
    go :: Maybe (MM.ArchSegmentOff arch) -> [MT.TraceEvent sym arch] -> [MT.TraceEvent sym arch] -> IO [TraceEventGroup sym arch]
    go last_instr ground_evs [] = return $ [TraceEventGroup last_instr (reverse ground_evs)]
    go last_instr ground_evs (e1 : evs) = do
      e1_instr <- fmap fst <$> groundMuxTree sym evalFn (MT.traceInstr e1)
      e1_ground <- groundTraceEvent sym evalFn e1
      case last_instr == e1_instr of
        True -> go last_instr (e1_ground : ground_evs) evs
        False -> do
          evs' <- go e1_instr [e1_ground] evs
          case ground_evs of
            [] -> return evs'
            _ -> do
              let ground_evs' = case evs' of
                    (_ : _) | Just{} <- e1_instr -> map dropPCReg ground_evs
                    _ -> ground_evs
              return $ (TraceEventGroup last_instr (reverse ground_evs') : evs')
