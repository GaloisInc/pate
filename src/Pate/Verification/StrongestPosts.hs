{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module Pate.Verification.StrongestPosts
  ( pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.) )
import           Control.Monad (foldM, forM)
import           Control.Monad.IO.Class
import           System.IO as IO
import           Control.Monad.Reader (asks)
import           Control.Monad.Except (runExceptT, catchError)
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import           Data.Proxy
import           Data.Functor.Const
import           Data.IORef ( IORef, newIORef, readIORef, modifyIORef )

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PPRT

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.Nonce

import qualified What4.Expr as W4
import qualified What4.Interface as W4
import           What4.SatResult (SatResult(..))

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator.RegValue as LCS
import           Lang.Crucible.Simulator.SymSequence
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.AbsDomain.AbsState as MAS

import qualified Pate.Abort as PAb
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Config as PCfg
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Event as PE
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof.Instances as PPI
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Register.Traversal as PRt
import           Pate.TraceTree
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy

import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node ( GraphNode(..), NodeEntry, mkNodeEntry, mkNodeReturn, nodeBlocks, addContext )
import           Pate.Verification.Widening
import qualified Pate.Verification.AbstractDomain as PAD

-- Overall module notes/thoughts
--
-- Currently, we are making rather limited use
-- of online solving. We might be able to get some
-- amount of additional speedup by sharing additional
-- context between tasks (e.g., the preconditions are
-- basically the same for all the subtasks like
-- checking observables and following exits).
--
-- We could consider using concurrency to, e.g., visit
-- several graph nodes at the same time in parallel. We
-- would certainly want to find a more clever way to choose
-- what nodes to visit if we go in that direction, as otherwise
-- we risk wasting a lot of work.  We would also need to be a
-- lot more careful about deciding how to schedule/commit updates
-- to the pair graph.
--
-- Currently, this analysis is context-insensitive. It would be
-- not terribly difficult, I think, to add additional information
-- to the graph nodes to capture some contextual information
-- (e.g., call stack). In those cases, some returns would have
-- statically known return points and would hopefully result in more
-- precise analysis. This has the potential to be quite expensive,
-- of course.

runVerificationLoop ::
  forall sym arch.
  PA.ValidArch arch =>
  EquivEnv sym arch ->
  -- | A list of block pairs to test for equivalence. They must be the entry points of functions.
  [PPa.FunPair arch] ->
  IO (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
runVerificationLoop env pPairs = do
  (result, trees) <- runEquivM env doVerify
  withValidEnv @(IO ()) env $ do
    let p = ppFullTraceTree [Summary] trees
    let s = PP.layoutPretty PP.defaultLayoutOptions p
    PPRT.renderIO IO.stdout s
  case result of
    Left err -> return (PE.Errored err, mempty)
    Right r  -> return r
 where
   doVerify :: EquivM sym arch (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
   doVerify =
     do pg0 <- initializePairGraph pPairs
        result <- catchError (do
          -- Do the main work of computing the dataflow fixpoint
          pg <- pairGraphComputeFixpoint pg0
          -- Report a summary of any errors we found during analysis
          reportAnalysisErrors (envLogger env) pg
          pairGraphComputeVerdict pg) (pure . PE.Errored)

        emitEvent (PE.StrongestPostOverallResult result)

        -- TODO, does reporting these kind of statistics make sense for this verification method?
        -- Currently, we only really do this to make the types fit at the call site.
        statVar <- asks envStatistics
        stats <- liftIO $ MVar.readMVar statVar

        return (result, stats)


-- | Execute the forward dataflow fixpoint algorithm.
--   Visit nodes and compute abstract domains until we propagate information
--   to all reachable positions in the program graph and we reach stability,
--   or until we run out of gas.
--
--   TODO, could also imagine putting timeouts/compute time limits here.
pairGraphComputeFixpoint ::
  forall sym arch. PairGraph sym arch -> EquivM sym arch (PairGraph sym arch)
pairGraphComputeFixpoint gr_outer =
  withSubTraces $ do
    let go (gr :: PairGraph sym arch) = case chooseWorkItem gr of
          Nothing -> return gr
          Just (gr', nd, preSpec) -> do
            gr'' <- subTrace @"node" nd $ startTimer $ do
              PS.viewSpec preSpec $ \scope d -> do
                emitTraceLabel @"domain" PAD.Predomain (Some d)
                withAssumptionSet (PS.scopeAsm scope) $ do
                  gr'' <- visitNode scope nd d gr'
                  emitEvent $ PE.VisitedNode nd
                  return gr''
            go gr''
    go gr_outer


-- | For a given 'PSR.MacawRegEntry' (representing the initial state of a register)
-- and a corresponding 'MAS.AbsValue' (its initial abstract value according to Macaw),
-- compute an 'PAS.AssumptionSet' that assumes they correspond.
-- Currently the only case that is covered is when macaw decides that the register
-- is holding a stack offset (i.e. a 'MAS.StackOffsetAbsVal'). In this case we
-- compute the expected value for the register by adding the stack offset to
-- the stack base of the given 'PS.SimVars'.
-- This is necessary to ensure that we can successfully re-scope any references
-- to these registers in 'Pate.Verification.Widening.abstractOverVars'
absValueToAsm ::
  forall sym arch v bin tp.
  PS.SimVars sym arch v bin ->
  PSR.MacawRegEntry sym tp ->
  MAS.AbsValue (MM.ArchAddrWidth arch) tp ->
  EquivM sym arch (PAS.AssumptionSet sym)
absValueToAsm vars regEntry val = withSym $ \sym -> case val of
  -- FIXME: check the MemAddr here to make sure we only use
  -- stack offsets from this frame
  MAS.StackOffsetAbsVal _memAddr slot -> do
    CLM.LLVMPointer region off <- return $ PSR.macawRegValue regEntry
    stackRegion <- asks (PMC.stackRegion . envCtx)
    -- the region of this value must be the stack region
    let bindRegion = PAS.natBinding region stackRegion

    let w = MM.memWidthNatRepr @(MM.ArchAddrWidth arch)
    slotBV <- liftIO $ W4.bvLit sym w (BV.mkBV w (fromIntegral slot))
    let sb = PS.unSE $ PS.unSB $ PS.simStackBase $ PS.simVarState vars
    off' <- liftIO $ W4.bvAdd sym sb slotBV
    -- the offset of this value must be frame + slot
    let bindOffSet = PAS.exprBinding off off'
    return $ bindRegion <> bindOffSet
  _ -> return mempty

-- | Returns an 'PS.AssumptionSet' that assumes the initial abstract block state
-- from Macaw ('MAS.AbsBlockState') corresponds to the given 'PB.ConcreteBlock'.
-- Specifically each register is assumed to agree with the corresponding 'MAS.AbsValue'.
-- TODO: At the moment this is limited to identifying stack offsets, but in general
-- we could lift all of the abstract value information from Macaw.
validAbsValues ::
  forall sym arch v bin.
  PBi.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  PS.SimVars sym arch v bin ->
  EquivM sym arch (PAS.AssumptionSet sym)
validAbsValues block var = do
  absBlockState <- PD.getAbsDomain block
  let
    absRegs = absBlockState ^. MAS.absRegState
    regs = PS.simRegs $ PS.simVarState var
  fmap PRt.collapse $ PRt.zipWithRegStatesM regs absRegs $ \_ re av ->
    Const <$> absValueToAsm var re av

-- | Perform the work of propagating abstract domain information through
--   a single program "slice". First we check for equivalence of observables,
--   then we check the totality of the computed exits, then we update any
--   function return nodes, and finally we follow all the exit nodes
--   that were computed via "discoverPairs." (The specific order in which
--   we perform these steps should not be very important).
--
--   When we visit a "ReturnNode", we need to propagate abstract domain
--   information directly to the return points of of the call sites of
--   the given function, which are recorded in the pair graph
--   "return vectors."
visitNode :: forall sym arch v.
  PS.SimScope sym arch v ->
  GraphNode arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)

visitNode scope (GraphNode node@(nodeBlocks -> bPair)) d gr0 = withPair bPair $  do
  let vars = PS.scopeVars scope
  validInit <- PVV.validInitState (Just bPair) (PS.simVarState $ PPa.pOriginal vars) (PS.simVarState $ PPa.pPatched vars)
  validAbs <- PPa.catBins $ \get -> validAbsValues (get bPair) (get vars)
  withAssumptionSet (validInit <> validAbs) $
    do -- do the symbolic simulation
       bundle' <- mkSimBundle bPair vars d
       emitTrace @"bundle" (Some bundle')
       withPredomain bundle' d $ do
         -- simplify the bundle under the domain assumptions
         bundle <- applyCurrentAsms bundle'
         traceBundle bundle $ "visitNode:  incoming domain\n" ++ (show (PAD.ppAbstractDomain (\_ -> "") d))
         
  {-     traceBundle bundle $ unlines
         [ "== SP result =="
         , show (MM.getBoundValue (MM.sp_reg @(MM.ArchReg arch))
              (PS.simRegs (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))))
         , show (MM.getBoundValue (MM.sp_reg @(MM.ArchReg arch))
              (PS.simRegs (PS.simOutState (PPa.pPatched (PS.simOut bundle)))))
         ] -}

         -- Compute exit pairs
         traceBundle bundle $ "Discovering exit pairs from " ++ (show bPair)
         -- TODO, manifest errors here?
         exitPairs <- PD.discoverPairs bundle
         traceBundle bundle $ (show (length exitPairs) ++ " pairs found!")


         gr1 <- checkObservables node bundle d gr0

         gr2 <- checkTotality node bundle d exitPairs gr1

         gr3 <- updateReturnNode scope node bundle d gr2

         -- Follow all the exit pairs we found
         withSubTraces $
           foldM (\x y@(_,tgt) -> subTrace @"blocktarget" tgt $ followExit scope bundle node d x y) gr3 (zip [0 ..] exitPairs)


visitNode scope (ReturnNode fPair) d gr0 =
  -- propagate the abstract domain of the return node to
  -- all of the known call sites of this function.
  foldM processReturn gr0 (getReturnVectors gr0 fPair)

 where
   -- Here, we're using a bit of a trick to propagate abstract domain information to call sites.
   -- We are making up a "dummy" simulation bundle that basically just represents a no-op, and
   -- using the ordinary widening machinery.

   processReturn gr node@(nodeBlocks -> ret) = withPair ret $ do
     let vars = PS.scopeVars scope
     validState <- PVV.validInitState (Just ret) (PS.simVarState (PPa.pOriginal vars)) (PS.simVarState (PPa.pPatched vars))
     withAssumptionSet validState $
       do (asm, bundle) <- returnSiteBundle vars d ret
          withAssumptionSet asm $ withPredomain bundle d $ do
            traceBundle bundle "Processing return edge"
    --        traceBundle bundle "== bundle asm =="
    --        traceBundle bundle (show (W4.printSymExpr asm))
            widenAlongEdge scope bundle (ReturnNode fPair) d gr (GraphNode node)


-- | Construct a "dummy" simulation bundle that basically just
--   immediately returns the prestate as the poststate.
--   This is used to compute widenings that propagate abstract domain
--   information from function return nodes to the actual return sites.
--   The only state update that occurs is that a fresh variable is created
--   to represent the stack base in the output state.
--   The returned 'PAS.AssumptionSet' associates the internal stack base
--   from the callee (i.e. in 'SimInput') with the stack
--   pointer of the caller (i.e. in 'SimOutput').
--   This effectively re-phrases the resulting domain from the
--   function call with respect to the specific call site that we are
--   returning, and allows us to properly contextualize any resulting inequalities
--   with respect to what is visible in the callers stack frame.
returnSiteBundle :: forall sym arch v.
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  AbstractDomain sym arch v ->
  PPa.BlockPair arch {- ^ block pair being returned to -} ->
  EquivM sym arch (PAS.AssumptionSet sym, SimBundle sym arch v)
returnSiteBundle vars _preD pPair = withSym $ \sym -> do
  simIn_ <- PPa.forBins $ \get -> do
    absSt <- PD.getAbsDomain (get pPair)
    return $ PS.SimInput (PS.simVarState (get vars)) (get pPair) absSt
  blockEndVal <- liftIO (MCS.initBlockEnd (Proxy @arch) sym)

  simOut_ <- PPa.forBins $ \get -> do
    let inSt = PS.simInState $ get simIn_
    postFrame <- liftIO $ PS.freshStackBase sym (Proxy @arch)
    let postSt = inSt { PS.simStackBase = postFrame }
    return $ PS.SimOutput postSt blockEndVal

  bundle <- applyCurrentAsms $ SimBundle simIn_ simOut_

  -- assert that, upon return, the frame of the callee is the same as its
  -- stack pointer (i.e. interpret the domain as if all of its values were
  -- computed as offsets starting from the call site)
  asms <- PPa.catBins $ \get -> do
    let
      inSt = PS.simInState $ get simIn_
      initFrame = PS.simStackBase inSt
      outVars = get (PS.bundleOutVars bundle)
      CLM.LLVMPointer _ sp_pre = PSR.macawRegValue $ PS.simSP inSt
    vAbs <- validAbsValues (get pPair) outVars
    return $ vAbs <> (PAS.exprBinding (PS.unSE $ PS.unSB $ initFrame) sp_pre)

  return (asms, bundle)


-- | Run the given function a context where the
-- given abstract domain is assumed to hold on the pre-state of the given
-- bundle.
withPredomain ::
  forall sym arch v a.
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch a ->
  EquivM sym arch a
withPredomain bundle preD f = withSym $ \sym -> do
  eqCtx <- equivalenceContext
  precond <- liftIO $ PAD.absDomainToPrecond sym eqCtx bundle preD
  withAssumptionSet precond $ f

data ObservableCheckResult sym ptrW
  = ObservableCheckEq
  | ObservableCheckCounterexample (ObservableCounterexample sym ptrW)
  | ObservableCheckError String

checkObservables :: forall sym arch v.
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkObservables bPair bundle preD gr =
  considerObservableEvent gr bPair $
    do res <- doCheckObservables bundle preD
       case res of
         ObservableCheckEq ->
           do traceBundle bundle "Observables agree"
              return (Nothing, gr)
         ObservableCheckError msg ->
           do let msg' = ("Error checking observables: " ++ msg)
              err <- emitError (PEE.ObservabilityError msg')
              return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) err)
         ObservableCheckCounterexample cex@(ObservableCounterexample oSeq pSeq) -> do
           do traceBundle bundle ("Obserables disagree!")
              traceBundle bundle ("== Original sequence ==")
              traceBundle bundle (show (vcat (map MT.prettyMemEvent oSeq)))
              traceBundle bundle ("== Patched sequence ==")
              traceBundle bundle (show (vcat (map MT.prettyMemEvent pSeq)))
              return (Just cex, gr)

doCheckObservables :: forall sym arch v.
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (ObservableCheckResult sym (MM.ArchAddrWidth arch))
doCheckObservables bundle _preD =
  withSym $ \sym ->
    do let oMem = PS.simMem (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
       let pMem = PS.simMem (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))

       stackRegion <- asks (PMC.stackRegion . envCtx)

       -- Grab the specified areas of observable memory
       obsMem <- asks (PMC.observableMemory . envCtx)

       -- test if the memory operation overlaps with one of the observable regions
       let filterObservableMemOps op@(MT.MemOp (CLM.LLVMPointer blk _off) _dir _cond _w _val _end) =
              do notStk <- W4.notPred sym =<< W4.natEq sym blk stackRegion
                 inRng <- sequence
                           [ MT.memOpOverlapsRegion sym op addr len
                           | (addr, len) <- obsMem
                           ]
                 inRng' <- foldM (W4.orPred sym) (W4.falsePred sym) inRng
                 W4.andPred sym notStk inRng'

       -- This filtering function selects out the memory operations that are writes to
       -- to non-stack regions to treat them as observable.
{-
       let filterHeapWrites (MT.MemOp (CLM.LLVMPointer blk _off) MT.Write _cond _w _val _end) =
             W4.notPred sym =<< W4.natEq sym blk stackRegion
           filterHeapWrites _ = return (W4.falsePred sym)
-}

       oSeq <- liftIO (MT.observableEvents sym filterObservableMemOps oMem)
       pSeq <- liftIO (MT.observableEvents sym filterObservableMemOps pMem)

{-
       traceBundle bundle $ unlines
         [ "== original event trace =="
         , show (MT.prettyMemTraceSeq oSeq)
         ]

       traceBundle bundle $ unlines
         [ "== patched event trace =="
         , show (MT.prettyMemTraceSeq pSeq)
         ]
-}

       eqSeq <- equivalentSequences oSeq pSeq

{-
       traceBundle bundle $ unlines
         [ "== Observable Eq precond =="
         , show (W4.printSymExpr precond)
         ]

       traceBundle bundle $ unlines
         [ "== Observable Eq condition =="
         , show (W4.printSymExpr eqSeq)
         ]
-}
       not_goal <- liftIO $ W4.notPred sym eqSeq
       goalSat "checkObservableSequences" not_goal $ \res -> case res of
         Unsat _ -> return ObservableCheckEq
         Unknown -> return (ObservableCheckError "UNKNOWN result when checking observable sequences")
         Sat evalFn' -> withGroundEvalFn evalFn' $ \evalFn -> do
           -- NB, observable sequences are stored in reverse order, so we reverse them here to
           -- display the counterexample in a more natural program order
           oSeq' <- reverse <$> groundObservableSequence sym evalFn oSeq -- (MT.memSeq oMem)
           pSeq' <- reverse <$> groundObservableSequence sym evalFn pSeq -- (MT.memSeq pMem)
           return (ObservableCheckCounterexample (ObservableCounterexample oSeq' pSeq'))

-- | Right now, this requires the pointer and written value to be exactly equal.
--   At some point, we may want to relax this in some way, but it's not immediately
--   clear how.
eqMemOp :: forall sym ptrW.
  (LCB.IsSymInterface sym, 1 <= ptrW) =>
  sym ->
  MT.MemOp sym ptrW ->
  MT.MemOp sym ptrW ->
  IO (W4.Pred sym)
eqMemOp sym (MT.MemOp xptr xdir xcond xw xval xend) (MT.MemOp yptr ydir ycond yw yval yend)
  | Just Refl <- testEquality xw yw
  , Just Refl <- testEquality (CLM.ptrWidth xval) (CLM.ptrWidth yval)
  , Just LeqProof <- isPosNat (CLM.ptrWidth xval)
  , xdir == ydir
  , xend == yend
  = do peq <- CLM.ptrEq sym (CLM.ptrWidth xptr) xptr yptr
       veq <- CLM.ptrEq sym (CLM.ptrWidth xval) xval yval
       ceq <- W4.eqPred sym (MT.getCond sym xcond) (MT.getCond sym ycond)
       W4.andPred sym peq =<< W4.andPred sym veq ceq

  | otherwise = return (W4.falsePred sym)


data SeqPairCache a b = SeqPairCache (IORef (Map.Map (Maybe (Nonce GlobalNonceGenerator a), Maybe (Nonce GlobalNonceGenerator a)) b))

newSeqPairCache :: IO (SeqPairCache a b)
newSeqPairCache = SeqPairCache <$> newIORef Map.empty

-- TODO: clagged from SymSequence module
symSequenceNonce :: SymSequence sym a -> Maybe (Nonce GlobalNonceGenerator a)
symSequenceNonce SymSequenceNil = Nothing
symSequenceNonce (SymSequenceCons n _ _ ) = Just n
symSequenceNonce (SymSequenceAppend n _ _) = Just n
symSequenceNonce (SymSequenceMerge n _ _ _) = Just n

evalWithPairCache :: MonadIO m =>
  SeqPairCache a b ->
  SymSequence sym a ->
  SymSequence sym a ->
  m b ->
  m b
evalWithPairCache (SeqPairCache ref) seq1 seq2 f = do
  m <- liftIO (readIORef ref)
  let k = (symSequenceNonce seq1, symSequenceNonce seq2)
  case Map.lookup k m of
    Just v -> return v
    Nothing -> do
      v <- f
      liftIO (modifyIORef ref (Map.insert k v))
      return v

-- TODO, this procedure can be exponential in the worst case,
-- because of the way we are splitting along merges.
--
-- It might be possible to do this in a better way, but
-- it's pretty tricky.
equivalentSequences :: forall sym arch ptrW.
  (1 <= ptrW) =>
  MM.MemWidth ptrW =>
  SymSequence sym (MT.MemEvent sym ptrW) ->
  SymSequence sym (MT.MemEvent sym ptrW) ->
  EquivM sym arch (W4.Pred sym)
equivalentSequences seq1 seq2 = withSym $ \sym -> do
  cache <- liftIO newSeqPairCache
  equivalentSequences' sym cache seq1 seq2

equivalentSequences' :: forall sym arch ptrW.
  (1 <= ptrW) =>
  MM.MemWidth ptrW =>
  sym ->
  SeqPairCache (MT.MemEvent sym ptrW) (W4.Pred sym) ->
  SymSequence sym (MT.MemEvent sym ptrW) ->
  SymSequence sym (MT.MemEvent sym ptrW) ->
  EquivM sym arch (W4.Pred sym)
equivalentSequences' sym cache = \xs ys -> loop [xs] [ys]
 where
  eqEvent :: MT.MemEvent sym ptrW -> MT.MemEvent sym ptrW -> EquivM sym arch (W4.Pred sym)

  eqEvent (MT.MemOpEvent xop) (MT.MemOpEvent yop) = liftIO $ eqMemOp sym xop yop

  eqEvent (MT.SyscallEvent _ x) (MT.SyscallEvent _ y) =
     case testEquality (W4.bvWidth x) (W4.bvWidth y) of
       Just Refl | Just W4.LeqProof <- W4.isPosNat (W4.bvWidth x) ->
         liftIO $ W4.bvEq sym x y
       _ -> return (W4.falsePred sym)

  eqEvent MT.MemOpEvent{} MT.SyscallEvent{} = return (W4.falsePred sym)
  eqEvent MT.SyscallEvent{} MT.MemOpEvent{} = return (W4.falsePred sym)

  -- The arguments to this loop are lists of SymSeqence values, which
  -- are basically a stack of list segments.
  -- The lists are used to manage append nodes, which get pushed onto the
  -- top of the stack when encountered.  This potentially loses sharing,
  -- but is pretty tricky to do better.
  loop ::
    [SymSequence sym (MT.MemEvent sym ptrW)] ->
    [SymSequence sym (MT.MemEvent sym ptrW)] ->
    EquivM sym arch (W4.Pred sym)
  loop seqs1 seqs2 = case (seqs1, seqs2) of
    -- cache the special case when the stacks are both a single sequence
    (seq1:[], seq2:[]) -> evalWithPairCache cache seq1 seq2 $ loop' seqs1 seqs2
    _ -> loop' seqs1 seqs2

  loop' ::
    [SymSequence sym (MT.MemEvent sym ptrW)] ->
    [SymSequence sym (MT.MemEvent sym ptrW)] ->
    EquivM sym arch (W4.Pred sym)
  -- nil/nil case, equal sequences
  loop' [] [] = return (W4.truePred sym)

  -- nil/cons and cons/nil cases, unequal sequences
  loop' [] (SymSequenceCons{}:_) = return (W4.falsePred sym)
  loop' (SymSequenceCons{}:_) [] = return (W4.falsePred sym)

  -- just pop empty sequences off the top of the stack
  loop' (SymSequenceNil:xs) ys = loop xs ys
  loop' xs (SymSequenceNil:ys) = loop xs ys

  -- push appended sequences onto the stack
  loop' (SymSequenceAppend _ xs1 xs2:xs) ys = loop (xs1:xs2:xs) ys
  loop' xs (SymSequenceAppend _ ys1 ys2:ys) = loop xs (ys1:ys2:ys)

  -- special case, both sequences split on the same predicate
  loop' (SymSequenceMerge _ px xs1 xs2:xs) ys_outer@(SymSequenceMerge _ py ys1 ys2:ys) =
    do goalTimeout <- asks (PCfg.cfgGoalTimeout . envConfig)
       p_eq <- liftIO $ W4.isEq sym px py
       (isPredTrue' goalTimeout p_eq) >>= \case
         True -> do
           eq1 <- loop (xs1:xs) (ys1:ys)
           eq2 <- loop (xs2:xs) (ys2:ys)
           liftIO $ W4.itePred sym px eq1 eq2
         False -> do
           -- split along the left stack
           eq1 <- loop (xs1:xs) ys_outer
           eq2 <- loop (xs2:xs) ys_outer
           liftIO $ W4.itePred sym px eq1 eq2

  -- split along merges on the top of the left stack
  loop' (SymSequenceMerge _ p xs1 xs2:xs) ys =
    do eq1 <- loop (xs1:xs) ys
       eq2 <- loop (xs2:xs) ys
       liftIO $ W4.itePred sym p eq1 eq2

  -- split along merges on the top of the right stack
  loop' xs (SymSequenceMerge _ p ys1 ys2:ys) =
    do eq1 <- loop xs (ys1:ys)
       eq2 <- loop xs (ys2:ys)
       liftIO $ W4.itePred sym p eq1 eq2

  -- cons/cons case.  Compare the heads and compare the tails
  loop' (SymSequenceCons _ x xs1:xs) (SymSequenceCons _ y ys1:ys) =
    do eq1 <- eqEvent x y
       eq2 <- loop (xs1:xs) (ys1:ys)
       liftIO $ W4.andPred sym eq1 eq2



checkTotality :: forall sym arch v.
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkTotality bPair bundle preD exits gr =
  considerDesyncEvent gr bPair $
    do tot <- doCheckTotality bundle preD exits
       case tot of
         CasesTotal ->
           do traceBundle bundle "Totality check succeeded."
              return (Nothing, gr)
         TotalityCheckingError msg ->
           do let msg' = ("Error while checking totality! " ++ msg)
              err <- emitError (PEE.TotalityError msg')
              return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) err)
         TotalityCheckCounterexample cex@(TotalityCounterexample (oIP,oEnd,oInstr) (pIP,pEnd,pInstr)) ->
           do traceBundle bundle $ unlines
                ["Found extra exit while checking totality:"
                , showHex oIP "" ++ " " ++ PPI.ppExitCase oEnd ++ " " ++ show oInstr
                , showHex pIP "" ++ " " ++ PPI.ppExitCase pEnd ++ " " ++ show pInstr
                ]
              return (Just cex, gr)

data TotalityResult ptrW
  = CasesTotal
  | TotalityCheckingError String
  | TotalityCheckCounterexample (TotalityCounterexample ptrW)

doCheckTotality :: forall sym arch v.
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  EquivM sym arch (TotalityResult (MM.ArchAddrWidth arch))
doCheckTotality bundle _preD exits =
  withSym $ \sym ->
    do
       -- compute the condition that leads to each of the computed
       -- exit pairs
       cases <- forM exits (\blkts -> PD.matchesBlockTarget bundle blkts >>= PAS.toPred sym)

       -- TODO, I really don't understand this abort case stuff, but it was copied
       -- from the triple verifier.
       isReturn <- do
         bothReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
         abortO <- PAb.isAbortedStatePred (PPa.get @PBi.Original (simOut bundle))
         returnP <- liftIO $ MCS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutP bundle) MCS.MacawBlockEndReturn
         abortCase <- liftIO $ W4.andPred sym abortO returnP
         liftIO $ W4.orPred sym bothReturn abortCase

       asm <- liftIO $ (forM (isReturn:cases) (W4.notPred sym) >>= (foldM (W4.andPred sym) (W4.truePred sym)))

       goalSat "doCheckTotality" asm $ \res -> case res of
         Unsat _ -> return CasesTotal
         Unknown -> return (TotalityCheckingError "UNKNOWN result when checking totality")
         Sat evalFn' -> withGroundEvalFn evalFn' $ \evalFn ->
           -- We found an execution that does not correspond to one of the
           -- executions listed above, so compute the counterexample.
           --
           -- TODO: if the location being jumped to is unconstrained (e.g., a return where we don't have
           -- information about the calling context) the solver will invent nonsense addresses for
           -- the location.  It might be better to only report concrete values for exit address
           -- if it is unique.
           do let oRegs  = PS.simRegs (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
              let pRegs  = PS.simRegs (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))
              let oIPReg = oRegs ^. MM.curIP
              let pIPReg = pRegs ^. MM.curIP
              let oBlockEnd = PS.simOutBlockEnd (PPa.pOriginal (PS.simOut bundle))
              let pBlockEnd = PS.simOutBlockEnd (PPa.pPatched  (PS.simOut bundle))

              let oMem = PS.simMem (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
              let pMem = PS.simMem (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))

              oBlockEndCase <- groundBlockEndCase sym (Proxy @arch) evalFn oBlockEnd
              pBlockEndCase <- groundBlockEndCase sym (Proxy @arch) evalFn pBlockEnd

              oIPV <- groundIPValue sym evalFn oIPReg
              pIPV <- groundIPValue sym evalFn pIPReg

              oInstr <- groundMuxTree sym evalFn (MT.memCurrentInstr oMem)
              pInstr <- groundMuxTree sym evalFn (MT.memCurrentInstr pMem)

              case (oIPV, pIPV) of
                (Just oval, Just pval) ->
                   return (TotalityCheckCounterexample
                     (TotalityCounterexample (oval,oBlockEndCase,oInstr) (pval,pBlockEndCase,pInstr)))
                (Nothing, _) ->
                  return (TotalityCheckingError ("IP register had unexpected type: " ++ show (PSR.macawRegRepr oIPReg)))
                (_, Nothing) ->
                  return (TotalityCheckingError ("IP register had unexpected type: " ++ show (PSR.macawRegRepr pIPReg)))

groundIPValue ::
  (sym ~ W4.ExprBuilder t st fs, LCB.IsSymInterface sym) =>
  sym ->
  W4.GroundEvalFn t ->
  PSR.MacawRegEntry sym tp ->
  IO (Maybe Integer)
groundIPValue _sym evalFn reg =
  case PSR.macawRegRepr reg of
    CLM.LLVMPointerRepr _w | CLM.LLVMPointer _ bv <- (PSR.macawRegValue reg)
      -> Just . BV.asUnsigned <$> W4.groundEval evalFn bv
    _ -> return Nothing

groundBlockEndCase ::
  (sym ~ W4.ExprBuilder t st fs, LCB.IsSymInterface sym) =>
  sym ->
  Proxy arch ->
  W4.GroundEvalFn t ->
  LCS.RegValue sym (MCS.MacawBlockEndType arch) ->
  IO MCS.MacawBlockEndCase
groundBlockEndCase sym prx evalFn v =
  do mt <- MCS.blockEndCase prx sym v
     groundMuxTree sym evalFn mt

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

followExit ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  (Integer, PPa.PatchPair (PB.BlockTarget arch)) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
followExit scope bundle currBlock d gr (idx, pPair) = 
  do traceBundle bundle ("Handling proof case " ++ show idx)
     res <- manifestError (triageBlockTarget scope bundle currBlock d gr pPair)
     case res of
       Left err ->
         do emitEvent $ PE.ErrorEmitted err
            return (recordMiscAnalysisError gr (GraphNode currBlock) err)
       Right gr' -> return gr'

-- Update the return summary node for the current function if this
--  sim bundle might return.
updateReturnNode ::
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
updateReturnNode scope bPair bundle preD gr = do
  isReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
  maybeUpdate gr $ withSatAssumption (PAS.fromPred isReturn) $ do
    framesMatch <- PD.associateFrames bundle MCS.MacawBlockEndReturn False
    withAssumptionSet framesMatch $
      handleReturn scope bundle bPair preD gr

maybeUpdate ::
  PairGraph sym arch -> 
  EquivM sym arch (Maybe (PairGraph sym arch)) ->
  EquivM sym arch (PairGraph sym arch)
maybeUpdate gr f = f >>= \case
  Just gr' -> return gr'
  Nothing -> return gr

-- | Figure out what kind of control-flow transition we are doing
--   here, and call into the relevant handlers.
triageBlockTarget ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.BlockTarget arch) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
triageBlockTarget scope bundle currBlock d gr blkts@(PPa.PatchPair blktO blktP) =
  do let
        blkO = PB.targetCall blktO
        blkP = PB.targetCall blktP
        pPair = PPa.PatchPair blkO blkP

     isPLT <- findPLTSymbol blkO blkP
     traceBundle bundle ("  targetCall: " ++ show blkO) 
     matches <- PD.matchesBlockTarget bundle blkts
     maybeUpdate gr $ withSatAssumption matches $ do
       framesMatch <- PD.associateFrames bundle (PB.targetEndCase blktO) (isJust isPLT)
       withAssumptionSet framesMatch $
         case (PB.targetReturn blktO, PB.targetReturn blktP) of
           (Just blkRetO, Just blkRetP) ->
             do traceBundle bundle ("  Return target " ++ show blkRetO ++ ", " ++ show blkRetP)

                -- TODO, this isn't correct.  Syscalls don't correspond to
                -- "ArchTermStmt" in any meaningful way, so this is all a misnomer.
                isSyscall <- case (PB.concreteBlockEntry blkO, PB.concreteBlockEntry blkP) of
                   (PB.BlockEntryPreArch, PB.BlockEntryPreArch) -> return True
                   (entryO, entryP) | entryO == entryP -> return False
                   _ -> throwHere $ PEE.BlockExitMismatch
                traceBundle bundle ("  Is Syscall? " ++ show isSyscall)

                ctx <- view PME.envCtxL
                let isEquatedCallSite = any (PPa.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)


                if | isSyscall -> handleSyscall scope bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                   | isEquatedCallSite -> handleInlineCallee scope bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                   | Just pltSymbol <- isPLT -> handlePLTStub scope bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP) pltSymbol
                   | otherwise -> handleOrdinaryFunCall scope bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)

           (Nothing, Nothing) -> withSym $ \sym ->
             do traceBundle bundle "No return target identified"
                p <- do j <- PD.matchingExits bundle MCS.MacawBlockEndJump
                        b <- PD.matchingExits bundle MCS.MacawBlockEndBranch
                        liftIO $ W4.orPred sym j b
                withAssumption p $
                  handleJump scope bundle currBlock d gr (mkNodeEntry currBlock pPair)

           _ -> do traceBundle bundle "BlockExitMismatch"
                   throwHere $ PEE.BlockExitMismatch

-- | See if the given jump targets correspond to a PLT stub for
--   the same symbol, and return it if so.
findPLTSymbol ::
  PB.ConcreteBlock arch PBi.Original ->
  PB.ConcreteBlock arch PBi.Patched ->
  EquivM sym arch (Maybe BS.ByteString)
findPLTSymbol blkO blkP =
  do PA.SomeValidArch archData <- asks envValidArch
     let oExtraMap = PA.validArchOrigExtraSymbols archData
     let pExtraMap = PA.validArchPatchedExtraSymbols archData

     let oAddr = PAd.addrToMemAddr (PB.concreteAddress blkO)
     let pAddr = PAd.addrToMemAddr (PB.concreteAddress blkP)

     -- TODO! TR is concerned that this may not work correctly for
     -- position independent code.
     case (MM.asAbsoluteAddr oAddr, MM.asAbsoluteAddr pAddr) of
       (Just oMw, Just pMw) -> do
         -- TODO, this is a stupid way to do this.  We should
         -- compute the reverse mapping in advance.
         let oSyms = [ s | (s,bv) <- Map.toList oExtraMap
                         , BV.asUnsigned bv == toInteger (MM.memWordValue oMw)
                     ]
         let pSyms = [ s | (s,bv) <- Map.toList pExtraMap
                         , BV.asUnsigned bv == toInteger (MM.memWordValue pMw)
                     ]
         case (oSyms, pSyms) of
           ([osym], [psym]) | osym == psym -> return (Just osym)
           _ -> return Nothing

       _ -> return  Nothing


-- TODO, as mentioned above, this is a misnomer and basically a bug.
-- System calls don't end up looking like this.
handleSyscall ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleSyscall _scope bundle _currBlock _d gr pPair pRetPair =
  do traceBundle bundle ("Encountered syscall! " ++ show pPair ++ " " ++ show pRetPair)
     return gr -- TODO!


-- TODO!!
handleInlineCallee ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleInlineCallee _scope _bundle _currBlock _d gr _pPair _pRetPair =
  return gr -- TODO!

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "funcall" where
  type TraceNodeType '(sym,arch) "funcall" = PPa.PatchPair (PB.FunctionEntry arch)
  prettyNode funs = PP.pretty funs

-- | Record the return vector for this call, and then handle a
--   jump to the entry point of the function.
handleOrdinaryFunCall ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleOrdinaryFunCall scope bundle currBlock d gr pPair pRetPair =
   case (PB.asFunctionEntry (PPa.pOriginal pPair), PB.asFunctionEntry (PPa.pPatched pPair)) of
     (Just oFun, Just pFun) ->
       do
          emitTrace @"funcall" (PPa.PatchPair oFun pFun)
          -- augmenting this block with the return point as its calling context
          currBlock' <- asks (PCfg.cfgContextSensitivity . envConfig) >>= \case
            PCfg.SharedFunctionAbstractDomains -> return currBlock
            PCfg.DistinctFunctionAbstractDomains -> return $ addContext pRetPair currBlock
          let
            funNode = mkNodeReturn currBlock' (PPa.PatchPair oFun pFun)
            returnSite = mkNodeEntry currBlock pRetPair
            callNode = mkNodeEntry currBlock' pPair
            gr' = addReturnVector gr funNode returnSite
          matches <- PD.matchingExits bundle MCS.MacawBlockEndCall
          withAssumption matches $
            handleJump scope bundle currBlock d gr' callNode
     _ -> panic Verifier "handleOrdinaryFunCall"
              [ "Ordinary function call jumped to a location that is not a function start!"
              , show currBlock
              , show pPair
              , show pRetPair
              ]

handlePLTStub ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  BS.ByteString {- ^ PLT symbol name -} ->
  EquivM sym arch (PairGraph sym arch)
handlePLTStub scope bundle currBlock d gr0 _pPair pRetPair stubSymbol = withSym $ \sym -> do
  PA.SomeValidArch archData <- asks envValidArch
  PA.StubOverride f <- case PA.lookupStubOverride archData stubSymbol of
    Just f -> do
      traceBundle bundle ("Using override for PLT stub " ++ show stubSymbol)
      return f
    Nothing -> do
      -- we have no model for this stub, so we emit a warning and unsoundly
      -- leave the state unmodified
      emitWarning $ PEE.UnknownPLTStub stubSymbol
      -- dummy override that does nothing
      return $ PA.StubOverride $ \_ st -> return st
  outputs <- PPa.forBins $ \get -> do
    nextSt <- liftIO $ f sym (PS.simOutState (get (PS.simOut bundle)))
    return $ (get (PS.simOut bundle)) { PS.simOutState = nextSt }
  let bundle' = bundle { PS.simOut = outputs }
  -- handleJump scope bundle' currBlock d gr0 pRetPair
  handleJump scope bundle' currBlock d gr0 (mkNodeEntry currBlock pRetPair)


handleReturn ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleReturn scope bundle currBlock d gr =
 do let fPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks currBlock)
    widenAlongEdge scope bundle (GraphNode currBlock) d gr (ReturnNode (mkNodeReturn currBlock fPair))

handleJump ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  NodeEntry arch {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
handleJump scope bundle currBlock d gr nextNode =
  widenAlongEdge scope bundle (GraphNode currBlock) d gr (GraphNode nextNode)


mkSimBundle ::
  PPa.BlockPair arch ->
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  AbstractDomain sym arch v ->
  EquivM sym arch (SimBundle sym arch v)
mkSimBundle pPair vars _d =
  do let oVarState = PS.simVarState (PPa.pOriginal vars)
     let pVarState = PS.simVarState (PPa.pPatched vars)
     oAbsState <- PD.getAbsDomain (PPa.pOriginal pPair)
     pAbsState <- PD.getAbsDomain (PPa.pPatched pPair)

     let simInO    = PS.SimInput oVarState (PPa.pOriginal pPair) oAbsState
     let simInP    = PS.SimInput pVarState (PPa.pPatched pPair) pAbsState

     traceBlockPair pPair "Simulating original blocks"
     (_asmO, simOutO_) <- PVSy.simulate simInO
     traceBlockPair pPair "Simulating patched blocks"
     (_asmP, simOutP_) <- PVSy.simulate simInP
     traceBlockPair pPair "Finished simulating blocks"

     let bnd = SimBundle (PPa.PatchPair simInO simInP) (PPa.PatchPair simOutO_ simOutP_)
     return bnd
     -- applyCurrentAsms bnd
