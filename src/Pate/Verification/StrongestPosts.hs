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

module Pate.Verification.StrongestPosts
  ( pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.) )
import           Control.Monad (foldM, forM, forM_)
import           Control.Monad.IO.Class
import           Control.Monad.Reader (asks)
import           Control.Monad.Except (runExceptT)
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import           Data.Proxy
import qualified Data.Text as Text

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.TraversableF as TF

import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Protocol.Online as W4
import qualified What4.Protocol.SMTWriter as W4
import           What4.SatResult (SatResult(..))

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator.RegValue as LCS
import           Lang.Crucible.Simulator.SymSequence
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFGSlice as MCS

import qualified Pate.Abort as PAb
import qualified Pate.Arch as PA
import qualified Pate.Address as PAd
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PCfg
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.EquivalenceDomain as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Monad.Context as PMC
import qualified Pate.Equivalence.Statistics as PESt
import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Proof.Instances as PPI
import qualified Pate.Monad.Environment as PME
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.Domain as PVD

import           Pate.Verification.PairGraph
import           Pate.Verification.Widening

import           Debug.Trace

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
  result <- runExceptT (runEquivM env doVerify)
  case result of
    Left err -> withValidEnv env (error (show err))
    Right r  -> return r

 where
   doVerify :: EquivM sym arch (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
   doVerify =
     do pg0 <- initializePairGraph pPairs

        -- To the main work of computing the dataflow fixpoint
        pg <- pairGraphComputeFixpoint pg0

        -- liftIO $ putStrLn "==== Whole program state ===="
        -- liftIO $ print (ppProgramDomains W4.printSymExpr pg)

        -- Report a summary of any errors we found during analysis
        reportAnalysisErrors pg

        result <- pairGraphComputeVerdict pg

        liftIO $ putStrLn $ unwords ["Overall verification verdict:", show result]

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
  PairGraph sym arch -> EquivM sym arch (PairGraph sym arch)
pairGraphComputeFixpoint gr =
  case chooseWorkItem gr of
    Nothing -> return gr
    Just (gr', nd, d) ->
      do gr'' <- visitNode nd d gr'
         pairGraphComputeFixpoint gr''

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
visitNode :: forall sym arch.
  GraphNode arch ->
  AbstractDomain sym arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)

visitNode (GraphNode bPair) d gr0 = withPair bPair $
  do -- do the symbolic simulation
     (asm, bundle) <- mkSimBundle bPair d

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

     gr1 <- checkObservables bPair asm bundle d gr0

     gr2 <- checkTotality bPair asm bundle d exitPairs gr1

     gr3 <- updateReturnNode bPair asm bundle d gr2

     -- Follow all the exit pairs we found
     foldM (\x y -> followExit asm bundle bPair d x y) gr3 (zip [0 ..] exitPairs)


visitNode (ReturnNode fPair) d gr0 =
  -- propagate the abstract domain of the return node to
  -- all of the known call sites of this function.
  foldM processReturn gr0 (getReturnVectors gr0 fPair)

 where
   -- Here, we're using a bit of a trick to propagate abstract domain information to call sites.
   -- We are making up a "dummy" simulation bundle that basically just represents a no-op, and
   -- using the ordinary widening machinery.

   processReturn gr ret = withPair ret $
     do (asm, bundle) <- returnSiteBundle d ret
        traceBundle bundle "Processing return edge"
--        traceBundle bundle "== bundle asm =="
--        traceBundle bundle (show (W4.printSymExpr asm))
        withEmptyAssumptionFrame $
          withAssumption_ (return asm) $
          widenAlongEdge bundle (ReturnNode fPair) d gr (GraphNode ret)


-- | Construct a "dummy" simulation bundle that basically just
--   immediately returns the prestate as the poststate.
--   This is used to compute widenings that propagate abstract domain
--   information from function return nodes to the actual return sites.
returnSiteBundle :: forall sym arch.
  AbstractDomain sym arch ->
  PPa.BlockPair arch {- ^ block pair being returned to -} ->
  EquivM sym arch (W4.Pred sym, SimBundle sym arch)
returnSiteBundle preD pPair =
  withEmptyAssumptionFrame $
  withSym $ \sym ->
  do let oVarState = PS.simVarState (PPa.pOriginal (PS.specVars preD))
     let pVarState = PS.simVarState (PPa.pPatched  (PS.specVars preD))

     let simInO    = PS.SimInput oVarState (PPa.pOriginal pPair)
     let simInP    = PS.SimInput pVarState (PPa.pPatched pPair)

     blockEndVal <- liftIO (MCS.initBlockEnd (Proxy @arch) sym)

     let simOutO   = PS.SimOutput oVarState blockEndVal
     let simOutP   = PS.SimOutput pVarState blockEndVal

     -- TODO? Not clear how much this rewrite step is going to do for us.  Perhaps just skip it?
     withAssumptionFrame (PVV.validInitState (Just pPair) oVarState pVarState) $
       applyCurrentFrame
         (SimBundle (PPa.PatchPair simInO simInP)
                    (PPa.PatchPair simOutO simOutP))

data ObservableCheckResult sym ptrW
  = ObservableCheckEq
  | ObservableCheckCounterexample (ObservableCounterexample sym ptrW)
  | ObservableCheckError String

checkObservables :: forall sym arch.
  PPa.BlockPair arch ->
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkObservables bPair asm bundle preD gr =
  considerObservableEvent gr bPair $
    do res <- doCheckObservables asm bundle preD
       case res of
         ObservableCheckEq ->
           do traceBundle bundle "Observables agree"
              return (Nothing, gr)
         ObservableCheckError msg ->
           do let msg' = ("Error checking observables: " ++ msg)
              traceBundle bundle msg'
              return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) (Text.pack msg'))
         ObservableCheckCounterexample cex@(ObservableCounterexample oSeq pSeq) -> do
           do traceBundle bundle ("Obserables disagree!")
              traceBundle bundle ("== Original sequence ==")
              traceBundle bundle (show (vcat (map MT.prettyMemEvent oSeq)))
              traceBundle bundle ("== Patched sequence ==")
              traceBundle bundle (show (vcat (map MT.prettyMemEvent pSeq)))
              return (Just cex, gr)

doCheckObservables :: forall sym arch.
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  EquivM sym arch (ObservableCheckResult sym (MM.ArchAddrWidth arch))
doCheckObservables asm bundle preD =
  withSym $ \sym ->
    do let oMem = PS.simMem (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
       let pMem = PS.simMem (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))

       -- TODO, lots of duplication here...
       vcfg <- asks envConfig
       stackRegion <- asks (PMC.stackRegion . envCtx)
       eqCtx <- equivalenceContext

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg

       -- Grab the specified areas of observable memory
       obsMem <- asks (PMC.observableMemory . envCtx)

       -- test if the memory operation overlaps with one of the observable regions
       let filterObservableMemOps op@(MT.MemOp (CLM.LLVMPointer blk off) _dir _cond _w _val _end) =
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

       precond <- liftIO $ do
         eqInputs <- PE.getPredomain sym bundle eqCtx (PS.specBody preD)
         eqPred   <- PE.preCondPredicate sym
                        (PPa.pOriginal (PS.simIn bundle))
                        (PPa.pPatched  (PS.simIn bundle))
                        eqInputs
         W4.andPred sym asm eqPred

       let doPanic = panic Solver "checkObservables" ["Online solving not enabled"]

       eqSeq <- liftIO (equivalentSequences sym oSeq pSeq)

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

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
         liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
           W4.inNewFrame sp $
           do W4.assume (W4.solverConn sp) precond
              W4.assume (W4.solverConn sp) =<< W4.notPred sym eqSeq
              W4.checkAndGetModel sp "checkObservableSequences" >>= \case
                  Unsat _ -> return ObservableCheckEq
                  Unknown -> return (ObservableCheckError "UNKNOWN result when checking observable sequences")
                  Sat evalFn ->
                    do -- NB, observable sequences are stored in reverse order, so we reverse them here to
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

-- TODO, this procedure can be exponential in the worst case,
-- because of the way we are splitting along merges.
--
-- It might be possible to do this in a better way, but
-- it's pretty tricky.
equivalentSequences :: forall sym ptrW.
  (LCB.IsSymInterface sym, 1 <= ptrW) =>
  sym ->
  SymSequence sym (MT.MemEvent sym ptrW) ->
  SymSequence sym (MT.MemEvent sym ptrW) ->
  IO (W4.Pred sym)
equivalentSequences sym = \xs ys -> loop [xs] [ys]
 where
  eqEvent :: MT.MemEvent sym ptrW -> MT.MemEvent sym ptrW -> IO (W4.Pred sym)

  eqEvent (MT.MemOpEvent xop) (MT.MemOpEvent yop) = eqMemOp sym xop yop

  eqEvent (MT.SyscallEvent _ x) (MT.SyscallEvent _ y) =
     case testEquality (W4.bvWidth x) (W4.bvWidth y) of
       Just Refl | Just W4.LeqProof <- W4.isPosNat (W4.bvWidth x) -> W4.bvEq sym x y
       _ -> return (W4.falsePred sym)

  eqEvent MT.MemOpEvent{} MT.SyscallEvent{} = return (W4.falsePred sym)
  eqEvent MT.SyscallEvent{} MT.MemOpEvent{} = return (W4.falsePred sym)

  -- The arguments to this loop are lists of SymSeqence values, which
  -- are basically a stack of list segments.
  -- The lists are used to manage append nodes, which get pushed onto the
  -- top of the stack when encountered.  This potentially loses sharing,
  -- but is pretty tricky to do better.

  -- nil/nil case, equal sequences
  loop [] [] = return (W4.truePred sym)

  -- nil/cons and cons/nil cases, unequal sequences
  loop [] (SymSequenceCons{}:_) = return (W4.falsePred sym)
  loop (SymSequenceCons{}:_) [] = return (W4.falsePred sym)

  -- just pop empty sequences off the top of the stack
  loop (SymSequenceNil:xs) ys = loop xs ys
  loop xs (SymSequenceNil:ys) = loop xs ys

  -- push appended sequences onto the stack
  loop (SymSequenceAppend _ xs1 xs2:xs) ys = loop (xs1:xs2:xs) ys
  loop xs (SymSequenceAppend _ ys1 ys2:ys) = loop xs (ys1:ys2:ys)

  -- special case, both sequences split on the same predicate
  loop (SymSequenceMerge _ px xs1 xs2:xs) (SymSequenceMerge _ py ys1 ys2:ys)
    | Just Refl <- testEquality px py =
    do eq1 <- loop (xs1:xs) (ys1:ys)
       eq2 <- loop (xs2:xs) (ys2:ys)
       W4.itePred sym px eq1 eq2

  -- split along merges on the top of the left stack
  loop (SymSequenceMerge _ p xs1 xs2:xs) ys =
    do eq1 <- loop (xs1:xs) ys
       eq2 <- loop (xs2:xs) ys
       W4.itePred sym p eq1 eq2

  -- split along merges on the top of the right stack
  loop xs (SymSequenceMerge _ p ys1 ys2:ys) =
    do eq1 <- loop xs (ys1:ys)
       eq2 <- loop xs (ys2:ys)
       W4.itePred sym p eq1 eq2

  -- cons/cons case.  Compare the heads and compare the tails
  loop (SymSequenceCons _ x xs1:xs) (SymSequenceCons _ y ys1:ys) =
    do eq1 <- eqEvent x y
       eq2 <- loop (xs1:xs) (ys1:ys)
       W4.andPred sym eq1 eq2



checkTotality :: forall sym arch.
  PPa.BlockPair arch ->
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkTotality bPair asm bundle preD exits gr =
  considerDesyncEvent gr bPair $
    do tot <- doCheckTotality asm bundle preD exits
       case tot of
         CasesTotal ->
           do traceBundle bundle "Totality check succeeded."
              return (Nothing, gr)
         TotalityCheckingError msg ->
           do let msg' = ("Error while checking totality! " ++ msg)
              traceBundle bundle msg'
              return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) (Text.pack msg'))
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


-- TODO? should we try to share work with the followExit/widenPostcondition calls?
doCheckTotality :: forall sym arch.
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  EquivM sym arch (TotalityResult (MM.ArchAddrWidth arch))
doCheckTotality asm bundle preD exits =
  withSym $ \sym ->
    do vcfg <- asks envConfig
       eqCtx <- equivalenceContext

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg

       precond <- liftIO $ do
         eqInputs <- PE.getPredomain sym bundle eqCtx (PS.specBody preD)
         eqInputsPred <- PE.preCondPredicate sym (PS.simInO bundle) (PS.simInP bundle) eqInputs
         W4.andPred sym asm eqInputsPred

       -- compute the condition that leads to each of the computed
       -- exit pairs
       cases <- forM exits $ \(PPa.PatchPair oBlkt pBlkt) ->
                  PD.matchesBlockTarget bundle oBlkt pBlkt

       -- TODO, I really don't understand this abort case stuff, but it was copied
       -- from the triple verifier.
       isReturn <- do
         bothReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
         abortO <- PAb.isAbortedStatePred (PPa.getPair @PBi.Original (simOut bundle))
         returnP <- liftIO $ MCS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutP bundle) MCS.MacawBlockEndReturn
         abortCase <- liftIO $ W4.andPred sym abortO returnP
         liftIO $ W4.orPred sym bothReturn abortCase

       let doPanic = panic Solver "checkTotality" ["Online solving not enabled"]

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
           liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
             W4.inNewFrame sp $
             do W4.assume (W4.solverConn sp) precond
                W4.assume (W4.solverConn sp) =<< W4.notPred sym isReturn
                forM_ cases $ \c ->
                  W4.assume (W4.solverConn sp) =<< W4.notPred sym c

                W4.checkAndGetModel sp "prove postcondition" >>= \case
                  Unsat _ -> return CasesTotal
                  Unknown -> return (TotalityCheckingError "UNKNOWN result when checking totality")
                  Sat evalFn ->
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
  W4.Pred sym ->
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  (Integer, PPa.PatchPair (PB.BlockTarget arch)) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
followExit asm bundle currBlock d gr (idx, pPair) =
  do traceBundle bundle ("Handling proof case " ++ show idx)
     res <- manifestError (triageBlockTarget asm bundle currBlock d gr pPair)
     case res of
       Left err ->
         do traceBlockPair currBlock ("Caught error: " ++ show err)
            return (recordMiscAnalysisError gr (GraphNode currBlock) (Text.pack (show err)))
       Right gr' -> return gr'

-- Update the return summary node for the current function if this
--  sim bundle might return.
updateReturnNode ::
  PPa.BlockPair arch ->
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
updateReturnNode bPair asm bundle preD gr =
    withEmptyAssumptionFrame $
    withAssumption_ (return asm) $
    do -- TODO? use withSatAssumption here, or something similar using an online solver?
       isReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
       case W4.asConstantPred isReturn of
         Just False -> return gr
         _ -> withAssumption_ (pure isReturn) $
                handleReturn bundle bPair preD gr

-- | Figure out what kind of control-flow transition we are doing
--   here, and call into the relevant handlers.
triageBlockTarget ::
  W4.Pred sym ->
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.BlockTarget arch) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
triageBlockTarget asm bundle currBlock d gr (PPa.PatchPair blktO blktP) =
  withEmptyAssumptionFrame $
  do let
        blkO = PB.targetCall blktO
        blkP = PB.targetCall blktP
        pPair = PPa.PatchPair blkO blkP

     traceBundle bundle ("  targetCall: " ++ show blkO)
     withAssumption_ (return asm) $
       -- TODO? use withSatAssumption here, or something similar using an online solver?
       withAssumption_ (PD.matchesBlockTarget bundle blktO blktP) $

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

              isPLT <- findPLTSymbol blkO blkP

              if | isSyscall -> handleSyscall bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                 | isEquatedCallSite -> handleInlineCallee bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                 | Just pltSymbol <- isPLT -> handlePLTStub bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP) pltSymbol
                 | otherwise -> handleOrdinaryFunCall bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)

         (Nothing, Nothing) -> withSym $ \sym ->
           do traceBundle bundle "No return target identified"
              p <- do j <- PD.matchingExits bundle MCS.MacawBlockEndJump
                      b <- PD.matchingExits bundle MCS.MacawBlockEndBranch
                      liftIO $ W4.orPred sym j b
              withAssumption_ (pure p) $
                handleJump bundle currBlock d gr pPair

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
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleSyscall bundle _currBlock _d gr pPair pRetPair =
  do traceBundle bundle ("Encountered syscall! " ++ show pPair ++ " " ++ show pRetPair)
     return gr -- TODO!


-- TODO!!
handleInlineCallee ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleInlineCallee _bundle _currBlock _d gr _pPair _pRetPair =
  return gr -- TODO!


-- | Record the return vector for this call, and then handle a
--   jump to the entry point of the function.
handleOrdinaryFunCall ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleOrdinaryFunCall bundle currBlock d gr pPair pRetPair =
   case (PB.asFunctionEntry (PPa.pOriginal pPair), PB.asFunctionEntry (PPa.pPatched pPair)) of
     (Just oFun, Just pFun) ->
       do let gr' = addReturnVector gr (PPa.PatchPair oFun pFun) pRetPair
          withAssumption_ (PD.matchingExits bundle MCS.MacawBlockEndCall) $
            handleJump bundle currBlock d gr' pPair
     _ -> panic Verifier "handleOrdinaryFunCall"
              [ "Ordinary function call jumped to a location that is not a function start!"
              , show currBlock
              , show pPair
              , show pRetPair
              ]

handlePLTStub ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  BS.ByteString {- ^ PLT symbol name -} ->
  EquivM sym arch (PairGraph sym arch)
handlePLTStub bundle currBlock d gr _pPair pRetPair stubSymbol =
  do traceBundle bundle ("Handling PLT stub " ++ show stubSymbol)

     -- TODO!! Here we are just assuming the unknown function represented by the PLT stub
     -- immediately returns without having any observable or memory effects!!
     --
     -- We should instead consult some parameter that defines the behavior of unknown functions,
     -- and only fall back on this default policy if no additional information can be found.
     -- Moreover, we should report this assumption about external functions as potentially leading
     -- to unsoundness.

     handleJump bundle currBlock d gr pRetPair


handleReturn ::
  SimBundle sym arch ->
  PPa.BlockPair arch ->
  AbstractDomain sym arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleReturn bundle currBlock d gr =
 do let fPair = TF.fmapF PB.blockFunctionEntry currBlock
    widenAlongEdge bundle (GraphNode currBlock) d gr (ReturnNode fPair)

handleJump ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.BlockPair arch {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
handleJump bundle currBlock d gr pPair =
  widenAlongEdge bundle (GraphNode currBlock) d gr (GraphNode pPair)


mkSimBundle ::
  PPa.BlockPair arch ->
  AbstractDomain sym arch ->
  EquivM sym arch (W4.Pred sym, SimBundle sym arch)
mkSimBundle pPair d =
  withEmptyAssumptionFrame $
  withSym $ \sym ->

  do let oVarState = PS.simVarState (PPa.pOriginal (PS.specVars d))
     let pVarState = PS.simVarState (PPa.pPatched  (PS.specVars d))

     let simInO    = PS.SimInput oVarState (PPa.pOriginal pPair)
     let simInP    = PS.SimInput pVarState (PPa.pPatched pPair)

     let rd = PE.eqDomainRegisters (PS.specBody d)

     withAssumptionFrame (PVV.validInitState (Just pPair) oVarState pVarState) $
       do traceBlockPair pPair "Simulating original blocks"
          (asmO, simOutO_) <- PVSy.simulate simInO
          traceBlockPair pPair "Simulating patched blocks"
          (asmP, simOutP_) <- PVSy.simulate simInP
          traceBlockPair pPair "Finished simulating blocks"

          let bnd = SimBundle (PPa.PatchPair simInO simInP) (PPa.PatchPair simOutO_ simOutP_)
          withAssumption_ (liftIO $ W4.andPred sym asmO asmP) $
            withAssumptionFrame_ (PVD.equateRegisters rd bnd) $
              applyCurrentFrame bnd
