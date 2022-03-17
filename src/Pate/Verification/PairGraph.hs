{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Verification.PairGraph
  ( Gas(..)
  , PairGraph(..)
  , initializePairGraph
  , chooseWorkItem
  , updateDomain
  , pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.), _1 )
import           Control.Monad (foldM, when, forM, forM_, unless)
import           Control.Monad.IO.Class
import           Control.Monad.Reader (asks)
import           Control.Monad.Writer (tell, execWriterT)
import           Control.Monad.Except (runExceptT)
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import           Data.Maybe (fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word (Word32)

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF
--import qualified Data.Parameterized.Context as Ctx

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

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS

import qualified Pate.Abort as PAb
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PCfg
import qualified Pate.Discovery as PD
--import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.MemCell as PMc
import qualified Pate.Monad.Context as PMC
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Equivalence.EquivalenceDomain as PEE
import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT
--import qualified Pate.Monad.Context as PMC
import qualified Pate.Proof.Instances as PPI
import qualified Pate.Monad.Environment as PME
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy


newtype Gas = Gas Word32


runVerificationLoop ::
  forall sym arch.
  PA.ValidArch arch =>
  EquivEnv sym arch ->
  -- | A list of block pairs to test for equivalence. They must be the entry points of functions.
  [PPa.FunPair arch] ->
  IO (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
runVerificationLoop env pPairs = do
  result <- runExceptT (runEquivM env doVerify)
  case result of
    Left err -> withValidEnv env (error (show err))
    Right r  -> return r

 where
   doVerify :: EquivM sym arch (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
   doVerify =
     do pg0 <- initializePairGraph pPairs
        _pg <- pairGraphComputeFixpoint pg0

        -- TODO, something useful
        let result = PEq.Equivalent

        statVar <- asks envStatistics
        stats <- liftIO $ MVar.readMVar statVar
        return (result, stats)


-- | Temporary constant value for the gas parameter.
--   Should make this configurable.
initialGas :: Gas
initialGas = Gas 5

-- For now, the abstract domains we track are just exactly
--  a 'PE.DomainSpec', but we may change/add to this as we go
type AbstractDomain sym arch = PE.DomainSpec sym arch

data PairGraph sym arch =
  PairGraph
  { pairGraphDomains :: !(Map (PPa.BlockPair arch) (AbstractDomain sym arch))
  , pairGraphGas :: !(Map (PPa.BlockPair arch, PPa.BlockPair arch) Gas)
  , pairGraphWorklist :: !(Set (PPa.BlockPair arch)) -- TODO? priority queue of some kind?
  }


emptyPairGraph :: PairGraph sym arch
emptyPairGraph =
  PairGraph
  { pairGraphDomains  = mempty
  , pairGraphGas      = mempty
  , pairGraphWorklist = mempty
  }

initializePairGraph :: forall sym arch.
  [PPa.FunPair arch] ->
  EquivM sym arch (PairGraph sym arch)
initializePairGraph = foldM initPair emptyPairGraph
  where
    initPair :: PairGraph sym arch -> PPa.FunPair arch -> EquivM_ sym arch (PairGraph sym arch)
    initPair gr fnPair =
      do let bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair
         withPair bPair $ do
           -- initial state of the pair graph: choose the universal domain that equates as much as possible
           idom <- PVD.universalDomainSpec bPair

           return
             gr{ pairGraphDomains  = Map.insert bPair idom (pairGraphDomains gr)
               , pairGraphWorklist = Set.insert bPair (pairGraphWorklist gr)
               }
 
chooseWorkItem ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  Maybe (PairGraph sym arch, PPa.BlockPair arch, AbstractDomain sym arch)
chooseWorkItem gr =
  -- choose the smallest pair from the worklist. This is a pretty brain-dead
  -- heuristic.  Perhaps we should do something more clever.
  case Set.minView (pairGraphWorklist gr) of
    Nothing -> Nothing
    Just (pPair, wl) ->
      case Map.lookup pPair (pairGraphDomains gr) of
        Nothing -> panic Verifier "choseWorkItem" ["Could not find domain corresponding to block pair", show pPair]
        Just d  -> Just (gr{ pairGraphWorklist = wl }, pPair, d)


updateDomain ::
  PairGraph sym arch {- ^ pair graph to update -} ->
  PPa.BlockPair arch {- ^ point pair we are jumping from -} ->
  PPa.BlockPair arch {- ^ point pair we are jumping to -} ->
  AbstractDomain sym arch {- ^ new domain value to insert -} ->
  Maybe (PairGraph sym arch)
updateDomain gr pFrom pTo d
  | g > 0 = Just PairGraph
            { pairGraphDomains  = Map.insert pTo d (pairGraphDomains gr)
            , pairGraphGas      = Map.insert (pFrom,pTo) (Gas (g-1)) (pairGraphGas gr)
            , pairGraphWorklist = Set.insert pTo (pairGraphWorklist gr)
            }

  | otherwise = Nothing

  where
     -- Lookup the amount of remaining gas.  Initialize to a fresh value
     -- if it is not in the map
      Gas g = fromMaybe initialGas (Map.lookup (pFrom,pTo) (pairGraphGas gr))


pairGraphComputeFixpoint ::
  PairGraph sym arch -> EquivM sym arch (PairGraph sym arch)
pairGraphComputeFixpoint gr =
  case chooseWorkItem gr of
    Nothing -> return gr
    Just (gr', bPair, d) ->
      pairGraphComputeFixpoint =<<
      (withPair bPair $
      do -- do the symbolic simulation
         (asm, bundle) <- mkSimBundle bPair d

         -- Compute exit pairs
         traceBundle bundle $ "Discovering exit pairs from " ++ (show bPair)
         -- TODO, manifest errors here?
         exitPairs <- PD.discoverPairs bundle
         traceBundle bundle $ (show (length exitPairs) ++ " pairs found!")

         checkObservables asm bundle d

         -- Check the totality of the discovered pairs
         tot <- checkTotality asm bundle d exitPairs
         case tot of
           CasesTotal ->
             traceBundle bundle "Totality check succeeded."
           TotalityCheckingError msg ->
             traceBundle bundle ("Error while checking totality! " ++ msg)
           TotalityCounterexample (oIP,oEnd) (pIP,pEnd) ->
             traceBundle bundle $ unwords
               ["Found extra exit while checking totality:"
               , showHex oIP "", PPI.ppExitCase oEnd, showHex pIP "", PPI.ppExitCase pEnd
               ]

         -- Follow all the exit pairs we found
         foldM (followExit asm bundle bPair d) gr' (zip [0 ..] exitPairs)
      )


checkObservables :: forall sym arch.
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  EquivM sym arch ()
checkObservables asm bundle preD =
  withSym $ \sym ->
    do let oMem = PS.simMem (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
       let pMem = PS.simMem (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))

       oSeq <- liftIO (MT.observableEvents sym oMem)
       pSeq <- liftIO (MT.observableEvents sym pMem)

       traceBundle bundle $ unlines
         [ "== original event trace =="
         , show (prettySymSequence ppEvent oSeq)
         ] 

       traceBundle bundle $ unlines
         [ "== patched event trace =="
         , show (prettySymSequence ppEvent pSeq)
         ]

       -- TODO! actually check the equivalance of the observables


-- TODO move into MemTrace and do it properly
ppEvent :: LCB.IsSymInterface sym => MT.MemEvent sym ptrW -> Doc ann
ppEvent (MT.MemOpEvent op)   = pretty "MemOp"
ppEvent (MT.SyscallEvent ex) = pretty "SyscallEvent" <+> W4.printSymExpr ex


data TotalityResult
  = CasesTotal
  | TotalityCheckingError String
  | TotalityCounterexample (Integer,MS.MacawBlockEndCase) (Integer,MS.MacawBlockEndCase)

-- TODO? should we try to share work with the followExit/widenPostcondition calls?
checkTotality :: forall sym arch.
  W4.Pred sym ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  EquivM sym arch TotalityResult
checkTotality asm bundle preD exits =
  withSym $ \sym ->
    do vcfg <- asks envConfig
       eqRel <- asks envBaseEquiv
       stackRegion <- asks (PMC.stackRegion . envCtx)

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg

       precond <- liftIO $ do
         eqInputs <- PE.getPredomain sym stackRegion bundle eqRel (PS.specBody preD)
         W4.andPred sym asm eqInputs

       -- compute the condition that leads to each of the computed
       -- exit pairs
       cases <- forM exits $ \(PPa.PatchPair oBlkt pBlkt) ->
                  PD.matchesBlockTarget bundle oBlkt pBlkt

       isUnknown <- do
         isJump <- matchingExits bundle MS.MacawBlockEndJump
         isFail <- matchingExits bundle MS.MacawBlockEndFail
         isBranch <- matchingExits bundle MS.MacawBlockEndBranch
         liftIO (W4.orPred sym isJump =<< W4.orPred sym isFail isBranch)

       isReturn <- do
         bothReturn <- matchingExits bundle MS.MacawBlockEndReturn
         abortO <- PAb.isAbortedStatePred (PPa.getPair @PBi.Original (simOut bundle))
         returnP <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutP bundle) MS.MacawBlockEndReturn
         abortCase <- liftIO $ W4.andPred sym abortO returnP
         liftIO $ W4.orPred sym bothReturn abortCase


       let doPanic = panic Solver "checkTotality" ["Online solving not enabled"]

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
           do liftIO $ LCBO.withSolverProcess bak doPanic $ \sp -> do
                W4.assume (W4.solverConn sp) precond
                W4.assume (W4.solverConn sp) =<< W4.notPred sym isReturn
                W4.assume (W4.solverConn sp) =<< W4.notPred sym isUnknown
                forM_ cases $ \c ->
                  W4.assume (W4.solverConn sp) =<< W4.notPred sym c
                W4.checkAndGetModel sp "prove postcondition" >>= \case
                  Unsat _ -> return CasesTotal
                  Unknown -> return (TotalityCheckingError "UNKNOWN result when checking totality")
                  Sat evalFn ->
                    -- We found an execution that does not correspond to one of the
                    -- executions listed in "exits"
                    do let oRegs  = PS.simRegs (PS.simOutState (PPa.pOriginal (PS.simOut bundle)))
                       let pRegs  = PS.simRegs (PS.simOutState (PPa.pPatched  (PS.simOut bundle)))
                       let oIPReg = oRegs ^. MM.curIP
                       let pIPReg = pRegs ^. MM.curIP
                       let oBlockEnd = PS.simOutBlockEnd (PPa.pOriginal (PS.simOut bundle))
                       let pBlockEnd = PS.simOutBlockEnd (PPa.pPatched  (PS.simOut bundle))

                       -- Ugh, gross
                       q1 <- W4.groundEval evalFn (LCS.unRV (oBlockEnd ^. _1))
                       let oBlockEndCase :: MS.MacawBlockEndCase = toEnum . fromInteger . BV.asUnsigned $ q1
                       q2 <- W4.groundEval evalFn @(W4.BaseBVType 3) (LCS.unRV (pBlockEnd ^. _1))
                       let pBlockEndCase :: MS.MacawBlockEndCase = toEnum . fromInteger . BV.asUnsigned $ q2

                       -- Also gross
                       case PSR.macawRegRepr oIPReg of
                         CLM.LLVMPointerRepr _w | CLM.LLVMPointer _ obv <- (PSR.macawRegValue oIPReg) ->
                           case PSR.macawRegRepr pIPReg of
                             CLM.LLVMPointerRepr _w | CLM.LLVMPointer _ pbv <- (PSR.macawRegValue pIPReg) ->
                               do oIPVal <- BV.asUnsigned <$> W4.groundEval evalFn obv
                                  pIPVal <- BV.asUnsigned <$> W4.groundEval evalFn pbv
                                  return (TotalityCounterexample (oIPVal,oBlockEndCase) (pIPVal,pBlockEndCase))
                             res -> return (TotalityCheckingError ("IP register had unexpected type: " ++ show res))
                         res -> return (TotalityCheckingError ("IP register had unexpected type: " ++ show res))


matchingExits ::
  forall sym arch.
  SimBundle sym arch ->
  MS.MacawBlockEndCase ->
  EquivM sym arch (W4.Pred sym)
matchingExits bundle ecase = withSym $ \sym -> do
  case1 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutO bundle) ecase
  case2 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutP bundle) ecase
  liftIO $ W4.andPred sym case1 case2



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
         do -- TODO! make a more permanant record of errors
            traceBlockPair currBlock ("Caught error: " ++ show err)
            return gr
       Right gr' -> return gr'

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
       withAssumption_ (PD.matchesBlockTarget bundle blktO blktP) $

       case (PB.targetReturn blktO, PB.targetReturn blktP) of
         (Just blkRetO, Just blkRetP) ->
           do traceBundle bundle ("  Return target " ++ show blkRetO ++ ", " ++ show blkRetP)

              -- TODO, this isn't really correct.  Syscalls don't correspond to
              -- "ArchTermStmt" in any meaningful way.
              isSyscall <- case (PB.concreteBlockEntry blkO, PB.concreteBlockEntry blkP) of
                 (PB.BlockEntryPreArch, PB.BlockEntryPreArch) -> return True
                 (entryO, entryP) | entryO == entryP -> return False
                 _ -> throwHere $ PEE.BlockExitMismatch
              traceBundle bundle ("  Is Syscall? " ++ show isSyscall)

              ctx <- view PME.envCtxL
              let isEquatedCallSite = any (PPa.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)

              if | isSyscall -> handleSyscall bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                 | isEquatedCallSite -> handleInlineCallee bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)
                 | otherwise -> handleOrdinaryFunCall bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)

         (Nothing, Nothing) ->
           do traceBundle bundle "No return target identified"
              handleJump bundle currBlock d gr pPair

         _ -> do traceBundle bundle "BlockExitMismatch"
                 throwHere $ PEE.BlockExitMismatch

handleSyscall ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleSyscall bundle currBlock d gr pPair pRetPair =
  do traceBundle bundle ("Encountered syscall! " ++ show pPair ++ " " ++ show pRetPair)
     return gr -- TODO!

handleInlineCallee ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleInlineCallee bundle currBlock d gr pPair pRetPair =
  return gr -- TODO!


handleOrdinaryFunCall ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleOrdinaryFunCall bundle currBlock d gr pPair _pRetPair =
  -- TODO? we are just ignoring the retPair...
  handleJump bundle currBlock d gr pPair

handleJump ::
  SimBundle sym arch ->
  PPa.BlockPair arch {- ^ current entry point -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.BlockPair arch {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
handleJump bundle currBlock d gr pPair =
  do d' <- getTargetDomain pPair gr
     md <- widenPostcondition bundle d d'
     case md of
       NoWideningRequired ->
         do traceBundle bundle "Did not need to widen"
            return gr
       WideningError msg ->
         do traceBundle bundle ("Error during widening: " ++ msg)
            return gr -- TODO? better error handling?
       Widen _ d'' ->
         case updateDomain gr currBlock pPair d'' of
           Nothing ->
             do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show currBlock ++ " " ++ show pPair)
                return gr -- TODO? better error handling?
           Just gr' ->
             do traceBundle bundle "Successfully widened postcondition"
                return gr'

getTargetDomain ::
  PPa.BlockPair arch ->
  PairGraph sym arch ->
  EquivM sym arch (AbstractDomain sym arch)
getTargetDomain pPair gr =
  case Map.lookup pPair (pairGraphDomains gr) of
    Just d  -> return d
    Nothing ->
      -- initial state of the pair graph: choose the universal domain that equates as much as possible
      PVD.universalDomainSpec pPair

data WidenLocs sym arch =
  WidenLocs
    (Set (Some (MM.ArchReg arch)))
    (Set (Some (PMc.MemCell sym arch)))

instance PA.ValidArch arch => Show (WidenLocs sym arch) where
  show (WidenLocs regs cells) =
    unlines [ unwords (map show (Set.toList regs))
            , show (Set.size cells) ++ " memory locations"
            ]

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Semigroup (WidenLocs sym arch) where
  (WidenLocs r1 m1) <> (WidenLocs r2 m2) = WidenLocs (r1 <> r2) (m1 <> m2)

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Monoid (WidenLocs sym arch) where
  mempty = WidenLocs mempty mempty

data WidenResult sym arch
  = NoWideningRequired
  | WideningError String
  | Widen (WidenLocs sym arch) (AbstractDomain sym arch)

-- | Try the given widening stratetigs s one at a time,
--   until the first one that computes some nontrival
--   widening, or returns an error.
tryWidenings ::
  [IO (WidenResult sym arch)] ->
  IO (WidenResult sym arch)
tryWidenings [] = return NoWideningRequired
tryWidenings (x:xs) =
  x >>= \case
    NoWideningRequired -> tryWidenings xs
    res -> return res

widenPostcondition :: forall sym arch.
  PA.ValidArch arch =>
  SimBundle sym arch ->
  AbstractDomain sym arch {- ^ predomain -} ->
  AbstractDomain sym arch {- ^ postdomain -} ->
  EquivM sym arch (WidenResult sym arch)
widenPostcondition bundle preD postD0 =
  withSym $ \sym ->
    do vcfg <- asks envConfig
       asmFrame <- asks envCurrentFrame
       eqRel <- asks envBaseEquiv
       stackRegion <- asks (PMC.stackRegion . envCtx)

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg

       precond <- liftIO $ do
         asm <- PS.getAssumedPred sym asmFrame
         eqInputs <- PE.getPredomain sym stackRegion bundle eqRel (PS.specBody preD)
         W4.andPred sym asm eqInputs

       -- traceBundle bundle "== widenPost: precondition =="
       -- traceBundle bundle (show (W4.printSymExpr precond))

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
         do liftIO $ LCBO.withSolverProcess bak doPanic $ \sp -> do
              W4.assume (W4.solverConn sp) precond
            widenLoop sym bak eqRel postD0 Nothing

 where
   doPanic = panic Solver "widenPostcondition" ["Online solving not enabled"]

   -- TODO, we should probably have some way to bound the amout of times we can
   --  recurse into the widening loop, or we really need to be very careful to
   --  make sure that this kind of local widening will terminate in a reasonable
   --  number of steps.
   widenLoop ::
     ( bak ~ LCBO.OnlineBackend solver t st fs
     , sym ~ W4.ExprBuilder t st fs
     , W4.OnlineSolver solver
     , LCB.IsSymBackend sym bak
     , PA.ValidArch arch ) =>
     sym ->
     bak ->
     EquivRelation sym arch ->
     AbstractDomain sym arch ->
     Maybe (WidenLocs sym arch) ->
     EquivM sym arch (WidenResult sym arch)
   widenLoop sym bak eqRel postD mlocs =
     do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
        let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))
        (postCondAsm, postCondStatePred) <- liftIO (PS.bindSpec sym oPostState pPostState postD)

        postcond <- liftIO $ do
            eqPost <- PE.eqDomPost sym
                              (PPa.pOriginal (PS.simOut bundle))
                              (PPa.pPatched  (PS.simOut bundle))
                              eqRel
                              postCondStatePred
            W4.andPred sym postCondAsm eqPost

        --traceBundle bundle "== widenPost: postcondition =="
        --traceBundle bundle (show (W4.printSymExpr postcond))

        res <-
          liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
            W4.inNewFrame sp $
              do let conn = W4.solverConn sp
                 -- check if we already satisfy the associated condition

                 W4.assume conn =<< W4.notPred sym postcond
                 W4.checkAndGetModel sp "prove postcondition" >>= \case
                   Unsat _ -> return NoWideningRequired
                   Unknown -> return (WideningError "UNKNOWN result evaluating postcondition")
                   Sat evalFn ->
                     -- The current execution does not satisfy the postcondition, and we have
                     -- a counterexample.
                     widenUsingCounterexample sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD

        -- Re-enter the widening loop if we had to widen at this step.
        -- If this step completed, use the success continuation to
        -- return the result.  Only in the first iteration will we
        -- finally return a `NoWideningRequired`.  In other cases, we
        -- had to widen at least once.
        case res of
          WideningError{} -> return res

          NoWideningRequired ->
            case mlocs of
              Nothing   -> return NoWideningRequired
              Just locs -> return (Widen locs postD)

          Widen locs postD' ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show locs)
               let newlocs = case mlocs of
                               Nothing    -> Just locs
                               Just locs' -> Just (locs <> locs')
               widenLoop sym bak eqRel postD' newlocs


widenUsingCounterexample ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
widenUsingCounterexample sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD =
  tryWidenings
    [ widenRegisters sym evalFn bundle eqRel postCondAsm postCondStatePred postD
    , widenStack sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD
    , widenHeap sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD
    , return $ WideningError "Could not find any values to widen!"
    ]


-- TODO, lots of code duplication between the stack and heap cases.
--  should we find some generalization?
widenHeap ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
widenHeap sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD =
  do xs <- findUnequalHeapMemCells sym evalFn bundle eqRel preD
     ys <- findUnequalHeapWrites sym evalFn bundle eqRel
     let zs = xs++ys
     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- PMc.predFromList sym [ (c, W4.truePred sym) | c <- zs ]
          let heapDom = PEM.memDomainPred (PEE.eqDomainGlobalMemory (PS.specBody postD))
          heapDom' <- PMc.mergeMemCellPred sym heapDom newCells
          let md' = (PEE.eqDomainGlobalMemory (PS.specBody postD)){ PEM.memDomainPred = heapDom' }
          let pred' = (PS.specBody postD){ PEE.eqDomainGlobalMemory = md' }
          let postD' = postD{ PS.specBody = pred' }
          return (Widen (WidenLocs mempty (Set.fromList zs)) postD')

widenStack ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
widenStack sym evalFn bundle eqRel postCondAsm postCondStatePred preD postD =
  do xs <- findUnequalStackMemCells sym evalFn bundle eqRel preD
     ys <- findUnequalStackWrites sym evalFn bundle eqRel
     let zs = xs++ys
     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- PMc.predFromList sym [ (c, W4.truePred sym) | c <- zs ]
          let stackDom = PEM.memDomainPred (PEE.eqDomainStackMemory (PS.specBody postD))
          stackDom' <- PMc.mergeMemCellPred sym stackDom newCells
          let md' = (PEE.eqDomainStackMemory (PS.specBody postD)){ PEM.memDomainPred = stackDom' }
          let pred' = (PS.specBody postD){ PEE.eqDomainStackMemory = md' }
          let postD' = postD{ PS.specBody = pred' }
          return (Widen (WidenLocs mempty (Set.fromList zs)) postD')


findUnequalHeapWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalHeapWrites sym evalFn bundle eqRel =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym footprints (W4.falsePred sym))
     execWriterT $ forM_ memWrites $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquiv sym oPostState pPostState (PE.eqRelMem eqRel) cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalStackWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalStackWrites sym evalFn bundle eqRel =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym footprints (W4.falsePred sym))
     execWriterT $ forM_ memWrites $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquiv sym oPostState pPostState (PE.eqRelStack eqRel) cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalHeapMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  AbstractDomain sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalHeapMemCells sym evalFn bundle eqRel preD =
  do let prestateHeapCells = PEM.toList (PEE.eqDomainGlobalMemory (PS.specBody preD))
     let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     execWriterT $ forM_ prestateHeapCells $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquiv sym oPostState pPostState (PE.eqRelMem eqRel) cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalStackMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  AbstractDomain sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalStackMemCells sym evalFn bundle eqRel preD =
  do let prestateStackCells = PEM.toList (PEE.eqDomainStackMemory (PS.specBody preD))
     let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     execWriterT $ forM_ prestateStackCells $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquiv sym oPostState pPostState (PE.eqRelStack eqRel) cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

widenRegisters ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
widenRegisters sym evalFn bundle eqRel postCondAsm postCondStatePred postD =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     newRegs <- findUnequalRegs sym evalFn eqRel
                   (PEE.eqDomainRegisters postCondStatePred)
                   (PS.simRegs oPostState)
                   (PS.simRegs pPostState)

     if null newRegs then
       return NoWideningRequired
     else
       -- TODO, widen less aggressively?
       let regs' = foldl
                     (\m (Some r) -> PER.update sym (\ _ -> W4.falsePred sym) r m)
                     (PEE.eqDomainRegisters (PS.specBody postD))
                     newRegs
           pred' = (PS.specBody postD)
                   { PEE.eqDomainRegisters = regs'
                   }
           locs = WidenLocs (Set.fromList newRegs) mempty
        in return (Widen locs postD{ PS.specBody = pred' })


findUnequalRegs ::
  ( PA.ValidArch arch
  , sym ~ W4.ExprBuilder t st fs ) =>
  sym ->
  W4.GroundEvalFn t ->
  EquivRelation sym arch ->
  PER.RegisterDomain sym arch ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  IO [Some (MM.ArchReg arch)]
findUnequalRegs sym evalFn eqRel regPred oRegs pRegs =
  execWriterT $ MM.traverseRegsWith_
    (\regName oRegVal ->
         do let pRegVal = MM.getBoundValue regName pRegs
            let pRegEq  = PER.registerInDomain sym regName regPred
            regEq <- liftIO (W4.groundEval evalFn pRegEq)
            when regEq $
              do isEqPred <- liftIO (applyRegEquivRelation (PE.eqRelRegs eqRel) regName oRegVal pRegVal)
                 isEq <- liftIO (W4.groundEval evalFn isEqPred)
                 when (not isEq) (tell [Some regName]))
    oRegs


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

     withAssumptionFrame (PVV.validInitState (Just pPair) oVarState pVarState) $
       do traceBlockPair pPair "Simulating original blocks"
          (asmO, simOutO_) <- PVSy.simulate simInO
          traceBlockPair pPair "Simulating patched blocks"
          (asmP, simOutP_) <- PVSy.simulate simInP
          traceBlockPair pPair "Finished simulating blocks"
          (_, simOutO') <- withAssumptionFrame (PVV.validConcreteReads simOutO_) $ return simOutO_
          (_, simOutP') <- withAssumptionFrame (PVV.validConcreteReads simOutP_) $ return simOutP_

          withAssumption_ (liftIO $ W4.andPred sym asmO asmP) $
            applyCurrentFrame (SimBundle (PPa.PatchPair simInO simInP) (PPa.PatchPair simOutO' simOutP'))
