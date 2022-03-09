{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pate.Verification.PairGraph
  ( Gas(..)
  , PairGraph(..)
  , initializePairGraph
  , chooseWorkItem
  , updateDomain
  , pairGraphComputeFixpoint
  ) where

import           Control.Lens (view)
import           Control.Monad (foldM)
import           Control.Monad.IO.Class
import           Control.Monad.Reader (asks)
import           Data.Maybe (fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word (Word32)

import qualified Data.Parameterized.TraversableF as TF

--import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Protocol.Online as W4
import qualified What4.Protocol.SMTWriter as W4
import           What4.SatResult (SatResult(..))

import qualified Lang.Crucible.Backend.Online as LCBO

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Config as PCfg
import qualified Pate.Discovery as PD
--import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Monad.Context as PMC
--import qualified Pate.Equivalence.StatePred as PES
import           Pate.Monad
--import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PS

--import qualified Pate.Verification as PV
import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy


newtype Gas = Gas Word32


-- | Temporary constant value for the gas parameter.
--   Should make this configurable.
initialGas :: Gas
initialGas = Gas 5

type AbstractDomain sym arch = PE.StatePredSpec sym arch

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

initializePairGraph ::
  [PPa.FunPair arch] ->
  EquivM sym arch (PairGraph sym arch)
initializePairGraph = foldM initPair emptyPairGraph
  where
    initPair gr fnPair =
      do let bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair

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
      do -- do the symbolic simulation
         (asm, bundle) <- mkSimBundle bPair d

         traceBundle bundle $ "Discovering exit pairs from " ++ (show bPair)

         -- TODO, manifest errors here?
         exitPairs <- PD.discoverPairs bundle

         traceBundle bundle $ (show (length exitPairs) ++ " pairs found!")

         -- TOOD! check totality of bundle pairs
         gr'' <- foldM (followExit asm bundle bPair d) gr' (zip [0 ..] exitPairs)

         -- recurse until fixpoint
         pairGraphComputeFixpoint gr''


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
       NoWideningRequired -> return gr
       WideningError msg ->
         do traceBundle bundle ("Error during widening: " ++ msg)
            return gr -- TODO? better error handling?
       Widen d'' -> 
         case updateDomain gr currBlock pPair d'' of
           Nothing ->
             do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show currBlock ++ " " ++ show pPair)
                return gr -- TODO? better error handling?
           Just gr' ->
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

data WidenResult sym arch
  = NoWideningRequired
  | WideningError String
  | Widen (AbstractDomain sym arch)

widenPostcondition ::
  PA.ValidArch arch =>
  SimBundle sym arch ->
  AbstractDomain sym arch {- ^ predomain -} ->
  AbstractDomain sym arch {- ^ postdomain -} ->
  EquivM sym arch (WidenResult sym arch)
widenPostcondition bundle preD postD =
  withSym $ \sym ->
    do vcfg <- asks envConfig
       asmFrame <- asks envCurrentFrame
       eqRel <- asks envBaseEquiv
       stackRegion <- asks (PMC.stackRegion . envCtx)

       precond <- liftIO $ do
         asm <- PS.getAssumedPred sym asmFrame
         eqInputs <- PE.getPrecondition sym stackRegion bundle eqRel (PS.specBody preD)
         W4.andPred sym asm eqInputs

       let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
       let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))
       (postCondAsm, postCondStatePred) <- liftIO (PS.bindSpec sym oPostState pPostState postD)

       postcond <- liftIO $ do
           eqPost <- PE.statePredPost sym
                             (PPa.pOriginal (PS.simOut bundle))
                             (PPa.pPatched  (PS.simOut bundle))
                             eqRel
                             postCondStatePred
           W4.andPred sym postCondAsm eqPost

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg
       PS.withOnlineSolver solver saveInteraction sym $ \bak ->

         liftIO $ LCBO.withSolverProcess bak doPanic $ \sp -> do
           let conn = W4.solverConn sp
           -- check if we already satisfy the associated condition
           W4.assume conn precond
           W4.assume conn =<< W4.notPred sym postcond
           W4.checkAndGetModel sp "prove postcondition" >>= \case
             Unsat _ -> return NoWideningRequired
             Unknown -> return (WideningError "UNKNOWN result evaluating postcondition")
             Sat evalFn ->
               -- The current execution does not satisfy the postcondition, and we have
               -- a counterexample.
               widenUsingCounterexample sp evalFn postCondStatePred

  where
    doPanic = panic Solver "widenPostcondition" ["Online solving not enabled"]

    widenUsingCounterexample sp evalFn postCondStatePred =
      do return (WideningError "TODO! we gave up in the widening step")


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
