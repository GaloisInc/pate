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

module Pate.Verification.Widening
  ( widenAlongEdge
  , WidenLocs(..)
  ) where

import           Control.Monad (when, forM_, unless)
import           Control.Monad.IO.Class
import           Control.Monad.Reader (asks)
import           Control.Monad.Writer (tell, execWriterT)

import           Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
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

import qualified Data.Macaw.CFG as MM

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Config as PCfg
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.MemCell as PMc
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.EquivalenceDomain as PEE
import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT

import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified Pate.Verification.Domain as PVD
import           Pate.Verification.PairGraph

-- | Generate a fresh abstract domain value for the given graph node.
--   This should represent the most information we can ever possibly
--   have (i.e., all values are equal) as it will only ever be
--   weakend via widening.
makeFreshAbstractDomain ::
  GraphNode arch ->
  EquivM sym arch (AbstractDomain sym arch)
makeFreshAbstractDomain (GraphNode pPair) = PVD.universalDomainSpec pPair
makeFreshAbstractDomain (ReturnNode fPair) =
  -- TODO, this isn't really right, but seems pretty harmless.  The
  -- only thing the concrete block value is used for is to assign more
  -- human-readable names to arguments if we have debug information.
  PVD.universalDomainSpec (TF.fmapF PB.functionEntryToConcreteBlock fPair)

-- | Given the results of symbolic execution, and an edge in the pair graph
--   to consider, compute an updated abstract domain for the target node,
--   and update the pair graph, if necessary.
--
--   This is done by looking up the abstract domain for the target node
--   and proving that the poststate of symbolic execution satisfies
--   the abstract domain of the target node, assuming the abstract domain of
--   the source node.  If this is not the case, we use the resulting counterexample
--   to determing what additional locations need to be added to the target
--   abstract domain. We perform these widening steps in a loop until
--   the process converges or we run out of gas.
--
--   When widening, we first consider register values to widen, then we look at
--   stack, and finally global memory for locations. When widening memory, we
--   consider first locations that differ in the prestate, then locations that
--   were written during the execution of the block.  In theory, this should
--   enough to account for all the sources of differences we have to consider.
--
--   If, for some reason, we cannot find appropraite locations to widen, we
--   widen as much as we can, and report an error.
widenAlongEdge ::
  SimBundle sym arch {- ^ results of symbolic execution for this block -} ->
  GraphNode arch {- ^ current graph node -} ->
  AbstractDomain sym arch {- ^ current abstract domain -} ->
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ next graph node -} ->
  EquivM sym arch (PairGraph sym arch)
widenAlongEdge bundle from d gr to =

  case Map.lookup to (pairGraphDomains gr) of
    -- This is the first time we have discovered this location
    Nothing ->
     do traceBundle bundle ("First jump to " ++ show to)
        -- initial state of the pair graph: choose the universal domain that equates as much as possible
        d' <- makeFreshAbstractDomain to

        -- compute an initial widening, if necessary
        md <- widenPostcondition bundle d d'
        case md of
          NoWideningRequired ->
            return (freshDomain gr to d')
          WideningError msg _ d'' ->
            do -- TODO? better error handling?
               traceBundle bundle ("Error during widening: " ++ msg)
               return (freshDomain gr to d'') 
          Widen _ d'' ->
            return (freshDomain gr to d'')

    -- have visited this location at least once before
    Just d' ->
     do md <- widenPostcondition bundle d d'
        case md of
          NoWideningRequired ->
            do traceBundle bundle "Did not need to widen"
               return gr
          WideningError msg _ d'' ->
            do -- TODO? better error handling?
               traceBundle bundle ("Error during widening: " ++ msg)
               case updateDomain gr from to d'' of
                 Nothing ->
                   do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                      return gr{ pairGraphGasExhausted = Set.insert to (pairGraphGasExhausted gr) }
                 Just gr' -> return gr'
          Widen _ d'' ->
            case updateDomain gr from to d'' of
              Nothing ->
                do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                   return gr{ pairGraphGasExhausted = Set.insert to (pairGraphGasExhausted gr) }
              Just gr' ->
                do traceBundle bundle "Successfully widened postcondition"
                   return gr'


-- | Information about what locations were widened
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
  | WideningError String (WidenLocs sym arch) (AbstractDomain sym arch)
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
       eqCtx <- equivalenceContext

       let solver = PCfg.cfgSolver vcfg
       let saveInteraction = PCfg.cfgSolverInteractionFile vcfg

       precond <- liftIO $ do
         asm <- PS.getAssumedPred sym asmFrame
         eqInputs <- PE.getPredomain sym bundle eqCtx (PS.specBody preD)
         eqInputsPred <- PE.preCondPredicate sym (PS.simInO bundle) (PS.simInP bundle) eqInputs
         W4.andPred sym asm eqInputsPred

       --traceBundle bundle "== widenPost: precondition =="
       --traceBundle bundle (show (W4.printSymExpr precond))

       traceBundle bundle "Entering widening loop"

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
         do liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
              do W4.push sp
                 W4.assume (W4.solverConn sp) precond
            widenLoop sym bak initialGas eqCtx postD0 Nothing

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
     Gas ->
     EquivContext sym arch ->
     AbstractDomain sym arch ->
     Maybe (WidenLocs sym arch) ->
     EquivM sym arch (WidenResult sym arch)
   widenLoop _sym _bak (Gas i) _eqCtx postD mlocs | i <= 0 =
     do let msg = "Ran out of gas performing local widenings"
        return (WideningError msg (fromMaybe mempty mlocs) postD)

   widenLoop sym bak (Gas i) eqCtx postD mlocs =
     do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
        let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))
        (postCondAsm, postCondStatePred) <- liftIO (PS.bindSpec sym oPostState pPostState postD)

        eqPost <- liftIO $ PE.eqDomPost sym
                              (PPa.pOriginal (PS.simOut bundle))
                              (PPa.pPatched  (PS.simOut bundle))
                              eqCtx
                              postCondStatePred
        eqPostPred <- liftIO (PE.postCondPredicate sym eqPost)
        postcond <- liftIO $ W4.andPred sym postCondAsm eqPostPred

--        traceBundle bundle "== widenPost: postcondition asm =="
--        traceBundle bundle (show (W4.printSymExpr postCondAsm))

--        traceBundle bundle "== widenPost: postcondition eqPost =="
--        traceBundle bundle (show (W4.printSymExpr eqPost))

        res <-
          liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
            W4.inNewFrame sp $
            do let conn = W4.solverConn sp
               -- check if we already satisfy the associated condition
               W4.assume conn =<< W4.notPred sym postcond
               W4.checkAndGetModel sp "prove postcondition" >>= \case
                 Unsat _ -> return NoWideningRequired
                 Unknown -> return (WideningError "UNKNOWN result evaluating postcondition" (fromMaybe mempty mlocs) postD)
                 Sat evalFn ->
                   -- The current execution does not satisfy the postcondition, and we have
                   -- a counterexample.
                   widenUsingCounterexample sym evalFn bundle eqCtx postCondAsm postCondStatePred preD mlocs postD

        -- Re-enter the widening loop if we had to widen at this step.
        -- If this step completed, use the success continuation to
        -- return the result.  Only in the first iteration will we
        -- finally return a `NoWideningRequired`.  In other cases, we
        -- had to widen at least once.
        case res of
          WideningError msg locs _postD' ->
            do traceBundle bundle "== Widening error! =="
               traceBundle bundle msg
               traceBundle bundle "Partial widening at locations:"
               traceBundle bundle (show locs)
{-
               traceBundle bundle "===== PREDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody preD)))
               traceBundle bundle "===== POSTDOMAIN ====="
               traceBundle bundle (show (PEE.ppEquivalenceDomain W4.printSymExpr (PS.specBody postD')))
-}
               return res

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
               widenLoop sym bak (Gas (i-1)) eqCtx postD' newlocs


widenUsingCounterexample ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  Maybe (WidenLocs sym arch) ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
widenUsingCounterexample sym evalFn bundle eqCtx postCondAsm postCondStatePred preD mlocs postD =
  tryWidenings
    [ widenRegisters sym evalFn bundle eqCtx postCondAsm postCondStatePred postD
    , widenStack sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD
    , widenHeap sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD
    , return $ WideningError "Could not find any values to widen!" (fromMaybe mempty mlocs) postD
    ]


-- TODO, lots of code duplication between the stack and heap cases.
--  should we find some generalization?
widenHeap ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenHeap sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD =
  do xs <- findUnequalHeapMemCells sym evalFn bundle eqCtx preD
     ys <- findUnequalHeapWrites sym evalFn bundle eqCtx
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
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenStack sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD =
  do xs <- findUnequalStackMemCells sym evalFn bundle eqCtx preD
     ys <- findUnequalStackWrites sym evalFn bundle eqCtx
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
  EquivContext sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalHeapWrites sym evalFn bundle eqCtx =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym footprints (W4.falsePred sym))
     execWriterT $ forM_ memWrites $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquivMem sym eqCtx oPostState pPostState cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalStackWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalStackWrites sym evalFn bundle eqCtx =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym footprints (W4.falsePred sym))
     execWriterT $ forM_ memWrites $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquivStack sym eqCtx oPostState pPostState cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalHeapMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  AbstractDomain sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalHeapMemCells sym evalFn bundle eqCtx preD =
  do let prestateHeapCells = PEM.toList (PEE.eqDomainGlobalMemory (PS.specBody preD))
     let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     execWriterT $ forM_ prestateHeapCells $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquivMem sym eqCtx oPostState pPostState cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

findUnequalStackMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  AbstractDomain sym arch ->
  IO [Some (PMc.MemCell sym arch)]
findUnequalStackMemCells sym evalFn bundle eqCtx preD =
  do let prestateStackCells = PEM.toList (PEE.eqDomainStackMemory (PS.specBody preD))
     let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     execWriterT $ forM_ prestateStackCells $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquivStack sym eqCtx oPostState pPostState cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

widenRegisters ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch ->
  IO (WidenResult sym arch)
-- TODO, should we be using the postCondAsm?
widenRegisters sym evalFn bundle eqCtx _postCondAsm postCondStatePred postD =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     newRegs <- findUnequalRegs sym evalFn eqCtx
                   (PEE.eqDomainRegisters postCondStatePred)
                   (PS.simRegs oPostState)
                   (PS.simRegs pPostState)

     if null newRegs then
       return NoWideningRequired
     else
       -- TODO, widen less aggressively using the path condition or something?
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
  EquivContext sym arch ->
  PER.RegisterDomain sym arch ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  IO [Some (MM.ArchReg arch)]
findUnequalRegs sym evalFn eqCtx regPred oRegs pRegs =
  execWriterT $ MM.traverseRegsWith_
    (\regName oRegVal ->
         do let pRegVal = MM.getBoundValue regName pRegs
            let pRegEq  = PER.registerInDomain sym regName regPred
            regEq <- liftIO (W4.groundEval evalFn pRegEq)
            when regEq $
              do isEqPred <- liftIO (registerValuesEqual sym eqCtx regName oRegVal pRegVal)
                 isEq <- liftIO (W4.groundEval evalFn isEqPred)
                 when (not isEq) (tell [Some regName]))
    oRegs
