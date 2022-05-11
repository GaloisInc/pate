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

import           Control.Monad (when, forM_, unless, filterM)
import           Control.Monad.IO.Class
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Reader (asks)
import           Control.Monad.Writer (tell, execWriterT)

import           Prettyprinter

import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

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
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Proof.Operations as PP
import qualified Pate.Proof.CounterExample as PP
import qualified Pate.Proof.Instances ()

import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT

import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.Solver as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified Pate.Verification.Domain as PVD
import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node ( GraphNode(..) )
import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( AbstractDomain )

-- | Generate a fresh abstract domain value for the given graph node.
--   This should represent the most information we can ever possibly
--   have (i.e., all values are equal) as it will only ever be
--   weakend via widening.
makeFreshAbstractDomain ::
  GraphNode arch ->
  EquivM sym arch (AbstractDomain sym arch)
makeFreshAbstractDomain (GraphNode pPair) = do
  iEqSpec <- PVD.universalDomainSpec pPair
  return $ fmap (\x -> PAD.AbstractDomainBody x Nothing) iEqSpec
makeFreshAbstractDomain (ReturnNode fPair) = do
  -- TODO, this isn't really right, but seems pretty harmless.  The
  -- only thing the concrete block value is used for is to assign more
  -- human-readable names to arguments if we have debug information.
  iEqSpec <- PVD.universalDomainSpec (TF.fmapF PB.functionEntryToConcreteBlock fPair)
  return $ fmap (\x -> PAD.AbstractDomainBody x Nothing) iEqSpec

-- | Given the results of symbolic execution, and an edge in the pair graph
--   to consider, compute an updated abstract domain for the target node,
--   and update the pair graph, if necessary.
--
--   This is done by looking up the abstract domain for the target node
--   and proving that the poststate of symbolic execution satisfies
--   the abstract domain of the target node, assuming the abstract domain of
--   the source node.  If this is not the case, we use the resulting counterexample
--   to determine what additional locations need to be added to the target
--   abstract domain. We perform these widening steps in a loop until
--   the process converges or we run out of gas.
--
--   When widening, we first consider register values to widen, then we look at
--   stack, and finally global memory for locations. When widening memory, we
--   consider first locations that differ in the prestate, then locations that
--   were written during the execution of the block.  In theory, this should be
--   enough to account for all the sources of differences we have to consider.
--   Probably, the order in which we consider these effects doesn't matter much,
--   except perhaps if the widening process is aborted early (we run out of gas).
--
--   If, for some reason, we cannot find appropraite locations to widen, we
--   widen as much as we can, and report an error.
widenAlongEdge ::
  SimBundle sym arch {- ^ results of symbolic execution for this block -} ->
  GraphNode arch {- ^ source node -} ->
  AbstractDomain sym arch {- ^ source abstract domain -} ->
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ target graph node -} ->
  EquivM sym arch (PairGraph sym arch)
widenAlongEdge bundle from d gr to =

  case getCurrentDomain gr to of
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
            do let msg' = ("Error during widening: " ++ msg)
               traceBundle bundle msg'
               return $ recordMiscAnalysisError (freshDomain gr to d'') to (Text.pack msg')
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
            do let msg' = ("Error during widening: " ++ msg)
               traceBundle bundle msg'
               case updateDomain gr from to d'' of
                 Left gr' ->
                   do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                      return $ recordMiscAnalysisError gr' to (Text.pack msg')
                 Right gr' -> return $ recordMiscAnalysisError gr' to (Text.pack msg')

          Widen _ d'' ->
            case updateDomain gr from to d'' of
              Left gr' ->
                do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                   return gr'
              Right gr' -> return gr'


-- | Information about what locations were widened
data WidenLocs sym arch =
  WidenLocs
    (Set (Some (MM.ArchReg arch)))
    (Set (Some (PMc.MemCell sym arch)))

instance (W4.IsSymExprBuilder sym, PA.ValidArch arch) => Show (WidenLocs sym arch) where
  show (WidenLocs regs cells) =
    unlines $
      [ unwords (map show (Set.toList regs)) ] ++
      [ show (PMc.ppCell c)
      | Some c <- Set.toList cells
      ]

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Semigroup (WidenLocs sym arch) where
  (WidenLocs r1 m1) <> (WidenLocs r2 m2) = WidenLocs (r1 <> r2) (m1 <> m2)

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Monoid (WidenLocs sym arch) where
  mempty = WidenLocs mempty mempty

-- Result of attempting to widen.  Errors can occur for a couple of reasons:
-- UNKNOWN results from solvers; running out of gas in the widening loop,
-- or being unable to decide how to peform a widening step when a
-- counterexample is found.
data WidenResult sym arch
  = NoWideningRequired
  | WideningError String (WidenLocs sym arch) (AbstractDomain sym arch)
  | Widen (WidenLocs sym arch) (AbstractDomain sym arch)

-- | Try the given widening strategies one at a time,
--   until the first one that computes some nontrival
--   widening, or returns an error.
tryWidenings :: Monad m =>
  [m (WidenResult sym arch)] ->
  m (WidenResult sym arch)
tryWidenings [] = return NoWideningRequired
tryWidenings (x:xs) =
  x >>= \case
    NoWideningRequired -> tryWidenings xs
    res -> return res


-- | This gives a fixed amount of gas for traversing the
--   widening loop. Setting this value too low seems to
--   cause widening failures even for fairly reasonable
--   cases, so this is larger than the amount of gas
--   provided for the overall pair graph updates.
localWideningGas :: Gas
localWideningGas = Gas 100


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
         asm1 <- PS.getAssumedPred sym asmFrame
         let asm2 = PS.specAsm preD
         asm <- W4.andPred sym asm1 asm2
         absDomPred <- PAD.absDomainToPrecond sym eqCtx bundle (PS.specBody preD)
         W4.andPred sym asm absDomPred

       traceBundle bundle "Entering widening loop"

       PS.withOnlineSolver solver saveInteraction sym $ \bak ->
         do liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
              do -- NB, this `push` is here to avoid
                 -- https://github.com/GaloisInc/what4/issues/196
                 W4.push sp
                 W4.assume (W4.solverConn sp) precond
            widenLoop sym bak localWideningGas eqCtx postD0 Nothing

 where
   doPanic = panic Solver "widenPostcondition" ["Online solving not enabled"]



   -- The main widening loop. For now, we constrain it's iteration with a Gas parameter.
   -- In principle, I think this shouldn't be necessary, so we should revisit at some point.
   --
   -- The basic strategy here is to ask the solver to prove that the current post-condition
   -- abstract domain is sufficent to describe the post state when we assume the pre-condition
   -- abstract domain.  If it can do so, we are done. If not, then we have a counterexample
   -- in hand that we can use to decide how to widen the current post-domain and try again.
   -- `widenUsingCounterexample` uses a fixed list of heuristics to decide how to do the widening.
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
     Maybe (WidenLocs sym arch)
     {- ^ A summary of any widenings that were done in previous iterations.
          If @Nothing@, than no previous widenings have been performed. -} ->
     EquivM sym arch (WidenResult sym arch)

   widenLoop sym bak (Gas i) eqCtx postD mlocs =
     do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
        let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))
        (postCondAsm, postDomBody) <- liftIO (PS.bindSpec sym oPostState pPostState postD)

        res <- IO.withRunInIO $ \inIO ->
          liftIO $ LCBO.withSolverProcess bak doPanic $ \sp ->
            W4.inNewFrame sp $
            do let conn = W4.solverConn sp

               -- Assume the validity conditions coming outof the postdomain spec.
               -- TODO? Should we do this, or are these conditions irrelevant?
               W4.assume conn postCondAsm

               postDomBody' <- getInitalAbsDomainVals sym sp bundle postDomBody
               eqPostPred <- PAD.absDomainToPostCond sym eqCtx bundle postDomBody'

               -- check if we already satisfy the equality condition
               W4.assume conn =<< W4.notPred sym eqPostPred

               W4.checkAndGetModel sp "prove postcondition" >>= \case
                 Unsat _ -> return NoWideningRequired
                 Unknown -> return (WideningError "UNKNOWN result evaluating postcondition" (fromMaybe mempty mlocs) postD)
                 Sat evalFn ->
                   if i <= 0 then inIO $
                     -- we ran out of gas
                     do slice <- PP.simBundleToSlice bundle
                        ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState (PAD.absDomEq $ PS.specBody preD) (PAD.absDomEq $ PS.specBody postD) slice (SymGroundEvalFn evalFn)
                        let msg = unlines [ "Ran out of gas performing local widenings"
                                          , show (pretty ineqRes)
                                          ]
                        return $ WideningError msg (fromMaybe mempty mlocs) postD
                   else
                     -- The current execution does not satisfy the postcondition, and we have
                     -- a counterexample.
                     inIO (widenUsingCounterexample sym evalFn bundle eqCtx postCondAsm (PAD.absDomEq postDomBody) preD mlocs postD)

        -- Re-enter the widening loop if we had to widen at this step.
        --
        -- If we did not have to widen in this iteration, and no widening
        -- was done in previous iterations (i.e., this is the first iteration)
        -- return `NoWideningRequired`.  Otherwise return the new abstract domain
        -- and a summary of the widenings we did.
        case res of

          -- Some kind of error occured while widening.
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

          -- In this iteration, no additional widening was done, and we can exit the loop.
          -- The ultimate result we return depends on if we did any widening steps in
          -- previous iterations.
          NoWideningRequired ->
            case mlocs of
              Nothing   -> return NoWideningRequired
              Just locs -> return (Widen locs postD)

          -- We had to do some widening in this iteration, so reenter the loop.
          Widen locs postD' ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show locs)
               let newlocs = case mlocs of
                               Nothing    -> locs
                               Just locs' -> locs <> locs'
               widenLoop sym bak (Gas (i-1)) eqCtx postD' (Just newlocs)

-- | Refine a given 'AbstractDomainBody' to contain concrete values for some
-- model.
getInitalAbsDomainVals ::
  forall sym t solver st fs arch sp.
  ( sp ~ W4.SolverProcess t solver
  , sym ~ W4.ExprBuilder t st fs
  , W4.OnlineSolver solver
  , PA.ValidArch arch ) =>
  sym ->
  sp ->
  SimBundle sym arch ->
  PAD.AbstractDomainBody sym arch ->
  IO (PAD.AbstractDomainBody sym arch)
getInitalAbsDomainVals sym sp bundle absDom = case PAD.absDomVals absDom of
  Just _ -> return absDom
  Nothing -> do
    W4.checkAndGetModel sp "getInitalAbsDomainVals" >>= \case
      -- TODO: throw an error here?
      Unsat _ -> return absDom
      Unknown -> return absDom
      Sat evalFn -> do
        let
          getRange :: forall tp. W4.SymExpr sym tp -> IO (PAD.AbsRange tp)
          getRange e = do
            g <- W4.groundEval evalFn e
            return $ PAD.groundToAbsRange (W4.exprType e) g
        initO <- PAD.initAbsDomainVals sym getRange (PS.simOutO bundle)
        initP <- PAD.initAbsDomainVals sym getRange (PS.simOutP bundle)
        return $ absDom { PAD.absDomVals = Just (PPa.PatchPair initO initP) }

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
  EquivM sym arch (WidenResult sym arch)
widenUsingCounterexample sym evalFn bundle eqCtx postCondAsm postCondStatePred preD mlocs postD =
  tryWidenings
    [ -- First check for any disagreement in the constant values
      widenValues sym evalFn bundle postD

    , widenRegisters sym evalFn bundle eqCtx postCondAsm postCondStatePred postD

      -- We first attempt to widen using writes that occured in the current CFAR/slice
      -- as these are most likely to be relevant.
    , widenStack sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD LocalChunkWrite
    , widenHeap sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD LocalChunkWrite

      -- After that, we check for widenings relating to the precondition, i.e., frame conditions.
    , widenStack sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD PreDomainCell
    , widenHeap sym evalFn bundle eqCtx postCondAsm postCondStatePred preD postD PreDomainCell


    , do slice <- PP.simBundleToSlice bundle
         ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState
                         (PAD.absDomEq $ PS.specBody preD) (PAD.absDomEq $ PS.specBody postD) slice (SymGroundEvalFn evalFn)
         let msg = unlines [ "Could not find any values to widen!"
                           , show (pretty ineqRes)
                           ]
         return $ WideningError msg (fromMaybe mempty mlocs) postD
    ]

data MemCellSource = LocalChunkWrite | PreDomainCell

widenValues ::
  forall sym t st fs arch.
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  AbstractDomain sym arch ->
  EquivM sym arch (WidenResult sym arch)
widenValues sym evalFn bundle postD = do
  (postD', mlocs) <- PAD.widenAbsDomainVals sym (PS.specBody postD) getRange bundle
  case mlocs of
    Just (PAD.RelaxLocs regLocs memLocs) ->
      if regLocs == mempty && memLocs == mempty then
        return NoWideningRequired
      else
        return $ Widen (WidenLocs regLocs memLocs) (postD { PS.specBody = postD' })
    Nothing -> return $ WideningError "widenValues" mempty postD
  where
     getRange :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (PAD.AbsRange tp)
     getRange e = liftIO $ do
       g <- W4.groundEval evalFn e
       return $ PAD.groundToAbsRange (W4.exprType e) g

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
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenHeap sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalHeapWrites sym evalFn bundle eqCtx
             PreDomainCell   -> findUnequalHeapMemCells sym evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainGlobalMemory (PAD.absDomEq $ PS.specBody postD)) xs

     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PMc.predFromList sym [ (c, W4.truePred sym) | c <- zs ]
          let heapDom = PEM.memDomainPred (PEE.eqDomainGlobalMemory (PAD.absDomEq $ PS.specBody postD))
          heapDom' <- liftIO $ PMc.mergeMemCellPred sym heapDom newCells
          let md' = (PEE.eqDomainGlobalMemory (PAD.absDomEq $ PS.specBody postD)){ PEM.memDomainPred = heapDom' }
          let pred' = (PAD.absDomEq $ PS.specBody postD){ PEE.eqDomainGlobalMemory = md' }
          let postD' = fmap (\x -> x { PAD.absDomEq = pred' }) postD
          return (Widen (WidenLocs mempty (Set.fromList zs)) postD')


-- | Only return those cells not already excluded by the postdomain
filterCells :: forall sym t st fs arch.
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  PEM.MemoryDomain sym arch ->
  [Some (PMc.MemCell sym arch)] ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
filterCells sym evalFn memDom xs = filterM filterCell xs
  where
    filterCell (Some c) =
      liftIO (W4.groundEval evalFn =<< PEM.containsCell sym memDom c)

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
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenStack sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalStackWrites sym evalFn bundle eqCtx
             PreDomainCell   -> findUnequalStackMemCells sym evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainStackMemory (PAD.absDomEq $ PS.specBody postD)) xs
     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PMc.predFromList sym [ (c, W4.truePred sym) | c <- zs ]
          let stackDom = PEM.memDomainPred (PEE.eqDomainStackMemory (PAD.absDomEq $ PS.specBody postD))
          stackDom' <- liftIO $ PMc.mergeMemCellPred sym stackDom newCells
          let md' = (PEE.eqDomainStackMemory (PAD.absDomEq $ PS.specBody postD)){ PEM.memDomainPred = stackDom' }
          let pred' = (PAD.absDomEq $ PS.specBody postD){ PEE.eqDomainStackMemory = md' }
          let postD' = fmap (\x -> x { PAD.absDomEq = pred' }) postD
          return (Widen (WidenLocs mempty (Set.fromList zs)) postD')


-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalHeapWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
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

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
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

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalHeapMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  AbstractDomain sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalHeapMemCells sym evalFn bundle eqCtx preD =
  do let prestateHeapCells = PEM.toList (PEE.eqDomainGlobalMemory (PAD.absDomEq $ PS.specBody preD))
     let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     execWriterT $ forM_ prestateHeapCells $ \(Some cell, cond) ->
       do cellEq <- liftIO $ resolveCellEquivMem sym eqCtx oPostState pPostState cell cond
          cellEq' <- liftIO $ W4.groundEval evalFn cellEq
          unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackMemCells ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch ->
  EquivContext sym arch ->
  AbstractDomain sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalStackMemCells sym evalFn bundle eqCtx preD =
  do let prestateStackCells = PEM.toList (PEE.eqDomainStackMemory (PAD.absDomEq $ PS.specBody preD))
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
  EquivM sym arch (WidenResult sym arch)
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
                     (PEE.eqDomainRegisters (PAD.absDomEq $ PS.specBody postD))
                     newRegs
           pred' = (PAD.absDomEq $ PS.specBody postD)
                   { PEE.eqDomainRegisters = regs'
                   }
           postD' = fmap (\x -> x { PAD.absDomEq = pred' }) postD
           locs = WidenLocs (Set.fromList newRegs) mempty
        in return (Widen locs postD')


-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalRegs ::
  ( PA.ValidArch arch
  , sym ~ W4.ExprBuilder t st fs ) =>
  sym ->
  W4.GroundEvalFn t ->
  EquivContext sym arch ->
  PER.RegisterDomain sym arch ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  EquivM sym arch [Some (MM.ArchReg arch)]
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
