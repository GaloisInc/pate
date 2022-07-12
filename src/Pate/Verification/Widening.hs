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
import           Control.Monad.Writer (tell, execWriterT)
import qualified Control.Monad.Reader as CMR
import           Control.Monad.Trans.Maybe
import           Control.Applicative ( (<|>) )
import           Control.Monad.Trans.Class ( lift )

import           Prettyprinter

import qualified Data.Set as Set
import qualified Data.Text as Text

import           Data.Parameterized.Classes()
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Protocol.Online as W4
import qualified What4.Protocol.SMTWriter as W4 hiding (bvAdd)
import           What4.SatResult (SatResult(..))

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO

import qualified Data.Macaw.CFG as MM

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
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

import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Config as PC

import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.Concretize as PVC
import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node ( GraphNode(..) )
import qualified Pate.Verification.AbstractDomain as PAD
import           Pate.Verification.AbstractDomain ( WidenLocs(..) )

-- | Generate a fresh abstract domain value for the given graph node.
--   This should represent the most information we can ever possibly
--   have (i.e., all values are equal) as it will only ever be
--   weakend via widening.
makeFreshAbstractDomain ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  GraphNode arch {- ^ source node -} ->
  GraphNode arch {- ^ target graph node -} ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
makeFreshAbstractDomain scope bundle preDom from to = do
  dom <- case from of
    GraphNode{} -> do
      initDom <- initialDomain
      vals <- withOnlineBackend $ \bak ->
        liftIO $ getInitalAbsDomainVals bak bundle preDom
      return $ initDom { PAD.absDomVals = vals }
    ReturnNode{} -> do
      initDom <- initialDomain
      -- as a small optimization, we know that the return nodes leave the values
      -- unmodified, and therefore any previously-established value constraints
      -- will still hold
      return $ initDom { PAD.absDomVals = PAD.absDomVals preDom }
  postSpec <- initialDomainSpec to
  abstractOverVars scope bundle from to postSpec dom

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
  PS.SimScope sym arch v ->
  SimBundle sym arch v {- ^ results of symbolic execution for this block -} ->
  GraphNode arch {- ^ source node -} ->
  AbstractDomain sym arch v {- ^ source abstract domain -} ->
  PairGraph sym arch {- ^ pair graph to update -} ->
  GraphNode arch {- ^ target graph node -} ->
  EquivM sym arch (PairGraph sym arch)
widenAlongEdge scope bundle from d gr to = withSym $ \sym ->

  case getCurrentDomain gr to of
    -- This is the first time we have discovered this location
    Nothing ->
     do traceBundle bundle ("First jump to " ++ show to)
        -- initial state of the pair graph: choose the universal domain that equates as much as possible
        postSpec <- makeFreshAbstractDomain scope bundle d from to
        -- Here we need 'PS.bindSpec' just to make the types match up - see the usage
        -- below for where it's actually useful.
        (asm, d') <- liftIO $ PS.bindSpec sym (PS.bundleOutVars bundle) postSpec
        withAssumptionSet asm $ do
          md <- widenPostcondition bundle d d'
          case md of
            NoWideningRequired -> 
              return (freshDomain gr to postSpec)
            WideningError msg _ d'' ->
              do let msg' = ("Error during widening: " ++ msg)
                 traceBundle bundle msg'
                 postSpec' <- abstractOverVars scope bundle from to postSpec d''
                 return $ recordMiscAnalysisError (freshDomain gr to postSpec') to (Text.pack msg')
            Widen _ _ d'' -> do
              postSpec' <- abstractOverVars scope bundle from to postSpec d''
              return (freshDomain gr to postSpec')

    -- have visited this location at least once before
    Just postSpec -> do
      -- The variables in 'postSpec' represent the final values in the
      -- post-state of the slice (which have been abstracted out by 'abstractOverVars').
      -- To put everything in the same scope, we need to bind these variables to
      -- the post-state expressions that we have currently as the result of symbolic
      -- execution (i.e. the resulting state in 'SimOutput').
      --
      -- The result is a post-domain describing the proof target (i.e. d'), that
      -- has been brought into the current scope 'v' (as the bound variables in the output
      -- expressions are still in this scope).
      --
      -- After widening, this needs to be re-phrased with respect to the final
      -- values of the slice again. This is accomplised by 'abstractOverVars', which
      -- produces the final 'AbstractDomainSpec' that has been fully abstracted away
      -- from the current scope and can be stored as the updated domain in the 'PairGraph'
      (asm, d') <- liftIO $ PS.bindSpec sym (PS.bundleOutVars bundle) postSpec
      withAssumptionSet asm $ do
        md <- widenPostcondition bundle d d'
        case md of
          NoWideningRequired ->
            do traceBundle bundle "Did not need to widen"
               return gr

          WideningError msg _ d'' ->
            do let msg' = ("Error during widening: " ++ msg)
               traceBundle bundle msg'
               postSpec' <- abstractOverVars scope bundle from to postSpec d''
               case updateDomain gr from to postSpec' of
                 Left gr' ->
                   do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                      return $ recordMiscAnalysisError gr' to (Text.pack msg')
                 Right gr' -> return $ recordMiscAnalysisError gr' to (Text.pack msg')

          Widen _ _ d'' -> do
            postSpec' <- abstractOverVars scope bundle from to postSpec d''
            case updateDomain gr from to postSpec' of
              Left gr' ->
                do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                   return gr'
              Right gr' -> return gr'


abstractOverVars ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  GraphNode arch {- ^ source node -} ->
  GraphNode arch {- ^ target graph node -} ->
  PAD.AbstractDomainSpec sym arch {- ^ previous post-domain -} ->
  PAD.AbstractDomain sym arch v {- ^ computed post-domain -} ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
abstractOverVars scope_v bundle _from _to postSpec postResult = withSym $ \sym -> do
  -- the post-state of the slice phrased over 'v'
  let outVars = PS.bundleOutVars bundle

  PS.forSpec postSpec $ \(scope_v' :: PS.SimScope sym arch v') _body -> do
    -- the variables representing the post-state (i.e. the target scope)
    let postVars = PS.scopeVars scope_v'

    -- rewrite v'-scoped terms into v-scoped terms that represent
    -- the result of symbolic execution (i.e. formally stating that
    -- the initial bound variables of v' are equal to the results
    -- of symbolic execution)
    v'_to_v <- liftIO $ PS.getExprRewrite sym scope_v' outVars

    -- Rewrite a v-scoped term to a v'-scoped term by simply swapping
    -- out the bound variables
    v_to_v' <- liftIO $ PS.getExprRewrite sym scope_v postVars
    let
      asScopedConst :: forall v1 v2 tp. W4.Pred sym -> PS.ScopedExpr sym tp v1 -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp v2)
      asScopedConst asm se = do
        Just c <- lift $ withOnlineBackend $ \bak -> withSolverProcess $ \sp ->
          liftIO $ W4.inNewFrame sp $ do
            W4.assume (W4.solverConn sp) asm
            W4.asConcrete <$>
              PVC.resolveSingletonSymbolicAsDefault bak (PS.unSE se)
        liftIO $ PS.concreteScope @v2 sym c

      asStackOffset :: forall bin tp. PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym tp v -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp v')
      asStackOffset bin se = do
        W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
        Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))

        -- se[v]
        let postFrame = PS.simStackBase $ PS.simVarState $ (PPa.getPair' bin postVars)
        off <- liftIO $ PS.liftScope0 @v' sym (\sym' -> W4.freshConstant sym' (W4.safeSymbol "frame_offset") (W4.BaseBVRepr w))
        -- asFrameOffset := frame[v'] + off
        asFrameOffset <- liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off
        -- asFrameOffset' := frame[v'/f(v)] + off
        asFrameOffset' <- liftIO $ PS.applyExprRewrite sym v'_to_v asFrameOffset
        -- asm := se == frame[v'/f(v)] + off
        asm <- liftIO $ PS.liftScope2 sym W4.isEq se asFrameOffset'
        -- assuming 'asm', is 'off' constant?
        off' <- asScopedConst (PS.unSE asm) off
        lift $ traceBundle bundle (show $ W4.printSymExpr (PS.unSE off'))
        -- return frame[v'] + off
        liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off'

      asSimpleAssign :: forall tp. PS.ScopedExpr sym tp v -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym tp v')
      asSimpleAssign se = do
        -- se[v]
        -- se' := se[v/v']
        se' <- liftIO $ PS.applyExprRewrite sym v_to_v' se
        -- e'' := se[v/f(v)]
        e'' <- liftIO $ PS.applyExprRewrite sym v'_to_v se'
        -- se is the original value, and e'' is the value rewritten
        -- to be phrased over the post-state
        heuristicTimeout <- lift $ CMR.asks (PC.cfgHeuristicTimeout . envConfig)
        asm <- liftIO $ PS.liftScope2 sym W4.isEq se e''
        True <- lift $ isPredTrue' heuristicTimeout (PS.unSE asm)
        return se'

    PS.scopedExprMap sym postResult $ \(se :: PS.ScopedExpr sym tp v) -> do
      mres <- runMaybeT $
            asScopedConst (W4.truePred sym) se
        <|> asStackOffset PBi.OriginalRepr se
        <|> asStackOffset PBi.PatchedRepr se
        <|> asSimpleAssign se
      case mres of
        Just se' -> return se'
        -- FIXME: add graceful failure mode
        Nothing -> fail $ "Unable to rescope"

-- | Classifying what kind of widening has occurred
data WidenKind =
    WidenValue -- ^ constant values disagree in the value domain
  | WidenEquality -- ^ values disagree between the original and patched binaries

-- Result of attempting to widen.  Errors can occur for a couple of reasons:
-- UNKNOWN results from solvers; running out of gas in the widening loop,
-- or being unable to decide how to peform a widening step when a
-- counterexample is found.
data WidenResult sym arch v
  = NoWideningRequired
  | WideningError String (WidenLocs sym arch) (AbstractDomain sym arch v)
  | Widen WidenKind (WidenLocs sym arch) (AbstractDomain sym arch v)

-- | Try the given widening strategies one at a time,
--   until the first one that computes some nontrival
--   widening, or returns an error.
tryWidenings :: Monad m =>
  [m (WidenResult sym arch v)] ->
  m (WidenResult sym arch v)
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

widenPostcondition ::
  forall sym arch v.
  SimBundle sym arch v ->
  AbstractDomain sym arch v {- ^ predomain -} ->
  AbstractDomain sym arch v {- ^ postdomain -} ->
  EquivM sym arch (WidenResult sym arch v)
widenPostcondition bundle preD postD0 =
  withSym $ \sym -> do
    eqCtx <- equivalenceContext
    traceBundle bundle "Entering widening loop"
    widenLoop sym localWideningGas eqCtx postD0 Nothing

 where
   -- The main widening loop. For now, we constrain it's iteration with a Gas parameter.
   -- In principle, I think this shouldn't be necessary, so we should revisit at some point.
   --
   -- The basic strategy here is to ask the solver to prove that the current post-condition
   -- abstract domain is sufficent to describe the post state when we assume the pre-condition
   -- abstract domain.  If it can do so, we are done. If not, then we have a counterexample
   -- in hand that we can use to decide how to widen the current post-domain and try again.
   -- `widenUsingCounterexample` uses a fixed list of heuristics to decide how to do the widening.
   widenLoop ::
     sym ->
     Gas ->
     EquivContext sym arch ->
     AbstractDomain sym arch v ->
     Maybe (WidenResult sym arch v)
     {- ^ A summary of any widenings that were done in previous iterations.
          If @Nothing@, than no previous widenings have been performed. -} ->
     EquivM sym arch (WidenResult sym arch v)

   widenLoop sym (Gas i) eqCtx postD mPrevRes =
     do let prevLocs = case mPrevRes of
              Just (Widen _ locs _) -> locs
              _ -> mempty
        -- no rebinding necessary yet
        let postDomBody = postD
        --(postCondAsm, postDomBody) <- liftIO (PS.bindSpec sym oPostState pPostState postD)
        -- TODO: It is likely useful to separate checking the equality and value domains, rather
        -- than checking them simultaneously here. The plan is to change this check to instead
        -- iterate over the domain and check each location individually
        -- (see: https://github.com/GaloisInc/pate/issues/287), so we should revisit how to separate
        -- these checks at that point.
        eqPostPred <- liftIO $ PAD.absDomainToPostCond sym eqCtx bundle preD postDomBody
        res <- withSolverProcess $ \sp -> IO.withRunInIO $ \inIO -> W4.inNewFrame sp $ do
          let conn = W4.solverConn sp

          -- check if we already satisfy the equality condition
          W4.assume conn =<< W4.notPred sym eqPostPred

          W4.checkAndGetModel sp "prove postcondition" >>= \case
            Unsat _ -> return NoWideningRequired
            Unknown -> return (WideningError "UNKNOWN result evaluating postcondition" prevLocs postD)
            Sat evalFn -> 
              if i <= 0 then inIO $
                -- we ran out of gas
                do slice <- PP.simBundleToSlice bundle
                   ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice (SymGroundEvalFn evalFn)
                   let msg = unlines [ "Ran out of gas performing local widenings"
                                     , show (pretty ineqRes)
                                     ]
                   return $ WideningError msg prevLocs postD
              else
                -- The current execution does not satisfy the postcondition, and we have
                -- a counterexample.
                -- FIXME: postCondAsm doesn't exist anymore, but needs to be factored
                -- out still
                inIO (widenUsingCounterexample sym evalFn bundle eqCtx (W4.truePred sym) (PAD.absDomEq postDomBody) preD prevLocs postD)

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
            case mPrevRes of
              Nothing   -> return NoWideningRequired
              Just prevRes -> return prevRes

          -- We had to do some widening in this iteration, so reenter the loop.
          Widen widenK locs postD' ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show locs)
               let newlocs = locs <> prevLocs
               widenLoop sym (Gas (i-1)) eqCtx postD' (Just $ Widen widenK newlocs postD')

-- | Refine a given 'AbstractDomainBody' to contain concrete values for the
-- output of symbolic execution, where possible.
-- Uses the default concretization strategies from 'Pate.Verification.Concretize'
getInitalAbsDomainVals ::
  forall sym t solver st fs v arch.
  ( LCB.IsSymInterface sym
  , sym ~ W4.ExprBuilder t st fs
  , W4.OnlineSolver solver
  , PA.ValidArch arch ) =>
  LCBO.OnlineBackend solver t st fs ->
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  IO (PPa.PatchPair (PAD.AbstractDomainVals sym arch))
getInitalAbsDomainVals bak bundle preDom = do
  let
    sym = LCB.backendGetSym bak
    getConcreteRange :: forall tp. W4.SymExpr sym tp -> IO (PAD.AbsRange tp)
    getConcreteRange e = do
      e' <- PVC.resolveSingletonSymbolicAsDefault bak e
      return $ PAD.extractAbsRange sym e'

  let PPa.PatchPair preO preP = PAD.absDomVals preDom
  initO <- PAD.initAbsDomainVals sym getConcreteRange (PS.simOutO bundle) preO
  initP <- PAD.initAbsDomainVals sym getConcreteRange (PS.simOutP bundle) preP
  return $ PPa.PatchPair initO initP

widenUsingCounterexample ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  WidenLocs sym arch {- ^ previous widening -}   ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenUsingCounterexample sym evalFn bundle eqCtx postCondAsm postCondStatePred preD prevLocs postD =
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
                         (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice (SymGroundEvalFn evalFn)
         let msg = unlines [ "Could not find any values to widen!"
                           , show (pretty ineqRes)
                           ]
         return $ WideningError msg prevLocs postD
    ]

data MemCellSource = LocalChunkWrite | PreDomainCell

widenValues ::
  forall sym t st fs arch v.
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenValues sym evalFn bundle postD = do
  (postD', mlocs) <- PAD.widenAbsDomainVals sym postD getRange bundle
  case mlocs of
    Just (WidenLocs regLocs memLocs) ->
      if regLocs == mempty && memLocs == mempty then
        return NoWideningRequired
      else
        return $ Widen WidenValue (WidenLocs regLocs memLocs) postD'
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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch v)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenHeap sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalHeapWrites sym evalFn bundle eqCtx
             PreDomainCell   -> findUnequalHeapMemCells sym evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainGlobalMemory (PAD.absDomEq postD)) xs

     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- zs ]
          let heapDom = PEE.eqDomainGlobalMemory (PAD.absDomEq $ postD)
          heapDom' <- liftIO $ PEM.intersect sym heapDom newCells
          let pred' = (PAD.absDomEq postD){ PEE.eqDomainGlobalMemory = heapDom' }
          let postD' = postD { PAD.absDomEq = pred' }
          return (Widen WidenEquality (WidenLocs mempty (Set.fromList zs)) postD')


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
      liftIO (W4.groundEval evalFn =<< PEM.mayContainCell sym memDom c)

widenStack ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  MemCellSource ->
  EquivM sym arch (WidenResult sym arch v)
-- TODO? should we be using postCondAsm and postConstStatePred?
widenStack sym evalFn bundle eqCtx _postCondAsm _postCondStatePred preD postD memCellSource =
  do xs <- case memCellSource of
             LocalChunkWrite -> findUnequalStackWrites sym evalFn bundle eqCtx
             PreDomainCell   -> findUnequalStackMemCells sym evalFn bundle eqCtx preD
     zs <- filterCells sym evalFn (PEE.eqDomainStackMemory (PAD.absDomEq postD)) xs
     if null zs then
       return NoWideningRequired
     else
       do -- TODO, this could maybe be less aggressive
          newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- zs ]
          let stackDom = PEE.eqDomainStackMemory (PAD.absDomEq postD)
          stackDom' <- liftIO $ PEM.intersect sym stackDom newCells
          let pred' = (PAD.absDomEq $ postD){ PEE.eqDomainStackMemory = stackDom' }
          let postD' = postD { PAD.absDomEq = pred' }
          return (Widen WidenEquality (WidenLocs mempty (Set.fromList zs)) postD')


-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalHeapWrites ::
  ( sym ~ W4.ExprBuilder t st fs
  , PA.ValidArch arch ) =>
  sym ->
  W4.GroundEvalFn t ->
  SimBundle sym arch v ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalHeapWrites sym evalFn bundle eqCtx =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (Set.filter (MT.isDir MT.Write) footprints))
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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalStackWrites sym evalFn bundle eqCtx =
  do let oPostState = PS.simOutState (PPa.pOriginal (PS.simOut bundle))
     let pPostState = PS.simOutState (PPa.pPatched  (PS.simOut bundle))

     footO <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutO bundle)
     footP <- liftIO $ MT.traceFootprint sym (PS.simOutMem $ PS.simOutP bundle)
     let footprints = Set.union footO footP
     memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (Set.filter (MT.isDir MT.Write) footprints))
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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalHeapMemCells sym evalFn bundle eqCtx preD =
  do let prestateHeapCells = PEM.toList (PEE.eqDomainGlobalMemory (PAD.absDomEq preD))
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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
findUnequalStackMemCells sym evalFn bundle eqCtx preD =
  do let prestateStackCells = PEM.toList (PEE.eqDomainStackMemory (PAD.absDomEq preD))
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
  SimBundle sym arch v ->
  EquivContext sym arch ->
  W4.Pred sym ->
  PEE.EquivalenceDomain sym arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
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
                     (PEE.eqDomainRegisters (PAD.absDomEq $ postD))
                     newRegs
           pred' = (PAD.absDomEq postD)
                   { PEE.eqDomainRegisters = regs'
                   }
           postD' = postD { PAD.absDomEq = pred' }
           locs = WidenLocs (Set.fromList newRegs) mempty
        in return (Widen WidenEquality locs postD')


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
