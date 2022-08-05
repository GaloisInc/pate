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
{-# LANGUAGE PolyKinds #-}

module Pate.Verification.Widening
  ( widenAlongEdge
  , WidenLocs(..)
  ) where

import           Control.Lens ( (.~), (&) )
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
import           Data.List (foldl')
import           Data.Parameterized.Classes()
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import           What4.SatResult (SatResult(..))

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MT

import           Pate.Panic
import qualified Pate.Binary as PBi
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Location as PL
import qualified Pate.MemCell as PMc
import           Pate.Equivalence as PEq
import qualified Pate.Event as PE
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
  EquivM sym arch (PAD.AbstractDomain sym arch v)
makeFreshAbstractDomain scope bundle preDom from to = do
  case from of
    GraphNode{} -> startTimer $ do
      initDom <- initialDomain
      vals <- getInitalAbsDomainVals bundle preDom
      return $ initDom { PAD.absDomVals = vals }
    ReturnNode{} -> do
      initDom <- initialDomain
      -- as a small optimization, we know that the return nodes leave the values
      -- unmodified, and therefore any previously-established value constraints
      -- will still hold
      return $ initDom { PAD.absDomVals = PAD.absDomVals preDom }

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
        d' <- makeFreshAbstractDomain scope bundle d from to
        postSpec <- initialDomainSpec to
        md <- widenPostcondition bundle d d'
        case md of
          NoWideningRequired -> do
            postSpec' <- abstractOverVars scope bundle from to postSpec d'
            return (freshDomain gr to postSpec')
          WideningError msg _ d'' ->
            do let msg' = ("Error during widening: " ++ msg)
               err <- emitError (PEE.WideningError msg')
               postSpec' <- abstractOverVars scope bundle from to postSpec d''
               return $ recordMiscAnalysisError (freshDomain gr to postSpec') to err
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
               err <- emitError (PEE.WideningError msg')
               postSpec' <- abstractOverVars scope bundle from to postSpec d''
               case updateDomain gr from to postSpec' of
                 Left gr' ->
                   do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                      return $ recordMiscAnalysisError gr' to err
                 Right gr' -> return $ recordMiscAnalysisError gr' to err

          Widen _ _ d'' -> do
            postSpec' <- abstractOverVars scope bundle from to postSpec d''
            case updateDomain gr from to postSpec' of
              Left gr' ->
                do traceBundle bundle ("Ran out of gas while widening postconditon! " ++ show from ++ " " ++ show to)
                   return gr'
              Right gr' -> return gr'

data MaybeF f tp where
  JustF :: f tp -> MaybeF f tp
  NothingF :: MaybeF f tp

runMaybeTF :: Monad m => MaybeT m (a tp) -> m (MaybeF a tp)
runMaybeTF m = runMaybeT m >>= \case
  Just a -> return $ JustF a
  Nothing -> return $ NothingF

toMaybe :: MaybeF a tp -> Maybe (a tp)
toMaybe (JustF a) = Just a
toMaybe NothingF = Nothing

-- | Compute an'PAD.AbstractDomainSpec' from the input 'PAD.AbstractDomain' that is
-- parameterized over the *output* state of the given 'SimBundle'.
-- Until now, the widening process has used the same scope for the pre-domain and
-- post-domain (i.e. both contain free variables corresponding to the initial values
-- before symbolic execution).
-- To abstract the computed post-domain from its calling context, we need to rephrase
-- any symbolic terms it contains so that they only refer to the output state.
-- Specifically, given a post-domain @dom[pre]@ phrased over the pre-state variables, and
-- a function @f(pre)@ representing the result of symbolic execution, we want to compute
-- @dom'[post]@ such that @dom'[post/f(pre)] == dom[pre]@.
--
-- For any given sub-expression in the domain there are multiple possible strategies that
-- can be applied to perform this re-scoping. Here we have a (neccessarily incomplete) list of
-- strategies that are attempted, but in general they may all fail.
-- See: 'PS.StackBase' for a discussion on how this is used to re-scope stack relative
-- accesses
abstractOverVars ::
  forall sym arch pre.
  PS.SimScope sym arch pre  ->
  SimBundle sym arch pre ->
  GraphNode arch {- ^ source node -} ->
  GraphNode arch {- ^ target graph node -} ->
  PAD.AbstractDomainSpec sym arch {- ^ previous post-domain -} ->
  PAD.AbstractDomain sym arch pre {- ^ computed post-domain (with variables from the initial 'pre' scope) -} ->
  EquivM sym arch (PAD.AbstractDomainSpec sym arch)
abstractOverVars scope_pre bundle _from _to postSpec postResult = withSym $ \sym -> do
  -- the post-state of the slice phrased over 'pre'
  let outVars = PS.bundleOutVars bundle

  PS.forSpec postSpec $ \(scope_post :: PS.SimScope sym arch post) _body -> do
    -- the variables representing the post-state (i.e. the target scope)
    let postVars = PS.scopeVars scope_post

    -- rewrite post-scoped terms into pre-scoped terms that represent
    -- the result of symbolic execution (i.e. formally stating that
    -- the initial bound variables of post are equal to the results
    -- of symbolic execution)
    -- e[post] --> e[post/f(pre)]
    -- e.g.
    -- f := sp++;
    -- sp1 + 2 --> (sp0 + 1) + 2
    post_to_pre <- liftIO $ PS.getScopeCoercion sym scope_post outVars

    -- Rewrite a pre-scoped term to a post-scoped term by simply swapping
    -- out the bound variables
    -- e[pre] --> e[pre/post]
    pre_to_post <- liftIO $ PS.getScopeCoercion sym scope_pre postVars

    cache <- W4B.newIdxCache
    -- Strategies for re-scoping expressions
    let
      asConcrete :: forall v1 v2 tp. PS.ScopedExpr sym v1 tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym v2 tp)
      asConcrete se = do
        Just c <- return $ (W4.asConcrete (PS.unSE se))
        liftIO $ PS.concreteScope @v2 sym c

      asScopedConst :: forall v1 v2 tp. W4.Pred sym -> PS.ScopedExpr sym v1 tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym v2 tp)
      asScopedConst asm se = do
        Just c <- lift $ withAssumption asm $
          W4.asConcrete <$> concretizeWithSolver (PS.unSE se)
        liftIO $ PS.concreteScope @v2 sym c

      asStackOffset :: forall bin tp. PBi.WhichBinaryRepr bin -> PS.ScopedExpr sym pre tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym post tp)
      asStackOffset bin se = do
        W4.BaseBVRepr w <- return $ W4.exprType (PS.unSE se)
        Just Refl <- return $ testEquality w (MM.memWidthNatRepr @(MM.ArchAddrWidth arch))

        -- se[v]
        let postFrame = PS.unSB $ PS.simStackBase $ PS.simVarState $ (PPa.getPair' bin postVars)
        off <- liftIO $ PS.liftScope0 @post sym (\sym' -> W4.freshConstant sym' (W4.safeSymbol "frame_offset") (W4.BaseBVRepr w))
        -- asFrameOffset := frame[post] + off
        asFrameOffset <- liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off
        -- asFrameOffset' := frame[post/f(v)] + off
        asFrameOffset' <- liftIO $ PS.applyScopeCoercion sym post_to_pre asFrameOffset
        -- asm := se == frame[post/f(pre)] + off
        asm <- liftIO $ PS.liftScope2 sym W4.isEq se asFrameOffset'
        -- assuming 'asm', is 'off' constant?
        off' <- asScopedConst (PS.unSE asm) off
        lift $ traceBundle bundle (show $ W4.printSymExpr (PS.unSE off'))
        -- return frame[post] + off
        liftIO $ PS.liftScope2 sym W4.bvAdd postFrame off'

      asSimpleAssign :: forall tp. PS.ScopedExpr sym pre tp -> MaybeT (EquivM_ sym arch) (PS.ScopedExpr sym post tp)
      asSimpleAssign se = do
        -- se[pre]
        -- se' := se[pre/post]
        se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
        -- e'' := se[post/f(pre)]
        e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
        -- se is the original value, and e'' is the value rewritten
        -- to be phrased over the post-state
        heuristicTimeout <- lift $ CMR.asks (PC.cfgHeuristicTimeout . envConfig)
        asm <- liftIO $ PS.liftScope2 sym W4.isEq se e''
        True <- lift $ isPredTrue' heuristicTimeout (PS.unSE asm)
        return se'

      doRescope :: forall tp l. PL.Location sym arch l -> PS.ScopedExpr sym pre tp -> EquivM_ sym arch (MaybeF (PS.ScopedExpr sym post) tp)
      doRescope _loc se = W4B.idxCacheEval cache (PS.unSE se) $ runMaybeTF $ do
          -- The decision of ordering here is only for efficiency: we expect only
          -- one strategy to succeed (with the exception of 'asConcrete' being subsumed
          -- by 'asScopedConst' but much faster, as it doesn't involve the solver).
          -- TODO: We could do better by picking the strategy based on the term shape,
          -- but it's not strictly necessary.
          se' <- (    asConcrete se
                  <|> asStackOffset PBi.OriginalRepr se
                  <|> asStackOffset PBi.PatchedRepr se
                  <|> asScopedConst (W4.truePred sym) se
                  <|> asSimpleAssign se
                 )
          lift (emitEvent (PE.ScopeAbstractionResult (PS.simPair bundle) se se'))
          return se'

    -- First traverse the equivalence domain and rescope its entries
    -- In this case, failing to rescope is a (recoverable) error, as it results
    -- in a loss of soundness; dropping an entry means that the resulting domain
    -- is effectively now assuming equality on that entry.
    eq_post <- fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre (PAD.absDomEq postResult)) $ \loc se ->
      doRescope loc se >>= \case
        JustF se' -> return $ Just se'
        NothingF -> do
          -- failed to rescope, emit a recoverable error and drop this entry
          se' <- liftIO $ PS.applyScopeCoercion sym pre_to_post se
          e'' <- liftIO $ PS.applyScopeCoercion sym post_to_pre se'
          curAsms <- currentAsm
          _ <- emitError $ PEE.RescopingFailure curAsms se e''
          return Nothing

    -- Now traverse the value domain and rescope its entries. In this case
    -- failing to rescope is not an error, as it is simply weakening the resulting
    -- domain by not asserting any value constraints on that entry.
    val_post <- fmap PS.unWS $ PS.scopedLocWither @sym @arch sym (PS.WithScope @_ @pre (PAD.absDomVals postResult)) $ \loc se -> toMaybe <$> doRescope loc se

    return $ PAD.AbstractDomain eq_post val_post



-- | Classifying what kind of widening has occurred
data WidenKind =
    WidenValue -- ^ constant values disagree in the value domain
  | WidenEquality -- ^ values disagree between the original and patched binaries
  deriving Show

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

type WidenState sym arch v = Either (AbstractDomain sym arch v) (WidenResult sym arch v)

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
   widenOnce ::
     Gas ->
     WidenKind ->
     Maybe (Some (PBi.WhichBinaryRepr)) ->
     WidenState sym arch v ->
     PL.Location sym arch l ->
     W4.Pred sym ->
     EquivM_ sym arch (WidenState sym arch v)
   widenOnce (Gas i) widenK mwb prevState loc goal = case prevState of
     Right NoWideningRequired -> return prevState
     Right (WideningError{}) -> return prevState
     _ -> startTimer $ withSym $ \sym -> do
       eqCtx <- equivalenceContext
       let (prevLocs, postD) = case prevState of
             Left prevDom -> (mempty, prevDom)
             --FIXME: we're dropping the widening Kind now since we're
             --potentially doing multiple widenings in one iteration
             Right (Widen _ locs prevDom) -> (locs, prevDom)
       curAsms <- currentAsm
       let emit r =
             withValid @() $ emitEvent (PE.SolverEvent (PS.simPair bundle) PE.EquivalenceProof r curAsms goal)
       emit PE.SolverStarted

       not_goal <- liftIO $ W4.notPred sym goal

       goalSat "prove postcondition" not_goal $ \case
         Unsat _ -> do
           emit PE.SolverSuccess
           return prevState
         Unknown -> do
           emit PE.SolverError
           _ <- emitError $ PEE.WideningError $ "UNKNOWN result evaluating postcondition: " ++ show widenK ++ " " ++ show (pretty loc)
           -- this is a recoverable error, since we can conservatively consider the location
           -- under analysis as inequivalent in the resulting domain

           case widenK of
             WidenValue | Just (Some wb) <- mwb -> Right <$> dropValueLoc wb loc postD
             WidenEquality ->
               case loc of
                 PL.Cell c -> Right <$> widenCells [Some c] postD
                 PL.Register r -> Right <$> widenRegs [Some r] postD
             _ -> panic Verifier "widenPostcondition" [ "Unexpected widening case"]
         Sat evalFn -> do
           emit PE.SolverFailure
           if i <= 0 then
             -- we ran out of gas
             do slice <- PP.simBundleToSlice bundle
                ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice evalFn
                let msg = unlines [ "Ran out of gas performing local widenings"
                                  , show (pretty ineqRes)
                                  ]
                return $ Right $ WideningError msg prevLocs postD
           else do
             -- The current execution does not satisfy the postcondition, and we have
             -- a counterexample.
             -- FIXME: postCondAsm doesn't exist anymore, but needs to be factored
             -- out still
             res <- widenUsingCounterexample sym evalFn bundle eqCtx (W4.truePred sym) (PAD.absDomEq postD) preD prevLocs postD
             case res of
               -- this location was made equivalent by a previous widening in this same loop
               NoWideningRequired -> case prevState of
                 Left{} ->  do
                   -- if we haven't performed any widenings yet, then this is an error
                   slice <- PP.simBundleToSlice bundle
                   ineqRes <- PP.getInequivalenceResult PEE.InvalidPostState
                                   (PAD.absDomEq $ preD) (PAD.absDomEq $ postD) slice evalFn
                   let msg = unlines [ "Could not find any values to widen!"
                                     , show (pretty ineqRes)
                                     ]
                   return $ Right $ WideningError msg prevLocs postD
                 Right{} -> return prevState
               _ -> return $ Right res

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
     do
        (valPostO, valPostP) <- liftIO $ PPa.forBinsC $ \get -> do
          let
            vals = get (PAD.absDomVals postD)
            st = PS.simOutState $ get (PS.simOut bundle)
          PAD.absDomainValsToPostCond sym eqCtx st Nothing vals

        res1 <- PL.foldLocation @sym @arch sym valPostO (Left postD) (widenOnce (Gas i) WidenValue (Just (Some PBi.OriginalRepr)))
        res2 <- PL.foldLocation @sym @arch sym valPostP res1 (widenOnce (Gas i) WidenValue (Just (Some PBi.PatchedRepr)))
        eqPost_eq <- (liftIO $ PEq.getPostdomain sym bundle eqCtx (PAD.absDomEq preD) (PAD.absDomEq postD))
        res <- PL.foldLocation @sym @arch sym eqPost_eq res2 (widenOnce (Gas i) WidenEquality Nothing)

        -- Re-enter the widening loop if we had to widen at this step.
        --
        -- If we did not have to widen in this iteration, and no widening
        -- was done in previous iterations (i.e., this is the first iteration)
        -- return `NoWideningRequired`.  Otherwise return the new abstract domain
        -- and a summary of the widenings we did.
        case res of

          -- Some kind of error occured while widening.
          Right er@(WideningError msg locs _postD') ->
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
               return er

          -- In this iteration, no additional widening was done, and we can exit the loop.
          -- The ultimate result we return depends on if we did any widening steps in
          -- previous iterations.
          Right NoWideningRequired ->
            case mPrevRes of
              Nothing   -> return NoWideningRequired
              Just prevRes -> return prevRes
          -- no widening happened
          Left{} ->
            case mPrevRes of
              Nothing   -> return NoWideningRequired
              Just prevRes -> return prevRes
          -- We had to do some widening in this iteration, so reenter the loop.
          Right (Widen widenK locs postD') ->
            do traceBundle bundle "== Found a widening, returning into the loop =="
               traceBundle bundle (show locs)
               let newlocs = case mPrevRes of
                     Just (Widen _ prevLocs _) -> locs <> prevLocs
                     _ -> locs
               widenLoop sym (Gas (i-1)) eqCtx postD' (Just $ Widen widenK newlocs postD')


-- | Refine a given 'AbstractDomainBody' to contain concrete values for the
-- output of symbolic execution, where possible.
-- Uses the default concretization strategies from 'Pate.Verification.Concretize'
getInitalAbsDomainVals ::
  forall sym arch v.
  SimBundle sym arch v ->
  PAD.AbstractDomain sym arch v {- ^ incoming pre-domain -} ->
  EquivM sym arch (PPa.PatchPair (PAD.AbstractDomainVals sym arch))
getInitalAbsDomainVals bundle preDom = withSym $ \sym -> do
  let
    getConcreteRange :: forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (PAD.AbsRange tp)
    getConcreteRange e = do
      e' <- concretizeWithSolver e
      return $ PAD.extractAbsRange sym e'

  let PPa.PatchPair preO preP = PAD.absDomVals preDom
  eqCtx <- equivalenceContext
  IO.withRunInIO $ \inIO -> do
    initO <- PAD.initAbsDomainVals sym eqCtx (\e -> inIO (getConcreteRange e)) (PS.simOutO bundle) preO
    initP <- PAD.initAbsDomainVals sym eqCtx (\e -> inIO (getConcreteRange e)) (PS.simOutP bundle) preP
    return $ PPa.PatchPair initO initP

widenUsingCounterexample ::
  sym ->
  SymGroundEvalFn sym ->
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
    ]

data MemCellSource = LocalChunkWrite | PreDomainCell

widenValues ::
  forall sym arch v.
  sym ->
  SymGroundEvalFn sym ->
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
     getRange e = do
       g <- execGroundFn evalFn e
       return $ PAD.groundToAbsRange (W4.exprType e) g

dropValueLoc ::
  forall arch sym v l bin.
  PBi.WhichBinaryRepr bin ->
  PL.Location sym arch l ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
dropValueLoc wb loc postD = do
  let
    vals = PPa.getPair' wb (PAD.absDomVals postD)
    v = case loc of
      PL.Cell c -> vals { PAD.absMemVals = MapF.delete c (PAD.absMemVals vals) }
      PL.Register r ->
        vals { PAD.absRegVals = (PAD.absRegVals vals) & (MM.boundValue r) .~ (PAD.noAbsVal (MT.typeRepr r)) }
    locs = case loc of
      PL.Cell c -> WidenLocs Set.empty (Set.singleton (Some c))
      PL.Register r -> WidenLocs (Set.singleton (Some r)) Set.empty
    vals' = PPa.setPair wb v (PAD.absDomVals postD)
  return $ Widen WidenValue locs (postD { PAD.absDomVals = vals' })

widenCells ::
  [Some (PMc.MemCell sym arch)] ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenCells cells postD = withSym $ \sym -> do
  newCells <- liftIO $ PEM.fromList sym [ (c, W4.truePred sym) | c <- cells ]
  -- the domain semantics will ignore cells which have the wrong region, so
  -- we can just add the cells to both at the cost of some redundancy
  let heapDom = PEE.eqDomainGlobalMemory (PAD.absDomEq $ postD)
  heapDom' <- liftIO $ PEM.intersect sym heapDom newCells
  let stackDom = PEE.eqDomainStackMemory (PAD.absDomEq $ postD)
  stackDom' <- liftIO $ PEM.intersect sym stackDom newCells
  let pred' = (PAD.absDomEq postD){ PEE.eqDomainGlobalMemory = heapDom', PEE.eqDomainStackMemory = stackDom' }
  let postD' = postD { PAD.absDomEq = pred' }
  return (Widen WidenEquality (WidenLocs mempty (Set.fromList cells)) postD')

widenRegs ::
  [Some (MM.ArchReg arch)] ->
  AbstractDomain sym arch v ->
  EquivM sym arch (WidenResult sym arch v)
widenRegs newRegs postD = withSym $ \sym -> do
  let
    regs' = foldl'
                 (\m (Some r) -> PER.update sym (\ _ -> W4.falsePred sym) r m)
                 (PEE.eqDomainRegisters (PAD.absDomEq $ postD))
                 newRegs
    pred' = (PAD.absDomEq postD) { PEE.eqDomainRegisters = regs' }
    postD' = postD { PAD.absDomEq = pred' }
    locs = WidenLocs (Set.fromList newRegs) mempty
  return (Widen WidenEquality locs postD')

-- TODO, lots of code duplication between the stack and heap cases.
--  should we find some generalization?
widenHeap ::
  sym ->
  SymGroundEvalFn sym ->
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
filterCells :: forall sym arch.
  sym ->
  SymGroundEvalFn sym ->
  PEM.MemoryDomain sym arch ->
  [Some (PMc.MemCell sym arch)] ->
  EquivM sym arch [Some (PMc.MemCell sym arch)]
filterCells sym evalFn memDom xs = filterM filterCell xs
  where
    filterCell (Some c) =
      execGroundFn evalFn =<< liftIO (PEM.mayContainCell sym memDom c)

widenStack ::
  sym ->
  SymGroundEvalFn sym ->
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
  sym ->
  SymGroundEvalFn sym ->
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
          cellEq' <- lift $ execGroundFn evalFn cellEq
          unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackWrites ::
  sym ->
  SymGroundEvalFn sym ->
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
          cellEq' <- lift $ execGroundFn evalFn cellEq
          unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalHeapMemCells ::
  sym ->
  SymGroundEvalFn sym ->
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
          cellEq' <- lift $ execGroundFn evalFn cellEq
          unless cellEq' (tell [Some cell])

-- TODO, may be worth using Seq instead of lists to avoid the quadratic time
-- behavior of `WriterT` with lists
findUnequalStackMemCells ::
  sym ->
  SymGroundEvalFn sym ->
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
          cellEq' <- lift $ execGroundFn evalFn cellEq
          unless cellEq' (tell [Some cell])

widenRegisters ::
  sym ->
  SymGroundEvalFn sym ->
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
  sym ->
  SymGroundEvalFn sym ->
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
            regEq <- lift $ execGroundFn evalFn pRegEq
            when regEq $
              do isEqPred <- liftIO (registerValuesEqual sym eqCtx regName oRegVal pRegVal)
                 isEq <- lift $ execGroundFn evalFn isEqPred
                 when (not isEq) (tell [Some regName]))
    oRegs
