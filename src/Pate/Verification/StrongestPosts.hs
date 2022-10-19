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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Verification.StrongestPosts
  ( pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.) )
import           Control.Monad (foldM, forM)
import           Control.Monad.Identity ( runIdentity )
import           Control.Monad.IO.Class
import           Control.Monad.Reader (asks, local)
import           Control.Monad.Except (catchError, throwError)
import           Control.Monad.Trans (lift)
import           System.IO as IO
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Proxy
import           Data.Functor.Const
import           Data.IORef ( IORef, newIORef, readIORef, modifyIORef )

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.WithRepr

import qualified What4.Expr as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import           What4.SatResult (SatResult(..))

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator.RegValue as LCS
import           Lang.Crucible.Simulator.SymSequence
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.AbsDomain.AbsState as MAS
import qualified Data.Macaw.Discovery as MD

import qualified Pate.Abort as PAb
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Discovery.ParsedFunctions as PD
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
import qualified Pate.Verification.Simplify as PSi

import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node ( GraphNode(..), NodeEntry, mkNodeEntry, mkNodeReturn, nodeBlocks, addContext, returnToEntry, nodeFuns, graphNodeBlocks, getFrozen, isThisFrozen, applyFreeze, FrozenContext(..), frozenRepr, unfreezeReturn, freezeNodeFn, freezeNode, returnOfEntry)
import           Pate.Verification.Widening
import qualified Pate.Verification.AbstractDomain as PAD
import qualified Pate.ExprMappable as PEM
import           What4.ExprHelpers

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
  [PB.FunPair arch] ->
  IO (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
runVerificationLoop env pPairs = do
  result <- runEquivM env doVerify
  case result of
    Left err -> return (PE.Errored err, mempty)
    Right r -> return r
 where
   doVerify :: EquivM sym arch (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
   doVerify = do
          pg0 <- initializePairGraph pPairs
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

{-
resolveNode ::
  GraphNode arch ->
  EquivM sym arch (GraphNode arch)
resolveNode nd = case nd of
  (GraphNode entry) -> do
    let pPair = nodeBlocks entry
    let fnPair = TF.fmapF PB.blockFunctionEntry pPair
    pPair' <- PPa.forBins $ \get -> do
      let fnEntry = get fnPair
      pfm <- PMC.parsedFunctionMap <$> getBinCtx
      fnEntry' <- liftIO $ PD.resolveFunctionEntry fnEntry pfm
      return $ (get pPair) { PB.blockFunctionEntry = fnEntry' }
    return $ GraphNode (mkNodeEntry entry pPair')
  (ReturnNode ret) -> do
    let fnPair = nodeFuns ret
    fnPair' <- PPa.forBins $ \get -> do
      let fnEntry = get fnPair
      pfm <- PMC.parsedFunctionMap <$> getBinCtx
      liftIO $ PD.resolveFunctionEntry fnEntry pfm
    return $ ReturnNode (mkNodeReturn (returnToEntry ret) fnPair')
-}

shouldProcessNode ::
  GraphNode arch ->
  EquivM sym arch Bool
shouldProcessNode node = do
  let PPa.PatchPair blkO blkP = graphNodeBlocks node
  case PB.concreteAddress blkO == PB.concreteAddress blkP of
    True -> return True
    False -> not <$> asks (PCfg.cfgIgnoreDivergedControlFlow . envConfig)

-- | Execute the forward dataflow fixpoint algorithm.
--   Visit nodes and compute abstract domains until we propagate information
--   to all reachable positions in the program graph and we reach stability,
--   or until we run out of gas.
--
--   TODO, could also imagine putting timeouts/compute time limits here.
pairGraphComputeFixpoint ::
  forall sym arch. PairGraph sym arch -> EquivM sym arch (PairGraph sym arch)
pairGraphComputeFixpoint gr0 = do
  let
    go (gr :: PairGraph sym arch) = case chooseWorkItem gr of
      Nothing -> return gr
      Just (gr', nd, preSpec) -> do
        gr'' <- subTrace @"node" nd $ startTimer $
          shouldProcessNode nd >>= \case
            False -> do
              emitWarning $ PEE.SkippedInequivalentBlocks (graphNodeBlocks nd)
              return gr'
            True -> PS.viewSpec preSpec $ \scope d -> do
              emitTraceLabel @"domain" PAD.Predomain (Some d)
              withAssumptionSet (PS.scopeAsm scope) $ do
                gr'' <- visitNode scope nd d gr'
                emitEvent $ PE.VisitedNode nd
                return gr''
        go gr''

    -- Orphaned returns can appear when we never find a return branch for
    -- a function (e.g. possibly due to a code analysis failure)
    -- Formally, the analysis can't proceed past any call site for a function
    -- that doesn't return, since we don't know anything about the equivalence post-domain.
    -- Rather than simply giving up at this point, we make a best-effort to
    -- invent a reasonable equivalence post-domain (see 'updateExtraEdges') and
    -- continue the analysis from
    -- all of the (orphaned) return sites for a non-terminating function
    go_orphans :: PairGraph sym arch -> NodeBuilderT '(sym,arch) "node" (EquivM_ sym arch) (PairGraph sym arch)
    go_orphans (gr :: PairGraph sym arch) = do
      let orphans = getOrphanedReturns gr
      case Set.toList orphans of
        [] -> return gr
        (ret : _) -> do
          let
            fnEntry = returnToEntry ret
            gr1 = addExtraEdge gr fnEntry (ReturnNode ret)
          gr2 <- subTrace @"node" (GraphNode fnEntry) $ do
            emitError $ PEE.BlockHasNoExit (nodeBlocks fnEntry)
            case getCurrentDomain gr1 (GraphNode fnEntry) of
              Just preSpec -> PS.viewSpec preSpec $ \scope d -> withValidInit scope (nodeBlocks fnEntry) $ updateExtraEdges scope fnEntry d gr1
              Nothing -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnEntry)
          go gr2 >>= go_orphans
  withSubTraces $ do
    gr1 <- go gr0
    (lift $ asks (PCfg.cfgAddOrphanEdges . envConfig)) >>= \case
      True -> go_orphans gr1
      False -> return gr1

-- | For an orphan return, we treat it the same as an undefined PLT stub,
--   since we effectively have no way to characterize the function behavior.
--   In this case we model the function behavior as having peformed the
--   default PLT stub action and then immediately returning.
orphanReturnBundle ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  PB.BlockPair arch ->
  EquivM sym arch (SimBundle sym arch v)
orphanReturnBundle scope pPair = withSym $ \sym -> do
  PA.SomeValidArch archData <- asks envValidArch
  let ov = PA.defaultStubOverride archData
  let vars = PS.scopeVars scope
  simIn_ <- PPa.forBins $ \get -> do
    absSt <- PD.getAbsDomain (get pPair)
    return $ PS.SimInput (PS.simVarState (get vars)) (get pPair) absSt

  wsolver <- getWrappedSolver
  simOut_ <- catchInIO $ PA.withStubOverride sym wsolver ov $ \f -> PPa.forBins $ \get -> do
    let inSt = PS.simInState $ get simIn_
    outSt <- f inSt
    --FIXME: this happens to correspond to a default "return" case,
    --but we should probably make that explicit
    blkend <- MCS.initBlockEnd (Proxy @arch) sym
    return $ PS.SimOutput outSt blkend

  return $ PS.SimBundle simIn_ simOut_


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
  HasCallStack =>
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

asFunctionPair ::
  PB.BlockPair arch ->
  Maybe (PB.FunPair arch)
asFunctionPair (PPa.PatchPair blkO blkP) = case (PB.asFunctionEntry blkO, PB.asFunctionEntry blkP) of
  (Just fnO, Just fnP) -> Just (PPa.PatchPair fnO fnP)
  _ -> Nothing

getFunctionAbs ::
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PPa.PatchPair (Const (Map.Map (MM.ArchSegmentOff arch) (PB.AbsStateOverride arch))))
getFunctionAbs node d gr = do
  case asFunctionPair (nodeBlocks node) of
    -- this is a function pair, so use the given domain
    Just fnPair ->  PPa.forBins $ \get -> do
      let
        vals = get (PAD.absDomVals d)
        absSt = PAD.domainValsToAbsState vals
        fe = get (fnPair)
      return $ Const (Map.singleton (PB.functionSegAddr fe) absSt)
    Nothing -> do
      -- this is some sub-block in a function, so use the domain for
      -- the function entry point
      let fnPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks node)  
      case getCurrentDomain gr (GraphNode node) of
        Just preSpec -> PS.viewSpec preSpec $ \scope d' -> PPa.forBins $ \get -> do
          let
            vals = get (PAD.absDomVals d')
            absSt = PAD.domainValsToAbsState vals
            fe = get (fnPair)
          return $ Const (Map.singleton (PB.functionSegAddr fe) absSt)
        Nothing -> throwHere $ PEE.MissingDomainForFun fnPair

-- | Setup a special-purpose ParsedFunctionMap with this block having a special
--   domain 
withAbsDomain ::
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withAbsDomain node d gr f = do
  PA.SomeValidArch archData <- asks envValidArch
  let pPair = nodeBlocks node
  ovPair <- getFunctionAbs node d gr  
  binCtxPair <- PPa.forBins $ \get -> do
    binCtx <- getBinCtx
    let
      Const absSt = get ovPair
      pfm = PMC.parsedFunctionMap binCtx
      defaultInit = PA.validArchInitAbs archData
    pfm' <- liftIO $ PD.addOverrides defaultInit pfm absSt
    return $ binCtx { PMC.parsedFunctionMap = pfm' }
  local (\env -> env { envCtx = (envCtx env) { PMC.binCtxs = binCtxPair } }) $ do
    let fnBlks = TF.fmapF (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) (nodeBlocks node)
    PPa.catBins $ \get -> do
      pfm <- PMC.parsedFunctionMap <$> getBinCtx
      (liftIO $ PD.parsedFunctionContaining (get fnBlks) pfm) >>= \case
        Just{} -> return ()
        Nothing -> throwHere $ PEE.MissingDomainForBlock fnBlks
    f
        

   
{-
-- | Inject the current value domain into macaw so it can be used
--   during code discovery
updateAbsBlockState ::
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  EquivM sym arch ()
updateAbsBlockState node d = do
  let pPair = nodeBlocks node
  case asFunctionPair pPair of
    Just fnPair -> do
      PPa.catBins $ \get -> do
        let vals = get (PAD.absDomVals d)
        pfm <- PMC.parsedFunctionMap <$> getBinCtx

        
        liftIO $ PD.setAbstractState defaultInit (get fnPair) absDom pfm
        (liftIO $ PD.parsedFunctionContaining (get pPair) pfm) >>= \case
          Just{} -> return ()
          Nothing -> throwHere $ PEE.MissingParsedBlockEntry "parsedFunctionContaining" (get pPair)

    _ -> return ()
-}
processBundle ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
processBundle scope node bundle d gr0 = do
  exitPairs <- PD.discoverPairs bundle (frozenRepr (getFrozen node))

  gr1 <- checkObservables node bundle d gr0

  gr2 <- checkTotality node bundle d exitPairs gr1

  mgr3 <- updateReturnNode scope node bundle d gr2
  gr3 <- case mgr3 of
    Just gr3 -> return gr3
    Nothing ->
      case exitPairs of
      -- if we find a busy loop, try to continue the analysis assuming we
      -- break out of the loop, even if the semantics say it can't happen
      -- TODO: ideally we should handle this as an "extra" edge rather than
      -- directly handling the widening here.
      [PPa.PatchPair (PB.BlockTarget tgtO Nothing _) (PB.BlockTarget tgtP Nothing _)] |
         PPa.PatchPair tgtO tgtP == (PS.simPair bundle) ->
        asks (PCfg.cfgAddOrphanEdges . envConfig) >>= \case
           True -> do
             emitWarning $ PEE.BlockHasNoExit (PS.simPair bundle)
             nextBlocks <- PPa.forBins $ \get -> do
               let blk = get (PS.simPair bundle)
               PD.nextBlock blk >>= \case
                 Just nb -> return nb
                 Nothing -> throwHere $ PEE.MissingParsedBlockEntry "processBundle" blk
             bundle' <- PD.associateFrames bundle MCS.MacawBlockEndJump False
             widenAlongEdge scope bundle' (GraphNode node) d gr2 (GraphNode (mkNodeEntry node nextBlocks))
           False -> return gr2
      _ -> return gr2

  -- Follow all the exit pairs we found
  subTree @"blocktarget" "Block Exits" $
    foldM (\x y@(_,tgt) -> subTrace tgt $ followExit scope bundle node d x y) gr3 (zip [0 ..] exitPairs)

withValidInit ::
  forall sym arch v a.
  HasCallStack =>
  PS.SimScope sym arch v ->
  PB.BlockPair arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withValidInit scope bPair f = withPair bPair $ do
  let vars = PS.scopeVars scope
  validInit <- PVV.validInitState (Just bPair) (PS.simVarState $ PPa.pOriginal vars) (PS.simVarState $ PPa.pPatched vars)
  validAbs <- PPa.catBins $ \get -> validAbsValues (get bPair) (get vars)
  withAssumptionSet (validInit <> validAbs) $ f  



withSimBundle ::
  forall sym arch v a.
  PPa.PatchPair (PS.SimVars sym arch v) ->
  NodeEntry arch ->
  (SimBundle sym arch v -> EquivM_ sym arch a) ->
  EquivM sym arch a
withSimBundle vars node f = do
  let bPair = nodeBlocks node
  bundle0 <- withTracing @"function_name" "mkSimBundle" $ mkSimBundle node vars
  simplifier <- PSi.getSimplifier
  bundle1 <- PSi.applySimplifier simplifier bundle0
  bundle <- applyCurrentAsms bundle1
  emitTrace @"bundle" (Some bundle)
  f bundle

handleExtraEdge ::
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  GraphNode arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)  
handleExtraEdge scope node target d gr = do
  bundle <- orphanReturnBundle scope (nodeBlocks node)
  withPredomain bundle d $ 
    widenAlongEdge scope bundle (GraphNode node) d gr target

updateExtraEdges ::
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)   
updateExtraEdges scope node d gr = withTracing @"function_name" "updateExtraEdges" $ do
  let extra = getExtraEdges gr node
  foldM (\gr' tgt -> handleExtraEdge scope node tgt d gr') gr (Set.toList extra)

checkParsedBlocks ::
  PB.BlockPair arch ->
  EquivM sym arch ()
checkParsedBlocks pPair = PPa.catBins $ \get -> do
  pfm <- PMC.parsedFunctionMap <$> getBinCtx
  let blk = get pPair
  let fnEntryBlk = PB.functionEntryToConcreteBlock (PB.blockFunctionEntry blk)
  (liftIO $ PD.parsedFunctionContaining blk pfm) >>= \case
    Just{} -> return ()
    Nothing -> throwHere $ PEE.MissingParsedBlockEntry "checkParsedBlocks" blk


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
  HasCallStack =>
  PS.SimScope sym arch v ->
  GraphNode arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
visitNode scope (GraphNode node@(nodeBlocks -> bPair)) d gr0 = withAbsDomain node d gr0 $ do
  checkParsedBlocks bPair
  withValidInit scope bPair $ do
    gr1 <- updateExtraEdges scope node d gr0
    let vars = PS.scopeVars scope
    withSimBundle vars node $ \bundle -> withPredomain bundle d $ processBundle scope node bundle d gr1

visitNode scope (ReturnNode fPair) d gr0 =
  -- propagate the abstract domain of the return node to
  -- all of the known call sites of this function.
  subTree @"entrynode" "Block Returns" $
    foldM (\gr node -> subTrace node $ processReturn gr node) gr0 (getReturnVectors gr0 fPair)

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
  HasCallStack =>
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  AbstractDomain sym arch v ->
  PB.BlockPair arch {- ^ block pair being returned to -} ->
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

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "observable_result" where
  type TraceNodeType '(sym,arch) "observable_result" = ObservableCheckResult sym (MM.ArchAddrWidth arch)
  prettyNode () = \case
    ObservableCheckEq -> "Observably Equivalent"
    ObservableCheckCounterexample (ObservableCounterexample oSeq pSeq) -> PP.vsep $ 
       ["Observable Inequivalence Detected:"
       , "== Original sequence =="
       ] ++ (map MT.prettyMemEvent oSeq) ++
       [ "== Patched sequence ==" ]
       ++ (map MT.prettyMemEvent pSeq)

    ObservableCheckError msg -> PP.vsep $
      [ "Error during observability check"
      , PP.pretty msg
      ]
  nodeTags = [(Summary, \() res -> case res of
                  ObservableCheckEq -> "Observably Equivalent"
                  ObservableCheckCounterexample{} -> "Observable Inequivalence Detected"
                  ObservableCheckError{} -> "Error during observability check")
             ]

checkObservables :: forall sym arch v.
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkObservables bPair bundle preD gr =
  considerObservableEvent gr bPair $
    do res <- doCheckObservables bundle preD
       withTracing @"observable_result" res $
         case res of
           ObservableCheckEq ->
             do traceBundle bundle "Observables agree"
                return (Nothing, gr)
           ObservableCheckError msg ->
             do let msg' = ("Error checking observables: " ++ msg)
                err <- emitError' (PEE.ObservabilityError msg')
                return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) err)
           ObservableCheckCounterexample cex@(ObservableCounterexample oSeq pSeq) -> do
             do traceBundle bundle ("Obserables disagree!")
                traceBundle bundle ("== Original sequence ==")
                traceBundle bundle (show (vcat (map MT.prettyMemEvent oSeq)))
                traceBundle bundle ("== Patched sequence ==")
                traceBundle bundle (show (vcat (map MT.prettyMemEvent pSeq)))
                emitWarning $ PEE.ObservableDifferenceFound
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

eqSymBVs ::
  Ctx.Assignment (MT.SymBV' sym) ctx1 ->
  Ctx.Assignment (MT.SymBV' sym) ctx2 ->
  EquivM sym arch (W4.Pred sym)
eqSymBVs (asn1 Ctx.:> MT.SymBV' bv1) (asn2 Ctx.:> MT.SymBV' bv2) = case testEquality (W4.bvWidth bv1) (W4.bvWidth bv2) of
  Just Refl | Just W4.LeqProof <- W4.isPosNat (W4.bvWidth bv1) -> withSym $ \sym -> do
    hdeq <- liftIO $ W4.bvEq sym bv1 bv2
    tleq <- eqSymBVs asn1 asn2
    liftIO $ W4.andPred sym hdeq tleq
  _ -> withSym $ \sym -> return $ W4.falsePred sym
eqSymBVs Ctx.Empty Ctx.Empty = withSym $ \sym -> return $ W4.truePred sym
-- mismatched sizes
eqSymBVs _ _ = withSym $ \sym -> return $ W4.falsePred sym
  

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

  eqEvent (MT.ExternalCallEvent nmx x) (MT.ExternalCallEvent nmy y)
    | nmx == nmy
    = eqSymBVs x y
    
  eqEvent _ _ = return (W4.falsePred sym)

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

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "totality" where
  type TraceNodeType '(sym,arch) "totality" = TotalityResult (MM.ArchAddrWidth arch)
  prettyNode () r = case r of
    CasesTotal -> "Cases total"
    TotalityCheckingError msg -> "Error:" <+> PP.pretty msg
    TotalityCheckCounterexample (TotalityCounterexample (oIP,oEnd,oInstr) (pIP,pEnd,pInstr)) -> PP.vsep $
      ["Found extra exit while checking totality:"
      , PP.pretty (showHex oIP "") <+> PP.pretty (PPI.ppExitCase oEnd) <+> PP.pretty (show oInstr)
      , PP.pretty (showHex pIP "") <+> PP.pretty (PPI.ppExitCase pEnd) <+> PP.pretty (show pInstr)
      ]
  nodeTags = [(Summary, \_ r -> case r of
                   CasesTotal -> "Total"
                   TotalityCheckingError{} -> "Error"
                   TotalityCheckCounterexample{} -> "Not total")
             ]
   

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
       withTracing @"totality" tot $ case tot of
         TotalityCheckCounterexample{} -> emitWarning $ PEE.NonTotalBlockExits (nodeBlocks bPair)
         _ -> return()
       case tot of
         CasesTotal ->
           do traceBundle bundle "Totality check succeeded."
              return (Nothing, gr)
         TotalityCheckingError msg ->
           do let msg' = ("Error while checking totality! " ++ msg)
              err <- emitError' (PEE.TotalityError msg')
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
  EquivM sym arch (Maybe (PairGraph sym arch))
updateReturnNode scope bPair bundle preD gr = do
  isReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
  withPathCondition (PAS.fromPred isReturn) $ do
    bundle' <- PD.associateFrames bundle MCS.MacawBlockEndReturn False
    handleReturn scope bundle' bPair preD gr

maybeUpdate ::
  PairGraph sym arch -> 
  EquivM sym arch (Maybe (PairGraph sym arch)) ->
  EquivM sym arch (PairGraph sym arch)
maybeUpdate gr f = f >>= \case
  Just gr' -> return gr'
  Nothing -> return gr

skippedFnName :: BS.ByteString
skippedFnName = BSC.pack "__pate_skipped"

getFunctionStub ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Maybe BS.ByteString)
getFunctionStub blk = do
  PA.SomeValidArch archData <- asks envValidArch
  findPLTSymbol blk >>= \case
    Just nm -> return $ Just nm
    Nothing | Just fnEntry <- PB.asFunctionEntry blk -> do
      let mnm = PB.functionSymbol fnEntry
      case mnm of
        Just nm | Just{} <- PA.lookupStubOverride archData nm -> return $ Just nm
        Just nm | Set.member nm abortStubs -> return $ Just nm
        Just nm | PB.functionIgnored fnEntry -> return $ Just nm
        Nothing | PB.functionIgnored fnEntry -> return $ Just skippedFnName
        Nothing -> asks (PCfg.cfgIgnoreUnnamedFunctions . envConfig) >>= \case
          True -> return $ Just skippedFnName
          False -> return Nothing
        _ -> return Nothing
    Nothing -> return Nothing

type StubPair = PPa.PatchPair (Const (Maybe BS.ByteString))

viewStubPair ::
  StubPair ->
  (Maybe BS.ByteString, Maybe BS.ByteString)
viewStubPair (PPa.PatchPair (Const sO) (Const sP)) = (sO,sP)

-- | Return the name of a function if we want to replace its call with
--   stub semantics
getFunctionStubPair ::
  NodeEntry arch ->
  EquivM sym arch StubPair
getFunctionStubPair node = PPa.forBins $ \get -> do
  case isThisFrozen get node of
    -- never process a frozen node as if it has stub semantics
    True -> return $ Const Nothing
    False -> Const <$> getFunctionStub (get (nodeBlocks node))

hasStub :: StubPair -> Bool
hasStub stubPair = case viewStubPair stubPair of
  (Just{}, _) -> True
  (_, Just{}) -> True
  _ -> False

-- | True if either stub has an abort symbol
hasTerminalStub :: StubPair -> Bool
hasTerminalStub stubPair = case viewStubPair stubPair of
  (Just nm, _) | isAbortStub nm -> True
  (_, Just nm) | isAbortStub nm -> True
  _ -> False
 
bothTerminalStub :: StubPair -> Bool
bothTerminalStub stubPair = case viewStubPair stubPair of
  (Just nm1, Just nm2) | isAbortStub nm1 && isAbortStub nm2 -> True
  _ -> False

isIgnoredBlock :: PB.ConcreteBlock arch bin -> Bool
isIgnoredBlock blk = case PB.asFunctionEntry blk of
  Just fnEntry -> PB.functionIgnored fnEntry
  Nothing -> False

{-
isIgnoredBlockPair :: PPa.PatchPair (PB.ConcreteBlock arch) -> Bool
isIgnoredBlockPair blks = isIgnoredBlock (PPa.pOriginal blks) (PPa.pPatched blks)
-}

-- FIXME: defined by the architecture?
abortStubs :: Set.Set (BS.ByteString)
abortStubs = Set.fromList $ map BSC.pack ["abort","err","perror","exit"]

isAbortStub :: BS.ByteString -> Bool
isAbortStub nm = Set.member nm abortStubs

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
triageBlockTarget scope bundle' currBlock d gr blkts@(PPa.PatchPair blktO blktP) =
  do let
        blkO = PB.targetCall blktO
        blkP = PB.targetCall blktP
        pPair = PPa.PatchPair blkO blkP
        nextNode = mkNodeEntry currBlock pPair

     stubPair <- getFunctionStubPair nextNode
     traceBundle bundle' ("  targetCall: " ++ show blkO)
     matches <- PD.matchesBlockTarget bundle' blkts
     maybeUpdate gr $ withPathCondition matches $ do
       bundle <- PD.associateFrames bundle' (PB.targetEndCase blktO) (hasStub stubPair)
       case (PB.targetReturn blktO, PB.targetReturn blktP) of
         (Just blkRetO, Just blkRetP) ->
           do traceBundle bundle ("  Return target " ++ show blkRetO ++ ", " ++ show blkRetP)
              isPreArch <- case (PB.concreteBlockEntry blkO, PB.concreteBlockEntry blkP) of
                 (PB.BlockEntryPreArch, PB.BlockEntryPreArch) -> return True
                 (entryO, entryP) | entryO == entryP -> return False
                 _ -> throwHere $ PEE.BlockExitMismatch
              ctx <- view PME.envCtxL
              let isEquatedCallSite = any (PB.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)


              if | isPreArch -> handleArchStmt scope bundle currBlock d gr (PB.targetEndCase blktO) pPair (Just (PPa.PatchPair blkRetO blkRetP))
                 | isEquatedCallSite -> handleInlineCallee scope bundle currBlock d gr pPair  (PPa.PatchPair blkRetO blkRetP)
                 | hasStub stubPair -> handleStub scope bundle currBlock d gr pPair (Just (PPa.PatchPair blkRetO blkRetP)) stubPair
                 | otherwise -> handleOrdinaryFunCall scope bundle currBlock d gr pPair (PPa.PatchPair blkRetO blkRetP)

         (Nothing, Nothing) | PB.targetEndCase blktO == PB.targetEndCase blktP ->
           do traceBundle bundle "No return target identified"
              -- exits without returns need to either be a jump, branch or tail calls
              -- we consider those cases here (having already assumed a specific
              -- block exit condition)
              case PB.targetEndCase blktO of
                MCS.MacawBlockEndCall | hasStub stubPair ->
                  handleStub scope bundle currBlock d gr pPair Nothing stubPair
                MCS.MacawBlockEndCall -> handleTailFunCall scope bundle currBlock d gr pPair
                MCS.MacawBlockEndJump -> handleJump scope bundle currBlock d gr nextNode
                MCS.MacawBlockEndBranch -> handleJump scope bundle currBlock d gr nextNode
                _ -> throwHere $ PEE.BlockExitMismatch
         _ -> do traceBundle bundle "BlockExitMismatch"
                 throwHere $ PEE.BlockExitMismatch

findPLTSymbol ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Maybe BS.ByteString)
findPLTSymbol blk = do
  PA.SomeValidArch archData <- asks envValidArch
  let
    extraMapPair = PPa.PatchPair (Const (PA.validArchOrigExtraSymbols archData)) (Const (PA.validArchPatchedExtraSymbols archData))
    Const extraMap = PPa.get @bin extraMapPair
    addr = PAd.addrToMemAddr (PB.concreteAddress blk)
  case (MM.asAbsoluteAddr addr) of
    Just mw -> do
      let syms = [ s | (s,bv) <- Map.toList extraMap
                 , BV.asUnsigned bv == toInteger (MM.memWordValue mw)
                 ]
      case syms of
        [sym] -> return (Just sym)
        _ -> return Nothing
    _ -> return Nothing

{-
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
-}

-- TODO: This is a bit tricky because it might involve architecture-specific
-- reasoning
handleArchStmt ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  MCS.MacawBlockEndCase ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  Maybe (PPa.PatchPair (PB.ConcreteBlock arch)) {- ^ return point -} ->
  EquivM sym arch (PairGraph sym arch)
handleArchStmt scope bundle currBlock d gr endCase pPair mpRetPair = case endCase of
  -- this is the jump case for returns, if we return *with* a return site, then
  -- this is actually a normal jump
  MCS.MacawBlockEndReturn | Just pRetPair <- mpRetPair, pPair == pRetPair ->
    handleJump scope bundle currBlock d gr (mkNodeEntry currBlock pPair)
  -- if our return site isn't the same as the target, then this is just a return
  -- NOTE: this is slightly different than 'updateReturnNode', because the
  -- 'matchesBlockExit' assumption has assumed that exactly this return statement
  -- is the one under consideration.
  -- In general it's possible for multiple return statements to be reachable
  -- from the entry point, and 'updateReturnNode' will have handled all of them
  -- TODO: this is likely redundant, since 'updateReturnNode' should subsume this
  MCS.MacawBlockEndReturn | Just pRetPair <- mpRetPair, pPair /= pRetPair ->
    handleReturn scope bundle currBlock d gr
  MCS.MacawBlockEndReturn | Nothing <- mpRetPair ->
    handleReturn scope bundle currBlock d gr
  _ -> do
    _ <- emitError $ PEE.NotImplementedYet "handleArchStmt"
    return gr


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
handleInlineCallee _scope _bundle _currBlock _d gr _pPair _pRetPair = do
  _ <- emitError $ PEE.NotImplementedYet "handleInlineCallee"
  return gr -- TODO!

-- TODO: there's a fair bit copied from the ordinary function call case here,
-- the only difference is that we link up the return of tail-called function
-- to the caller
handleTailFunCall ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch)
handleTailFunCall scope bundle currBlock d gr pPair =
  case (PB.asFunctionEntry (PPa.pOriginal pPair), PB.asFunctionEntry (PPa.pPatched pPair)) of
    (Just oFun, Just pFun) -> do
      emitTraceLabel @"funcall" PB.TailFunCall (PPa.PatchPair oFun pFun)
      currBlock' <- asks (PCfg.cfgContextSensitivity . envConfig) >>= \case
        PCfg.SharedFunctionAbstractDomains -> return currBlock
        PCfg.DistinctFunctionAbstractDomains -> return $ addContext pPair currBlock
      -- find the function call block to determine where this tail will ultimately return to
      funEntry <- PPa.forBins $ \get -> return $ (PB.blockFunctionEntry (get (nodeBlocks currBlock)))
      -- node representing the return sites of the caller
      let
        callerFunNode = mkNodeReturn currBlock funEntry
        tailCallFunNode = mkNodeReturn currBlock' (PPa.PatchPair oFun pFun)
        tailCallNode = mkNodeEntry currBlock' pPair
        callers = getReturnVectors gr callerFunNode
        gr' = Set.foldl' (\gr'' caller -> addReturnVector gr'' tailCallFunNode caller) gr callers
      case Set.null callers of
        True -> (emitError $ PEE.UnexpectedTailCallEntry funEntry) >> return ()
        False -> return ()
      matches <- PD.matchingExits bundle MCS.MacawBlockEndCall
      withAssumption matches $
        handleJump scope bundle currBlock d gr' tailCallNode
    _ -> panic Verifier "handleTailFunCall"
             [ "Tail function call jumped to a location that is not a function start!"
             , show currBlock
             , show pPair
             ]

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
          emitTraceLabel @"funcall" PB.NormalFunCall (PPa.PatchPair oFun pFun)
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

data FnStubKind = DefinedFn | UndefinedFn | SkippedFn | IgnoredFn | DivergedJump
  deriving (Eq, Ord, Show)

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "fnstub" where
  type TraceNodeType '(sym,arch) "fnstub" = String
  type TraceNodeLabel "fnstub" = FnStubKind
  prettyNode DefinedFn nm = "Defined Function stub call:" <+> PP.pretty nm
  prettyNode UndefinedFn nm = "Undefined Function stub call:" <+> PP.pretty nm
  prettyNode SkippedFn _nm = "Skipped unnamed function"
  prettyNode IgnoredFn nm = "Ignoring function:" <+> PP.pretty nm
  prettyNode DivergedJump nm = "Diverging jump:" <+> PP.pretty nm
  nodeTags = mkTags @'(sym,arch) @"fnstub" [Summary, Simplified]
  
-- | Mark the function that this entry belongs to as terminal, indicating
--   that it might have no valid exits (i.e. if a terminal exit is the only
--   return path for the function).
--   This is used to check that the final PairGraph is wellformed (i.e. all
--   non-terminal functions must ultimately have at least one return path).
handleTerminalFunction ::
  NodeEntry arch {- ^ current entry point -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleTerminalFunction node gr = do
  let fPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks node)
  return $ addTerminalNode gr (mkNodeReturn node fPair)

getStubOverrideOne ::
  PB.ConcreteBlock arch bin ->
  Maybe BS.ByteString ->
  EquivM sym arch (Maybe (PA.StubOverride arch))
getStubOverrideOne blk mstubSymbol = do
  PA.SomeValidArch archData <- asks envValidArch
  case mstubSymbol of       
    Just stubSymbol | stubSymbol == skippedFnName -> do
      emitTraceLabel @"fnstub" SkippedFn ""
      return Nothing
    Just stubSymbol | isIgnoredBlock blk -> do
      emitTraceLabel @"fnstub" IgnoredFn (show stubSymbol)
      return Nothing
    Just stubSymbol | Just f <- PA.lookupStubOverride archData stubSymbol -> do
      emitTraceLabel @"fnstub" DefinedFn (show stubSymbol)
      return $ Just f
    Nothing | isIgnoredBlock blk -> do
      emitTraceLabel @"fnstub" IgnoredFn (show skippedFnName)
      return $ Nothing
    _ -> do
      emitTraceLabel @"fnstub" DivergedJump (show (PP.pretty blk))
      return Nothing
      
combineOverrides ::
  PA.StubOverride arch ->
  PA.StubOverride arch ->
  PA.StubOverride arch
combineOverrides (PA.StubOverride f1) (PA.StubOverride f2) = PA.StubOverride $ \sym wsolver -> do
  f1' <- f1 sym wsolver
  f2' <- f2 sym wsolver
  let fnPair = PPa.PatchPair (Const f1') (Const f2')
  return $ PA.StateTransformer $ \(st :: PS.SimState sym arch v bin) -> do
    let Const (PA.StateTransformer fn) = PPa.get @bin fnPair
    fn st

-- We need to make sure that we only "merge" stubs
-- if we have mismatched stubs, otherwise we will
-- break the stub semantics
mergeStubOverrides ::
  PA.ValidArchData arch ->
  StubPair ->
  PPa.PatchPair (Const (Maybe (PA.StubOverride arch))) ->
  PA.StubOverride arch
mergeStubOverrides validArch
  (PPa.PatchPair (Const sym1) (Const sym2))
  (PPa.PatchPair (Const mov1) (Const mov2)) =
  let
    ov1' = case (sym1, mov1) of
        (Just{}, Just ov1) -> ov1
        (Just{}, Nothing) -> PA.defaultStubOverride validArch
        (Nothing,_) -> PA.idStubOverride
    ov2' = case (sym2, mov2) of
        (Just{}, Just ov2) -> ov2
        (Just{}, Nothing) -> PA.defaultStubOverride validArch
        (Nothing,_) -> PA.idStubOverride

  in case (sym1,sym2) of
    (Just nm1, Just nm2) | nm1 == nm2 -> ov1'
    _ -> combineOverrides ov1' ov2' 

bothDefinedOverrides ::
  PPa.PatchPair (Const (Maybe (PA.StubOverride arch))) ->
  Bool
bothDefinedOverrides (PPa.PatchPair (Const (Just{})) (Const (Just{}))) = True
bothDefinedOverrides _ = False


-- | If we have a mismatch in our stub semantics, we need to create
--   a freeze node for whichever binary hit the stub
--   TODO: this is only one case of how we might handle divergent control
--   flow
freezeMismatchedStubs ::
  StubPair ->
  Maybe (Some PBi.WhichBinaryRepr)
freezeMismatchedStubs stubs = case viewStubPair stubs of
  (Just{}, Just{}) -> Nothing
  (Nothing, Just{}) -> Just (Some PBi.PatchedRepr)
  (Just{}, Nothing) -> Just (Some PBi.OriginalRepr)
  -- shouldn't happen when handling stubs, since we have no
  -- stub symbol in this case
  (Nothing, Nothing) -> Nothing



transportStub ::
  StubPair ->
  NodeEntry arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ jump target -} ->
  PPa.PatchPair (PB.ConcreteBlock arch){- ^ return target -} ->
  NodeEntry arch
transportStub stubs currBlock pPair pRetPair = runIdentity $ do
  blks <- PPa.forBins $ \get -> do
    case get stubs of
      -- for an abort stub, we should jump back to the entry point
      -- that caused this
      -- FIXME: this is an approximation that allows us to
      -- continue in the case of divergent control flow,
      -- but is not exactly semantically correct
      Const (Just nm) | isAbortStub nm -> return $ get (nodeBlocks currBlock)
      -- for a normal stub, jump to the return
      Const (Just{}) ->  return $ get pRetPair
      -- otherwise, jump to the actual target
      Const Nothing -> return $ get pPair
  return $ mkNodeEntry currBlock blks

handleStub ::
  HasCallStack =>
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ next entry point -} ->
  Maybe (PPa.PatchPair (PB.ConcreteBlock arch)) {- ^ return point, Nothing for tail calls -} ->
  StubPair {- ^ stub names -} ->
  EquivM sym arch (PairGraph sym arch)
handleStub scope bundle currBlock d gr0_ pPair mpRetPair stubPair = withSym $ \sym -> do   
  gr0 <- case hasTerminalStub stubPair of
    True -> handleTerminalFunction currBlock gr0_
    False -> return gr0_
  case bothTerminalStub stubPair of
    True -> return gr0
    False -> do  
      PA.SomeValidArch archData <- asks envValidArch
      ovPair <- PPa.forBins $ \get -> Const <$> getStubOverrideOne (get pPair) (getConst (get stubPair))
      let ov = mergeStubOverrides archData stubPair ovPair
      wsolver <- getWrappedSolver

      outputs <- catchInIO $ PA.withStubOverride sym wsolver ov $ \f -> PPa.forBins $ \get -> do
        nextSt <- f (PS.simOutState (get (PS.simOut bundle)))
        return $ (get (PS.simOut bundle)) { PS.simOutState = nextSt }
      let bundle' = bundle { PS.simOut = outputs }
      case mpRetPair of
        Just pRetPair -> do
          parents <- asks envParentBlocks
          case (elem pRetPair parents) of
            -- FIXME: evaluate how safe inlining is
            False | bothDefinedOverrides ovPair, False -> do
              --  inline the next blocks
              vars <- PPa.forBins $ \get -> return $ PS.SimVars $ PS.simOutState (get outputs)

              withPair pRetPair $ withSimBundle vars currBlock $ \nextBundle -> withPair (nodeBlocks currBlock) $ do
                processBundle scope currBlock nextBundle d gr0
            _ -> do
              -- for previously-accessed nodes or undefined stubs, we treat it
              -- like a jump
              case freezeMismatchedStubs stubPair of
                Just (Some bin) -> do
                  -- a synthetic graph node representing
                  -- the result of pausing execution on the given
                  -- binary and continuing on the other
                  currBlock' <- asks (PCfg.cfgContextSensitivity . envConfig) >>= \case
                     PCfg.SharedFunctionAbstractDomains -> return currBlock
                     PCfg.DistinctFunctionAbstractDomains -> return $ addContext pRetPair currBlock
                  let
                    -- FIXME: this is a bit weird, since we end up making
                    -- a function that returns into itself for stubs
                    funNode = returnOfEntry currBlock'
                    callNode_ = mkNodeEntry currBlock' pPair
                    callNode = applyFreeze bin callNode_ pRetPair
                    returnSite = freezeNode bin (mkNodeEntry currBlock pRetPair)
                    gr' = addReturnVector gr0 funNode returnSite
                    -- FIXME: return edges?
                  handleJump scope bundle' currBlock d gr' callNode
                Nothing -> do
                  -- in this case
                  -- have inlined the effects of both stubs
                  -- and so diverging control flow is not an issue
                  handleJump scope bundle' currBlock d gr0 (mkNodeEntry currBlock pRetPair)
        -- unclear what to do here?
        Nothing ->
          handleReturn scope bundle' currBlock d gr0

handleReturn ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleReturn scope bundle currBlock d gr =
 do let fPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks currBlock)
    let ret = mkNodeReturn currBlock fPair

    let
      ret_thaw = unfreezeReturn ret
      vecs = getReturnVectors gr ret_thaw
        
    next <- case getFrozen currBlock of
      NotFrozen -> return $ ReturnNode ret
      _ | Set.null vecs -> return $ ReturnNode ret

      FrozenBlock bin -> do
        let bin_other = PBi.flipRepr bin
        -- mark the other binary as having been frozen just before this return
        let blk_swapped = freezeNodeFn bin_other currBlock
        -- virtual jump
        return $ GraphNode blk_swapped
      -- other side is waiting to return, so process the final return now
      FrozenReturn{} -> do
        return $ ReturnNode ret_thaw
    withTracing @"node" next $ 
      widenAlongEdge scope bundle (GraphNode currBlock) d gr next

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


-- | A no-op transition that matches the exit of the given output
noTransition ::
  forall sym arch v bin.
  PS.SimInput sym arch v bin ->
  PS.SimOutput sym arch v (PBi.OtherBinary bin) ->
  EquivM sym arch (PS.SimOutput sym arch v bin)
noTransition simIn_ otherSimOut = withSym $ \sym -> do
  ptr <- PD.concreteToLLVM (PS.simInBlock simIn_)
  blkEnd <- liftIO $ MCS.copyBlockEnd (Proxy @arch) sym ptr (PS.simOutBlockEnd otherSimOut)
  stackBase <- liftIO $ PS.freshStackBase sym (Proxy @arch)
  return $ PS.SimOutput ((PS.simInState simIn_) { PS.simStackBase = stackBase }) blkEnd

mkSimBundleOne ::
  PB.ConcreteBlock arch bin ->
  PS.SimVars sym arch v bin ->
  EquivM sym arch (PS.SimInput sym arch v bin, PS.SimOutput sym arch v bin)
mkSimBundleOne blk vars = do
  let varState = PS.simVarState vars
  absState <- PD.getAbsDomain blk
  let simIn_ = PS.SimInput varState blk absState
  (_asmO, simOut_) <- withRepr (PB.blockBinRepr blk) $ PVSy.simulate simIn_
  return (simIn_, simOut_)


mkSimBundle ::
  NodeEntry arch ->
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  EquivM sym arch (SimBundle sym arch v)
mkSimBundle node vars = do
  case frozenRepr (getFrozen node) of
    -- if one binary is frozen, manufacture a synthetic bundle for it
    Just (Some bin) -> do
      let otherBin = PBi.flipRepr bin
      -- actual transition
      (simInOther, simOutOther) <- mkSimBundleOne (PPa.getPair' otherBin (nodeBlocks node)) (PPa.getPair' otherBin vars)
      let
        var = PPa.getPair' bin vars
        blk = PPa.getPair' bin (nodeBlocks node)
      absState <- PD.getAbsDomain blk
      let simIn_ = PS.SimInput (PS.simVarState var) blk absState
      simOut_ <- noTransition simIn_ simOutOther
      let inputs = PPa.mkPair bin simIn_ simInOther
      let outputs = PPa.mkPair bin simOut_ simOutOther
      return $ SimBundle inputs outputs
    Nothing -> do
      let pPair = nodeBlocks node
      let oVarState = PS.simVarState (PPa.pOriginal vars)
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
