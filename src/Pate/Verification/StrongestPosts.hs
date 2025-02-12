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
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

module Pate.Verification.StrongestPosts
  ( pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import           GHC.Stack ( HasCallStack )

import           Control.Applicative
import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.), (&), (%~) )
import           Control.Monad (foldM, forM, unless, void, when, guard)
import           Control.Monad.IO.Class
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Reader (asks, local)
import           Control.Monad.Except (catchError, throwError)
import           Control.Monad.State.Strict  (get, gets, StateT, runStateT, put, execStateT, modify)
import           Control.Monad.Trans (lift)
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (findIndex, find, (\\))
import           Data.Maybe (mapMaybe, catMaybes)
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
import qualified Data.Quant as Qu
import qualified Data.Parameterized.Map as MapF

import qualified What4.Expr as W4
import qualified What4.Interface as W4
import           What4.SatResult (SatResult(..))
import           What4.SymSequence (SymSequenceTree, reverseSeq, toSequenceTree, ppSeq, compareSymSeq, ppSeqTree, feasiblePaths, shareMuxPrefix, seqTreeElemsSet, seqTreeHeads, seqTreeLasts)

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator.RegValue as LCS
import           Lang.Crucible.Simulator.SymSequence
import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.AbsDomain.AbsState as MAS

--import qualified Pate.Abort as PAb
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import qualified Pate.Discovery.ParsedFunctions as PD
import qualified Pate.Config as PCfg
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PEq
import qualified Pate.Equivalence.MemoryDomain as PEm
import qualified Pate.Equivalence.Condition as PEC
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Event as PE
import qualified Pate.Memory as PM
import qualified Pate.MemCell as PMc
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Location as PL
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import           Pate.Monad.PairGraph
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.StrongestPosts.CounterExample as CE
import qualified Pate.Register.Traversal as PRt
import           Pate.Discovery.PLT (extraJumpClassifier, ExtraJumps(..), ExtraJumpTarget(..))
import qualified Pate.TraceConstraint as PTC

import           Pate.TraceTree
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.ConditionalEquiv as PVC
import qualified Pate.Verification.Simplify as PSi

import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node
import           Pate.Verification.Widening
import qualified Pate.Verification.AbstractDomain as PAD
import Data.Monoid (All(..), Any (..))
import Data.Maybe (fromMaybe, fromJust)
import qualified System.IO as IO
import Control.Monad (forM_)
import qualified Data.Macaw.Discovery as MD
import Data.Foldable (foldl')
import qualified Pate.ExprMappable as PEM
import Pate.Verification.StrongestPosts.CounterExample (RegsCounterExample(..), prettyRegsCE)
import qualified Data.Macaw.BinaryLoader as MBL
import What4.Partial (justPartExpr)
import qualified Data.Aeson as JSON
import qualified Pate.Solver as PSo
import qualified Pate.EventTrace as ET
import Control.Exception (throw)
import qualified What4.ExprHelpers as WEH
import qualified What4.JSON as W4S
import qualified What4.Concrete as W4
import Data.Parameterized.PairF (PairF(..))
import qualified What4.Concrete as W4
import Data.Parameterized (Pair(..))
import qualified Pate.Verification.FnBindings as PFn
import Data.Parameterized.WithRepr (withRepr)

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
    Left err -> return (PE.Errored [err], mempty)
    Right r -> return r
 where
   doVerify :: EquivM sym arch (PE.EquivalenceStatus, PESt.EquivalenceStatistics)
   doVerify = do 
          pg0 <- chooseEntryPoint pPairs emptyPairGraph
          result <- catchError (do
            -- Do the main work of computing the dataflow fixpoint
            pg <- pairGraphComputeFixpoint pPairs pg0
            -- Report a summary of any errors we found during analysis
            pg1 <- handleDanglingReturns pPairs pg
            reportAnalysisErrors (envLogger env) pg1
            return $ pairGraphComputeVerdict pg1) (\err -> return $ PE.Errored [err])

          emitEvent (PE.StrongestPostOverallResult result)

          

          -- TODO, does reporting these kind of statistics make sense for this verification method?
          -- Currently, we only really do this to make the types fit at the call site.
          statVar <- asks envStatistics
          stats <- liftIO $ MVar.readMVar statVar

          return (result, stats)

asEntry :: PB.FunPair arch -> NodeEntry arch
asEntry fnPair = 
  let 
  bPair = PPa.map PB.functionEntryToConcreteBlock fnPair
  in (rootEntry bPair)

asRootEntry :: GraphNode arch -> Maybe (PB.FunPair arch )
asRootEntry (GraphNode ne) = Just (PPa.map PB.blockFunctionEntry (nodeBlocks ne))
asRootEntry (ReturnNode{}) = Nothing

-- FIXME: clagged from initializePairGraph
chooseEntryPoint ::
  [PB.FunPair arch] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
chooseEntryPoint entries pg0 = choose @"node" "Choose Entry Point" $ \choice -> do
  
  let knownRoots = Set.fromList (mapMaybe asRootEntry (getAllNodes pg0))
  let roots = Set.fromList (mapMaybe (\n -> case n of GraphNode ne -> Just (functionEntryOf ne); _ -> Nothing) (getAllNodes pg0))
  let entries' = Set.fromList (map asEntry $ filter (\e -> not (Set.member e knownRoots)) entries)
  -- avoid introducing new top-level entries for functions we've already analyzed
  -- this is a bit clunky and could be done better
  forM_ (Set.union roots entries') $ \nodeEntry -> do
    let node = GraphNode nodeEntry
    choice "" node $ do
      priority <- thisPriority
      let pg1 = emptyWorkList $ dropDomain node (priority PriorityDeferred) pg0
      idom <- initialDomainSpec node
      rootDom <- PS.forSpec idom $ \_ idom' -> do
        vals' <- PPa.forBins $ \bin -> do
          vals <- PPa.get bin (PAD.absDomVals idom')
          -- FIXME: compute this from the global and stack regions
          return $ vals { PAD.absMaxRegion = PAD.AbsIntConstant 3 }
        return $ idom' { PAD.absDomVals = vals' }
      let pg2 = freshDomain pg1 node (priority PriorityUserRequest) rootDom
      let pg3 = emptyReturnVector (dropReturns (returnOfEntry nodeEntry) pg2) (returnOfEntry nodeEntry)
      return pg3

-- | Returns a 'Just' result if we should restart verification after performing
--   some interactive modifications
refineFinalResult ::
  [PB.FunPair arch] ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
refineFinalResult entries pg = do
  shouldAddOrphans <- asks (PCfg.cfgAddOrphanEdges . envConfig)
  withTracing @"message" "Verification Finished" $ do
    choose @"()" "Continue verification?" $ \choice_outer -> do
      choice_outer "Finish and view final result" () $ return Nothing
      choice_outer "Restart from entry point" () $ fmap Just $ do
        pg' <- chooseEntryPoint entries pg
        (asks envResetTraceTree >>= liftIO)
        return pg'
      choice_outer "Handle pending refinements" () $ do
        Just <$> (queuePendingNodes pg)
      let orphans = getOrphanedReturns pg
      case Set.toList orphans of
      -- Orphaned returns can appear when we never find a return branch for
      -- a function (e.g. possibly due to a code analysis failure)
      -- Formally, the analysis can't proceed past any call site for a function
      -- that doesn't return, since we don't know anything about the equivalence post-domain.
      -- Rather than simply giving up at this point, we make a best-effort to
      -- invent a reasonable equivalence post-domain (see 'updateExtraEdges') and
      -- continue the analysis from
      -- all of the (orphaned) return sites for a non-terminating function
        (ret :_) | shouldAddOrphans -> choice_outer ("Add orphaned return node: " ++ show (pretty ret)) () $ fmap Just $ do
          let
            fnEntry = returnToEntry ret
            gr1 = addExtraEdge pg fnEntry (ReturnNode ret)
          case getCurrentDomain gr1 (GraphNode fnEntry) of
            Just preSpec -> PS.viewSpec preSpec $ \scope d -> 
              withValidInit scope (nodeBlocks fnEntry) $ updateExtraEdges scope fnEntry d gr1
            Nothing -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnEntry)
        _ -> return ()

      {-
      choose @"node" "Refine equivalence domain: From" $ \choice_from -> 
        forM_ (getAllNodes pg) $ \from -> do
          let edges = getEdgesFrom pg from
          case null edges of
            True -> return ()
            False -> choice_from "" from $
              choose @"node" "Refine equivalence domain: To" $ \choice_to ->
                forM_ edges $ \to ->
                  choice_to "" to $ do
                    let edge = (from,to)
                    pg' <- addLazyAction edge pg "Refine equivalence domain" $ \choice_act -> do
                      choice_act "Refine and generate equivalence condition" (\x y -> refineEqDomainForEdge edge x y)
                      choice_act "Prune branch for equivalence condition" (\x y -> pruneEdgeForEquality edge x y)
                    Just pg'' <- return $ addToWorkList from pg'
                    return pg''
      -}
{-

  choose @"node" "Refine " $ \choice -> do

    forM_ entries $ \fnPair -> do
      let bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair
      let nd = GraphNode (rootEntry bPair)
      choice "" nd $ case getCurrentDomain pg nd of
        Just{} -> return $ addToWorkList nd pg 
        Nothing -> Just <$> initializePairGraph [fnPair]
-}    
  

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
  let (addrO, addrP) = PPa.view PB.concreteAddress (graphNodeBlocks node)
  case addrO == addrP of
    True -> return True
    False -> not <$> asks (PCfg.cfgIgnoreDivergedControlFlow . envConfig)

handleDanglingReturns ::
  forall sym arch.
  [PB.FunPair arch] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleDanglingReturns fnPairs pg = do
  -- find all the single-sided entry point returns we have domains for
  let is_one_entry (Some fn_single) fnPair = 
       PPa.get (PB.functionBinRepr fn_single) fnPair == Just fn_single
  let single_rets = 
        mapMaybe (\nd -> 
          case nd of
            ReturnNode ret | PPa.PatchPairSingle _ fn_single <- nodeFuns ret,
              any (is_one_entry (Some fn_single)) fnPairs ->
              Just (Some fn_single, ret)
            _ -> Nothing) (getAllNodes pg)
  -- for each single-sided return, see if we can find its corresponding return 
  -- and add that to the graph, to ensure we consider the case where both single-sided
  -- control flows only re-sync when an entry point returns
  let go pg0 (Some (fn_single), ret) = do
        let mdiverged = getDivergePoint (ReturnNode ret)
        let bin = PB.functionBinRepr fn_single
        let (duals :: [NodeReturn arch]) = mapMaybe (\(Some fn_single',ret') -> 
              case testEquality (PBi.flipRepr (PB.functionBinRepr fn_single')) bin of
                Just Refl | getDivergePoint (ReturnNode ret') == mdiverged -> 
                  Just ret'
                _ -> Nothing) single_rets
        case duals of
          [] -> return pg0
          _ -> do
            let fn_single_ = PPa.mkSingle (PB.functionBinRepr fn_single) fn_single
            err <- emitError' (PEE.OrphanedSinglesidedAnalysis fn_single_)
            return $ recordMiscAnalysisError pg0 (ReturnNode ret) err

  foldM go pg single_rets 


addressOfNode ::
  GraphNode arch ->
  EquivM sym arch (PPa.PatchPairC (MM.ArchSegmentOff arch))
addressOfNode nd = PPa.forBinsC $ \bin -> do
  blk <- PPa.get bin (graphNodeBlocks nd)
  blockToSegOff blk

addIntraBlockCut ::
  forall bin sym arch.
  MM.ArchSegmentOff arch ->
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (PB.ConcreteBlock arch bin)
addIntraBlockCut segOff blk = fnTrace "addIntraBlockCut" $ do
  let repr = PB.blockBinRepr blk
  binCtx <- getBinCtx' repr
  let pfm = PMC.parsedFunctionMap binCtx
  liftIO $ PD.addExtraTarget pfm segOff
  PD.ParsedBlocks pblks <- PD.lookupBlocks blk
  forM_ pblks $ \pblk -> emitTrace @"parsedblock" (Some pblk)
  case [ pblk | pblk <- pblks, (MD.pblockAddr pblk) == segOff ] of
    (pblk:_) -> return $ PB.mkConcreteBlock blk PB.BlockEntryJump (MD.pblockAddr pblk)
    _ -> throwHere $ PEE.MissingBlockAtAddress segOff (map MD.pblockAddr pblks) repr blk

chooseDesyncPoint ::
  GraphNode' arch Qu.AllK ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
chooseDesyncPoint dp pg0 = do
  let nd = Qu.coerceToExists dp
  divergePair@(PPa.PatchPairC divergeO divergeP) <- PPa.forBinsC $ \bin -> do
    blk <- PPa.get bin (graphNodeBlocks nd)
    pblks <- PD.lookupBlocks blk
    divergeSingle <- toSingleGraphNode bin nd
    return $ (divergeSingle, Some blk, pblks)
  [Some (PPa.WithBin syncBin _)] <- pickCutPoints False syncMsg
    [divergeO, divergeP]
  let otherBin = PBi.flipRepr syncBin
  diverge <- PPa.getC otherBin divergePair
  _ <- pickCutPoints False syncMsg [diverge]
  return pg0
  where
    syncMsg = "Choose a desynchronization point:"

-- | Given a source divergent node, pick a synchronization point where
--   control flow should again match between the two binaries
chooseSyncPoint :: 
  GraphNode' arch Qu.AllK -> 
  PairGraph sym arch -> 
  EquivM sym arch (PairGraph sym arch)
chooseSyncPoint dp pg0 = do
  let nd = Qu.coerceToExists dp
  (PPa.PatchPairC divergeO divergeP) <- PPa.forBinsC $ \bin -> do
    blk <- PPa.get bin (graphNodeBlocks nd)
    pblks <- PD.lookupBlocks blk
    divergeSingle <- toSingleGraphNode bin nd
    return $ (divergeSingle, Some blk, pblks)
  cuts <- pickCutPoints True syncMsg [divergeO, divergeP]
  execPG pg0 $ forM_ cuts $ \(Some (PPa.WithBin bin addr)) -> do
    addSyncAddress dp bin addr
  where
    syncMsg = "Choose a synchronization point:"

{-
queueSplitAnalysis ::
  GraphNode arch -> 
  PairGraph sym arch -> 
  EquivM sym arch (PairGraph sym arch)
queueSplitAnalysis nd pg = do
  -- we always start the split analysis 
  divergeNodeO <- toSingleGraphNode PBi.OriginalRepr divergeNode
  case getCurrentDomain pg ndO
-}

{-
guessDivergence ::
  GraphNode arch {- divergence point -} -> 
  PairGraph sym arch ->
  EquivM sym arch (Maybe (GraphNode arch))
guessDivergence nd pg = do
  (instrsO,instrsP) <- fmap (PPa.view getConst) $ PPa.forBinsC $ \bin -> do
    blk <- PPa.get bin (graphNodeBlocks nd)
    PD.ParsedBlocks pblks <- PD.lookupBlocks blk
    return $ concat $
      map (\pblk -> 
         mapMaybe (\case { MM.InstructionStart addr txt -> Just (addr, txt, Some pblk); _ -> Nothing }) (MD.pblockStmts pblk)) pblks
  let instrs = zip instrsO instrsP
  let midxDesync = findIndex (\((addrO,txtO,_), (addrP,txtP,_)) -> addrO /= addrP || txtO /= txtP) instrs
  case midxDesync of
    Nothing -> return Nothing
    Just idxDesync -> do
      let (_,(desyncO, desyncP):rest) = splitAt idxDesync instrs
      let midxSync = findIndex (\((_,txtO), (_,txtP)) -> txtO == txtP) rest
      case midxSync of
        Nothing -> return Nothing
        Just idxSync -> return Nothing


  return Nothing
-}

getIntermediateAddrs ::
  forall arch ids.
  PA.ValidArch arch =>
  MD.ParsedBlock arch ids -> 
  [MM.ArchSegmentOff arch]
getIntermediateAddrs pb =
  let
    offs :: [MM.MemWord (MM.ArchAddrWidth arch)]
    offs = catMaybes (map (\case {MM.InstructionStart addr _ -> Just addr; _ -> Nothing}) (MD.pblockStmts pb))

    segOffs :: [Maybe (MM.ArchSegmentOff arch)]
    segOffs = map (\mw -> MM.incSegmentOff @(MM.ArchAddrWidth arch) (MD.pblockAddr pb) (fromIntegral mw)) offs
  in catMaybes $ segOffs

-- | Introduce a cut point (chosen from a list of nodes).
--   Code discovery will consider any CFAR that reaches this cut point to end in a Jump
--   to the next CFAR (i.e. splits a CFAR in two at the given address)
pickCutPoints ::
  Bool {- ^ true if this should keep asking for cut points -} ->
  String ->
  [(GraphNode arch, Some (PB.ConcreteBlock arch), PD.ParsedBlocks arch)] -> 
  EquivM sym arch [Some (PPa.WithBin (PAd.ConcreteAddress arch))]
pickCutPoints pickMany msg inputs = go []
  where
    hasBin bin picked = 
      any (\(Some (PPa.WithBin bin' _)) -> case testEquality bin bin' of Just Refl -> True; _ -> False) picked
    go picked = do
      let addr_opts = 
           [ (show addr ++ " " ++ "(" ++ show bin ++ ")", Just $ Pair concBlk (PPa.WithBin bin addr))
           | (_divergeSingle, Some blk, PD.ParsedBlocks pblks) <- inputs
           , bin <- return $ PB.blockBinRepr blk
           , pblk <- pblks
           , addr <- getIntermediateAddrs pblk
           , concBlk <- return $ PB.mkConcreteBlock blk PB.BlockEntryJump addr
           ]
      let opts = case pickMany && hasBin PBi.OriginalRepr picked && hasBin PBi.PatchedRepr picked of
            True -> addr_opts ++ [("Finish Choosing", Nothing)]
            False -> addr_opts
      -- either generate a menu of alternatives or take text input, based on
      -- the current configuration
      mres <- asks (PCfg.cfgPreferTextInput . envConfig) >>= \case
        True -> chooseInputFromList msg opts
        False -> fmap Just $ 
          choose @"()" msg $ \choice -> forM_ opts $ \(s,v) -> choice s () $ return v 
      case mres of
        Just (Just (Pair blk (PPa.WithBin bin addr))) -> do
          _ <- addIntraBlockCut addr blk
          let x = Some (PPa.WithBin bin (PAd.segOffToAddr addr))
          case pickMany of
            True -> go (x:picked)
            False -> return (x:picked)
        Just Nothing -> return picked
        Nothing -> return picked


-- | Add an intra-block cut to *both* binaries after the given address.
cutAfterAddress :: 
  MM.ArchSegmentOff arch ->
  PB.ConcreteBlock arch bin ->
  EquivM sym arch ()
cutAfterAddress addr blk = do
  PD.ParsedBlocks pblks <- PD.lookupBlocks blk
  let addrs = Set.toList $ Set.fromList $ concat $ map getIntermediateAddrs pblks
  go addrs
  where
    makeCut addr' = PPa.catBins $ \bin -> do
      binCtx <- getBinCtx' bin
      let pfm = PMC.parsedFunctionMap binCtx
      liftIO $ PD.addExtraTarget pfm addr'
  
    go [] = return ()
    go [_addr'] = return ()
    go (addr_this:addr_next:addrs) = case addr_this == addr of
      True -> makeCut addr_next
      False -> go (addr_next:addrs)

addImmediateEqDomRefinementChoice ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  PAD.AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
addImmediateEqDomRefinementChoice scope nd preD gr0 = do
  let gr1 = gr0
  choose @"()" ("Refine equivalence domain for sync point?") $ \choice -> do
    let go condK = do
          let msg = conditionAction condK
          choice (msg ++ " condition") () $ do
            locFilter <- refineEquivalenceDomain preD
            return $ addDomainRefinement nd (LocationRefinement condK RefineUsingExactEquality (PS.mkSimSpec scope locFilter)) gr1
          choice (msg ++ " condition (using intra-block path conditions)") () $ do
            locFilter <- refineEquivalenceDomain preD
            return $ addDomainRefinement nd (LocationRefinement condK RefineUsingIntraBlockPaths (PS.mkSimSpec scope locFilter)) gr1
          choice (msg ++ " that branch is infeasible") () $
            return $ addDomainRefinement nd (PruneBranch condK) gr1
    choice ("No refinements") () $ return gr1
    mapM_ go [minBound..maxBound]

-- | Connect the divergence point to the start of the single-sided analysis
--   If there is no single-sided domain, then it is initialized to be the split
--   version of the two-sided analysis.
initSingleSidedDomain ::
  forall sym arch bin.
  SingleNodeEntry arch bin ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
initSingleSidedDomain sne pg0 = withRepr bin $ withRepr (PBi.flipRepr bin) $ withSym $ \sym -> withPG_ pg0 $ do
  let dp = singleNodeDivergePoint (GraphNode sne)
  let nd = Qu.coerceToExists dp
  pr <- lift $ currentPriority

  nd' <- case Qu.convertQuant nd of
    Just (nd' :: GraphNode' arch Qu.AllK) -> return nd'
    Nothing -> fail $ "Unexpected single-sided diverge point: " ++ show nd
  let nd_single = GraphNode (singleToNodeEntry sne)
  dom_spec <- liftPG $ getCurrentDomainM nd
  PS.forSpec dom_spec $ \scope dom -> do
    dom_single <- PAD.singletonDomain bin dom
    {-
    case getCurrentDomain pg0 nd_single of
      Just{} -> return ()
      Nothing -> do
        emitTrace @"message" "init single-sided domain"
        let dom_single_spec = PS.mkSimSpec scope dom_single
        liftPG $ modify $ \pg -> initDomain pg nd nd_single (priority PriorityHandleDesync) dom_single_spec
    -}
    let (sne_other :: SingleGraphNode arch (PBi.OtherBinary bin)) = Qu.coerceQuant nd'
    
    bundle <- lift $ noopBundle scope (graphNodeBlocks nd)
    mbindsThis <- lift $ lookupFnBindings scope (GraphNode sne) pg0
    mbindsOther <- lift $ lookupFnBindings scope sne_other pg0

    let rewrite_cond condK exprBinds pg = fnTrace "rewrite_cond" $ case getCondition pg nd condK of
          Just condSpec -> do
            cond <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) condSpec
            cond' <- PSi.applySimpStrategy (PSi.rewriteStrategy exprBinds) cond
            let condSpec' = PS.mkSimSpec scope cond'
            let propK = getPropagationKind pg nd condK
            let pg' = setCondition nd condK propK condSpec' pg
            -- we need to schedule the ancestors here to ensure that the resulting
            -- assertion is propagated (if needed), since 'propagateOne' doesn't do this step
            return $ queueAncestors (lowerPriority pr) nd pg'

          Nothing -> return pg

    let do_widen binds pg = fnTrace "do_widen" $ do
          atPriority (raisePriority pr) (Just "Starting Split Analysis") $  do
            pg2 <- propagateOne scope bundle [ConditionAssumed, ConditionEquiv] dom nd nd_single ConditionAsserted pg >>= \case
              (ConditionNotPropagated, pg1) -> return pg1
              (ConditionPropagated preconds, pg1) -> foldM (\pg_ condK -> rewrite_cond condK binds pg_) pg1 (ConditionAsserted:preconds) 
              (ConditionInfeasible, pg1) -> rewrite_cond ConditionAsserted binds pg1

            withAssumptionSet (PAS.fromExprBindings binds) $ withGraphNode' scope nd bundle dom pg2 $ do
              widenAlongEdge scope bundle nd dom_single pg2 nd_single

          
    case (mbindsThis, mbindsOther) of

      (Just bindsThis, Just bindsOther) -> do
        emitTrace @"debug" "Case: Bindings on both sides"
        binds <- IO.liftIO $ WEH.mergeBindings sym (PFn.toExprBindings bindsThis) (PFn.toExprBindings bindsOther) 
        liftEqM_ $ \pg -> do_widen binds pg
      (Just{}, Nothing) -> do
        emitTrace @"debug" "Case: Bindings on only this side"
        
        -- Should we lower the priority here? Is it possible to get caught in a loop otherwise?
        -- Formally we should be able to find all relevant nodes based on which bindings
        -- we're missing
        liftPG $ getAllSyncPoints dp >>= \syncs -> forM_ syncs $ \syncPair -> do
          sp <- PPa.get (PBi.flipRepr bin) syncPair
          modify $ queueAncestors pr (GraphNode $ singleToNodeEntry (syncPointNode sp))
 
      (Nothing, Just bindsOther) -> do
        emitTrace @"debug" "Case: Bindings on only other side"
        let binds = PFn.toExprBindings bindsOther
        liftEqM_ $ \pg -> do_widen binds pg
      (Nothing, Nothing) -> do
        emitTrace @"debug" "Case: No bindings"
        liftEqM_ $ do_widen MapF.empty
    
    return (PS.WithScope ())
  where
    bin = singleNodeRepr (GraphNode sne)

withGraphNode' ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch) ->
  EquivM sym arch (PairGraph sym arch)
withGraphNode' scope nd bundle dom pg f = case nd of
  GraphNode ne -> withPredomain scope bundle dom $ withAbsDomain ne dom pg $ withValidInit scope (nodeBlocks ne) $
     withConditionsAssumed scope bundle dom nd pg $ f
  ReturnNode nr -> withPredomain scope bundle dom $ withConditionsAssumed scope bundle dom (ReturnNode nr) pg $
    f


handleProcessSplit ::
  SingleNodeEntry arch bin ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (GraphNode arch), PairGraph sym arch)
handleProcessSplit sne pg = withPG pg $ do
  let divergeNode = singleNodeDivergence sne
  priority <- lift $ thisPriority
  case getCurrentDomain pg divergeNode of
    Nothing -> do
      liftPG $ modify $ queueAncestors (priority PriorityDomainRefresh) (Qu.coerceToExists divergeNode)
      return Nothing
    Just{} -> do
      let nd = GraphNode (singleToNodeEntry sne)
      liftEqM_ $ initSingleSidedDomain sne
      return $ Just nd

handleProcessMerge ::
  SingleNodeEntry arch PBi.Original ->
  SingleNodeEntry arch PBi.Patched ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (GraphNode arch), PairGraph sym arch)
handleProcessMerge sneO sneP pg = withPG pg $ do
  let
    ndO = GraphNode $ singleToNodeEntry sneO
    ndP = GraphNode $ singleToNodeEntry sneP
    divergeNode = singleNodeDivergence sneO
  priority <- lift $ thisPriority
  case getCurrentDomain pg divergeNode of
    Nothing -> do
      liftPG $ modify $ queueNode (priority PriorityDomainRefresh) divergeNode
      return Nothing
    Just{} -> do
      case (getCurrentDomain pg ndO, getCurrentDomain pg ndP) of
        (Just{}, Just{}) -> do
          syncNode <- liftEqM $ mergeSingletons sneO sneP

          return $ Just $ GraphNode syncNode
        _ -> do
          liftPG $ modify $ queueNode (priority PriorityDomainRefresh) divergeNode
          return Nothing
{-
workItemDomainSpec ::
  WorkItem arch ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (GraphNode arch, PAD.AbstractDomainSpec sym arch), PairGraph sym arch)
workItemDomainSpec wi pg = withPG pg $ case wi of
  ProcessNode nd -> do
    dom <- liftPG $ getCurrentDomainM nd
    return $ Just (nd, dom)
  ProcessSplit sne -> do
    let divergeNode = singleNodeDivergePoint sne
    priority <- lift $ thisPriority
    case getCurrentDomain pg divergeNode of
      Nothing -> do
        liftPG $ modify $ queueNode (priority PriorityDomainRefresh) divergeNode
        return Nothing
      Just{} -> do
        liftEqM_ $ initSingleSidedDomain sne
        let nd = GraphNode (singleToNodeEntry sne)
        dom <- liftPG $ getCurrentDomainM nd
        return $ Just (nd, dom)

  ProcessMerge sneO sneP -> do
    let
      ndO = GraphNode $ singleToNodeEntry sneO
      ndP = GraphNode $ singleToNodeEntry sneP
      divergeNode = singleNodeDivergePoint sneO
    priority <- lift $ thisPriority
    case getCurrentDomain pg divergeNode of
      Nothing -> do
        liftPG $ modify $ queueNode (priority PriorityDomainRefresh) divergeNode
        return Nothing
      Just{} -> do
        case (getCurrentDomain pg ndO, getCurrentDomain pg ndP) of
          (Just{}, Just{}) -> do
            syncNode <- liftEqM $ mergeSingletons sneO sneP
            dom_spec <- liftPG $ getCurrentDomainM (GraphNode syncNode)
            return $ Just (GraphNode syncNode, dom_spec)
          _ -> do
            liftPG $ modify $ queueNode (priority PriorityDomainRefresh) divergeNode
            return Nothing
-}

mergeSingletons ::
  forall sym arch.
  SingleNodeEntry arch PBi.Original ->
  SingleNodeEntry arch PBi.Patched ->
  PairGraph sym arch ->
  EquivM sym arch (NodeEntry arch, PairGraph sym arch)
mergeSingletons sneO sneP pg = fnTrace "mergeSingletons" $ withSym $ \sym -> do
  let 
    blkO = singleNodeBlock sneO
    blkP = singleNodeBlock sneP
    blkPair = PPa.PatchPair blkO blkP

  syncNodeEntry <- case combineSingleEntries sneO sneP of
    Just ne -> return ne
    Nothing -> throwHere $ PEE.IncompatibleSingletonNodes blkO blkP
  
  let dp = singleNodeDivergence sneO
  let nd = Qu.coerceToExists dp

  let syncNode = GraphNode syncNodeEntry
  let snePair = Qu.QuantEach (\case PBi.OriginalRepr -> sneO; PBi.PatchedRepr -> sneP)

  -- we start with two scopes: one representing the program state at the point of divergence: 'init_scope',
  -- and one representing the program state at the merge point
  
  pg_final <- withFreshScope (graphNodeBlocks nd) $ \(splitScope :: PS.SimScope sym arch init) -> do
    withFreshScope blkPair $ \(mergeScope :: PS.SimScope sym arch merge) -> do
      ((sbundlePair@(PPa.PatchPair sbundleO sbundleP)), pg') <- mergeBundles splitScope mergeScope snePair pg
      dpDomSpec <- evalPG pg $ getCurrentDomainM nd
      -- domain at the divergence point
      dpDom <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair splitScope) dpDomSpec
      noop <- noopBundle splitScope (graphNodeBlocks nd)


      withValidInit splitScope (graphNodeBlocks nd) $ 
        withPredomain splitScope noop dpDom $
        withValidInit (singleBundleScope sbundleO) (singleBundleBlocks sbundleO) $
        withValidInit (singleBundleScope sbundleP) (singleBundleBlocks sbundleP) $
        withPredomain (singleBundleScope sbundleO) (singleBundle sbundleO) (singleBundleDomain sbundleO) $
        withPredomain (singleBundleScope sbundleP) (singleBundle sbundleP) (singleBundleDomain sbundleP) $
        withConditionsAssumed (singleBundleScope sbundleO) (singleBundle sbundleO) (singleBundleDomain sbundleO) (GraphNode $ singleToNodeEntry sneO) pg' $
        withConditionsAssumed (singleBundleScope sbundleP) (singleBundle sbundleP) (singleBundleDomain sbundleP) (GraphNode $ singleToNodeEntry sneP) pg' $ do
          
          bindsOAsm <- IO.liftIO $ PFn.toPred sym $ singleBundleBinds sbundleO
          bindsPAsm <- IO.liftIO $ PFn.toPred sym $ singleBundleBinds sbundleP
          bindsAsms <- IO.liftIO $ W4.andPred sym bindsOAsm bindsPAsm
          
          withAssumption bindsAsms $ do
            let
              collectCondition :: forall bin v. PBi.WhichBinaryRepr bin -> GraphNode arch -> PairGraph sym arch -> ConditionKind -> PFn.FnBindings sym (PBi.OtherBinary bin) v -> PFn.FnBindings sym (PBi.OtherBinary bin) v
              collectCondition _ nd pg_ condK binds_acc = do
                case getCondition pg_ nd condK of
                  Just condSpec -> PS.viewSpecBody condSpec $ \cond -> PFn.addUsedFns sym cond binds_acc
                  Nothing -> binds_acc
              
            (new_bind_asms, pg'') <- withPG pg' $ PPa.forBinsC $ \bin -> do
              sbundle <- PPa.get bin sbundlePair
              let sne = Qu.quantEach snePair bin
              let sne_other = Qu.quantEach snePair (PBi.flipRepr bin) 
              let nd = GraphNode $ singleToNodeEntry sne
              let scope = singleBundleScope sbundle

              liftEqM $ \pg_ -> propagateOne scope  (singleBundle sbundle) [ConditionAssumed, ConditionEquiv] (singleBundleDomain sbundle) nd syncNode ConditionAsserted pg_ >>= \case
                (ConditionNotPropagated, _) -> 
                  -- bindings already assumed above
                  return (W4.truePred sym, pg_)
                (_, pg_') -> do
                  let binds_other = foldr (collectCondition bin nd pg_') (singleBundleBinds sbundle) [minBound .. maxBound]
                  priority <- thisPriority
                  (binds, pg_'') <- IO.liftIO $ addFnBindings sym mergeScope (GraphNode sne_other) binds_other pg_'
                  binds_asm <- IO.liftIO $ PFn.toPred sym binds
                  return $ (binds_asm, queueAncestors (priority PriorityHandleDesync) nd pg_'')
            
            new_bind_asm <- PPa.joinPatchPred (\x y -> IO.liftIO $ W4.andPred sym x y) $ \bin -> 
              PPa.getC bin new_bind_asms

            withAssumption new_bind_asm $
              withPG_ pg'' $ PPa.catBins $ \bin -> do
                liftEqM_ $ \pg_ -> do
                  sbundle <- PPa.get bin sbundlePair
                  let sne = Qu.quantEach snePair bin
                  let nd = GraphNode $ singleToNodeEntry sne
                  let scope = singleBundleScope sbundle
                  withConditionsAssumed scope (singleBundle sbundle) (singleBundleDomain sbundle) nd pg_ $
                    widenAlongEdge scope (singleBundle sbundle) nd (singleBundleDomain sbundle) pg_ syncNode

  return (syncNodeEntry, pg_final)

-- | Choose some work item (optionally interactively)
withWorkItem ::
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  PairGraph sym arch ->
  ((NodePriority, PairGraph sym arch, WorkItem arch, PAD.AbstractDomainSpec sym arch) -> EquivM_ sym arch a) ->
  NodeBuilderT '(sym,arch) "node" (EquivM_ sym arch) (Maybe a)
withWorkItem gr0 f = do
  gr0' <- lift $ queuePendingNodes gr0
  case chooseWorkItem gr0' of
    Nothing -> return Nothing
    Just (priority, gr1, wi) ->  do
      let nd = workItemNode wi
      res <- subTraceLabel @"node" (printPriorityKind priority) nd $ atPriority priority Nothing $ do
        (mnext, gr2) <- case wi of
          ProcessNode _ (GraphNode ne) | Just (Some (Qu.AsSingle sne)) <- asSingleNodeEntry ne -> do
            (evalPG gr1 $ isSyncNode sne) >>= \case
              True -> do
                gr2 <- execPG gr1 $ queueExitMerges (\pk -> mkPriority pk priority) (SyncAtStart sne)
                return $ (Nothing, gr2)
              False -> processNode (GraphNode ne) gr1
          ProcessNode True nd' -> do
            emitTrace @"debug" $ "ProcessNode: " ++ show nd'
            p <- thisPriority
            (isSync, gr2) <- (runPG gr1 $ queueSyncNodeMerge p nd')
            case isSync of
              True -> do
                emitTrace @"debug" $ "Sync node found, scheduling merge"
                return (Nothing, gr2)
              False -> processNode nd' gr1
          ProcessNode False nd' -> do
            emitTrace @"debug" $ "ProcessNode: (no merge) " ++ show nd'
            processNode nd' gr1
          ProcessSplit sne -> do
            emitTrace @"debug" $ "ProcessSplit: " ++ show sne
            handleProcessSplit sne gr1
          ProcessMerge sneO sneP -> do
            emitTrace @"debug" $ "ProcessMerge: " ++ show sneO ++ " vs. " ++ show sneP
            (mnext, gr2) <- handleProcessMerge sneO sneP gr1
            case mnext of
              Just next -> do
                  emitTrace @"debug" $ "Drop and re-queue: " ++ show next
                  let gr3 = queueWorkItem priority (ProcessNode False next) $ dropWorkItem (ProcessNode True next) gr2
                  return $ (Nothing, gr3)
              Nothing -> do
                emitTrace @"debug" $ "No merge possible"
                return (Nothing, gr2)
        case (mnext, getCurrentDomain gr2 nd) of
          (Just next, Just spec) | next == nd -> fmap Right $ f (priority, gr2, wi, spec)
          _ -> return $ Left (mnext, gr2)
      case res of
        (Left ((Just next), gr2)) -> do
          case getCurrentDomain gr2 next of
            Just spec -> subTraceLabel @"node" (printPriorityKind priority) next $ 
              atPriority priority Nothing $ (Just <$> (f (priority, gr2, wi, spec)))
            -- we are missing the expected domain, so we need to just try again
            Nothing -> do

              withWorkItem (queueWorkItem priority wi gr2) f 
        Left (Nothing, gr2) ->  withWorkItem gr2 f
        Right a -> return $ Just a
  where
    processNode :: 
      GraphNode arch -> 
      PairGraph sym arch ->
      EquivM sym arch (Maybe (GraphNode arch), PairGraph sym arch)  
    processNode nd gr1 = do
      case getCurrentDomain gr1 nd of
        Just spec -> do
          PS.viewSpec spec $ \scope d -> do
            emitTrace @"debug" $ "runPendingActions"
            runPendingActions refineActions nd (TupleF2 scope d) gr1 >>= \case
              Just gr2 -> do
                emitTrace @"debug" $ "Actions Executed, returning..."
                return $ (Nothing, gr2)
              Nothing -> return $ (Just nd, gr1)
        Nothing -> fail $ "Missing domain for: " ++ show nd

-- | Execute the forward dataflow fixpoint algorithm.
--   Visit nodes and compute abstract domains until we propagate information
--   to all reachable positions in the program graph and we reach stability,
--   or until we run out of gas.
--
--   TODO, could also imagine putting timeouts/compute time limits here.
pairGraphComputeFixpoint ::
  forall sym arch. [PB.FunPair arch] -> PairGraph sym arch -> EquivM sym arch (PairGraph sym arch)
pairGraphComputeFixpoint entries gr_init = do
  let
    go (gr0 :: PairGraph sym arch) = do
      mgr4 <- withWorkItem gr0 $ \(priority, gr1, wi, preSpec) -> do
        let nd = workItemNode wi
        shouldProcessNode nd >>= \case
          False -> do
            emitWarning $ PEE.SkippedInequivalentBlocks (graphNodeBlocks nd)
            return gr1
          True -> do
            emitTrace @"priority" priority
            atPriority priority (Just (show nd)) $ do
              PS.viewSpec preSpec $ \scope d -> do
                d' <- asks (PCfg.cfgStackScopeAssume . envConfig) >>= \case
                  True -> strengthenStackDomain scope d
                  False -> return d
                gr2 <- addRefinementChoice nd gr1
                gr3 <- visitNode scope wi d' gr2
                emitEvent $ PE.VisitedNode nd
                return gr3
      case mgr4 of
        Just gr4 -> go gr4
        Nothing -> return gr0
    
    go_outer :: PairGraph sym arch -> EquivM_ sym arch (PairGraph sym arch)
    go_outer gr = do
      gr1 <- withSubTraces $ go gr
      gr2 <- handleDanglingReturns entries gr1
      refineFinalResult entries gr2 >>= \case
        Just gr3 -> go_outer gr3
        Nothing -> showFinalResult gr2 >> return gr2
  go_outer gr_init

clearTrivialCondition :: 
  GraphNode arch -> 
  ConditionKind -> 
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
clearTrivialCondition nd condK pg = case getCondition pg nd ConditionEquiv of
  Just cond_spec -> PS.viewSpec cond_spec $ \scope cond -> withSym $ \sym -> do
    ((), pg1) <- withNoTracing $ withGraphNode scope nd pg $ \_bundle _d -> do
      heuristicTimeout <- asks (PCfg.cfgHeuristicTimeout . envConfig)
      cond_pred <- PEC.toPred sym cond
      isPredTrue' heuristicTimeout cond_pred >>= \case
        True ->  return $ ((), dropCondition nd condK pg)
        False -> return ((), pg)
    return pg1
  Nothing -> return pg

-- | Context needed to re-generate traces when adding trace constraints
data IntermediateEqCond sym arch v = 
  IntermediateEqCond
    { ieqBundle :: SimBundle sym arch v
    , ieqFootprints:: PPa.PatchPairC (CE.TraceFootprint sym arch, JSON.Value)
    , ieqEnv :: W4S.ExprEnv sym
    , ieqAsms :: PAS.AssumptionSet sym
    , ieqCond :: W4.Pred sym
    , ieqDom :: AbstractDomain sym arch v
    }

data EqCondCollector sym arch = EqCondCollector
  { eqCondFinals :: Map.Map (GraphNode arch) (ConditionTraces sym arch)
  , eqCondInterims :: Map.Map (GraphNode arch) (PS.SimSpec sym arch (IntermediateEqCond sym arch))
  , eqCondConstraints :: PTC.TraceConstraintMap sym arch
  }

getExprEnvs :: EqCondCollector sym arch -> Map.Map (GraphNode arch) (W4S.ExprEnv sym)
getExprEnvs st = fmap (\spec -> PS.viewSpecBody spec ieqEnv) (eqCondInterims st)

showFinalResult :: forall sym arch. PairGraph sym arch -> EquivM sym arch ()
showFinalResult pg0 = withTracing @"final_result" () $ withSym $ \sym -> do
  st <- go (EqCondCollector Map.empty Map.empty (PTC.TraceConstraintMap Map.empty))
  add_constraints <- asks (PCfg.cfgTraceConstraints . envConfig)
  case add_constraints of
    True -> 
      let loop st_ = chooseBool "Regenerate result with new trace constraints?" >>= \case
            True -> do
              tcs <- PTC.readConstraintMap sym "Waiting for constraints.." (Map.toAscList (getExprEnvs st_))
              go (st_ {eqCondConstraints = tcs}) >>= loop
            False -> return ()
      in loop st
    False -> return ()

  where
    mkEqCond ::
      EqCondCollector sym arch ->
      GraphNode arch -> 
      NodeBuilderT '(sym,arch) "node" (EquivM_ sym arch) (EqCondCollector sym arch)
    mkEqCond rs nd  = do
      pg <- lift $ clearTrivialCondition nd ConditionEquiv pg0
      let PTC.TraceConstraintMap tcm = eqCondConstraints rs

      
      let
        rest :: forall v. PS.SimScope sym arch v -> IntermediateEqCond sym arch v -> EquivM_ sym arch (Maybe (ConditionTraces sym arch))
        rest scope (IntermediateEqCond bundle fps _ _ cond d) =  withSym $ \sym -> do
          trace_constraint <- case Map.lookup nd tcm of
            Just tc -> IO.liftIO $ PTC.constraintListToPred sym tc
            Nothing -> return $ W4.truePred sym
          mres <- withSatAssumption (PAS.fromPred trace_constraint) $ do
            (mtraceT, mtraceF) <- getTracesForPred scope bundle d cond
            case (mtraceT, mtraceF) of
              (Nothing, Nothing) -> return Nothing
              _ -> do
                cond_pretty <- PSi.applySimpStrategy PSi.prettySimplifier cond
                return $ Just (ConditionTraces cond_pretty mtraceT mtraceF fps)
              
          case mres of
            Just res -> return res
            Nothing -> emitWarning PEE.UnsatisfiableAssumptions >> return Nothing

      case Map.lookup nd (eqCondInterims rs) of
        Just ieqcspec -> subTrace nd $ PS.viewSpec ieqcspec $ \scope ieqc -> withAssumptionSet (ieqAsms ieqc) $ do
          rest scope ieqc >>= \case
            Just fcond -> return (rs { eqCondFinals = Map.insert nd fcond (eqCondFinals rs) })
            Nothing -> return rs
        Nothing -> case getCondition pg nd ConditionEquiv of
          Just cond_spec -> subTrace nd $ withSym $ \sym -> do
            withFreshScope (graphNodeBlocks nd) $ \scope -> do
              cond <- IO.liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) cond_spec
              fmap fst $ withGraphNode scope nd pg $ \bundle d -> do
                cond_simplified <- PSi.applySimpStrategy PSi.deepPredicateSimplifier cond
                eqCond_pred <- PEC.toPred sym cond_simplified
                (partialTraces, eenv) <- toConditionTraces scope bundle eqCond_pred Nothing Nothing
                let fpvs = eqFootprints partialTraces
                asms <- currentAsm
                let ieqc = IntermediateEqCond bundle fpvs eenv asms eqCond_pred d 
                let interims = Map.insert nd (PS.mkSimSpec scope ieqc) (eqCondInterims rs)
                rest scope ieqc >>= \case
                  Just fcond -> return (rs { eqCondFinals = Map.insert nd fcond (eqCondFinals rs), eqCondInterims = interims }, pg)
                  Nothing -> return (rs { eqCondInterims = interims }, pg)
          Nothing -> return rs

    go :: EqCondCollector sym arch -> EquivM sym arch (EqCondCollector sym arch)
    go rs = do
        subTree @"node" "Observable Counter-examples" $ do
          forM_ (Map.toList (pairGraphObservableReports pg0)) $ \(nd,report) -> 
            subTrace (GraphNode nd) $ 
              emitTrace @"observable_result" (CE.ObservableCheckCounterexample report)
        
        rs' <- subTree @"node" "Assumed Equivalence Conditions" $ 
          foldM mkEqCond (rs { eqCondFinals = Map.empty }) (getAllNodes pg0)
        let result = pairGraphComputeVerdict pg0
        emitTrace @"equivalence_result" result

        let toplevel_result = FinalResult result (pairGraphObservableReports pg0) (eqCondFinals rs')
        emitTrace @"toplevel_result" toplevel_result
        return rs'

data FinalResult sym arch = FinalResult
  { 
    _finEqStatus :: PE.EquivalenceStatus
  , _finObservableCE ::  Map.Map (NodeEntry arch) (CE.ObservableCounterexample sym arch)
  , _finEqConds :: Map.Map (GraphNode arch) (ConditionTraces sym arch)
  }

data ConditionTraces sym arch = ConditionTraces
  { 
    _eqCondPred :: W4.Pred sym
  , _eqCondTraceTrue :: Maybe (CE.TraceEvents sym arch)
  , _eqCondTraceFalse :: Maybe (CE.TraceEvents sym arch)
  -- small hack to include the footprint serialized according to the expression environment
  , eqFootprints :: PPa.PatchPairC (CE.TraceFootprint sym arch, JSON.Value)
  }

instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "condition_traces" where
  type TraceNodeType '(sym,arch) "condition_traces" = ConditionTraces sym arch
  prettyNode _ _ = "Condition Traces"
  nodeTags = mkTags @'(sym, arch) @"condition_traces" [Simplified, Summary]
  jsonNode sym () v = W4S.w4ToJSON sym v


toConditionTraces :: 
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  W4.Pred sym ->
  Maybe (CE.TraceEvents sym arch) -> 
  Maybe (CE.TraceEvents sym arch) ->
  EquivM sym arch (ConditionTraces sym arch, W4S.ExprEnv sym)
toConditionTraces scope bundle p mtraceT mtraceF = withSym $ \sym -> do
  fps <- getTraceFootprint scope bundle
  vs <- PPa.forBinsC $ \bin -> do
    fp <- PPa.getC bin fps
    (v, env) <- liftIO $ W4S.w4ToJSONEnv sym fp
    -- only visible with debug tag
    emitTraceLabel @"trace_footprint" v fp
    return (v, env)
  eenv <- PPa.joinPatchPred (\a b -> return $ W4S.mergeEnvs a b) $ \bin -> snd <$> (PPa.getC bin vs)
  fpvs <- PPa.forBinsC $ \bin -> do
    fp <- PPa.getC bin fps
    (v,_) <- PPa.getC bin vs
    return (fp,v)
  return (ConditionTraces p mtraceT mtraceF fpvs, eenv)

instance W4S.W4Serializable sym (PEq.EquivalenceStatus) where
  w4Serialize st = do
    let (simple :: String) = case st of
          PEq.Equivalent -> "Equivalent"
          PEq.Inequivalent{} -> "Inequivalent"
          PEq.ConditionallyEquivalent -> "ConditionallyEquivalent"
          PEq.Errored{} -> "Errored"
    simpleJSON <- W4S.w4SerializeString simple
    message <- W4S.w4SerializeString (PP.pretty st)
    W4S.object [ "simple" W4S..= simpleJSON, "message" W4S..= message ]

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (FinalResult sym arch) where
  w4Serialize (FinalResult st obs conds) = do
    W4S.object [ "eq_status" W4S..= st, "observable_counterexamples" W4S..= obs, "eq_conditions" W4S..= conds ]

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (ConditionTraces sym arch) where
  w4Serialize (ConditionTraces p trT trF fps) = do
    W4S.object [ "predicate" W4S..== p, "trace_true" W4S..= trT, "trace_false" W4S..= trF, "trace_footprint" W4S..= (PPa.map (\(Const(_,v)) -> Const v) fps) ]


instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "toplevel_result" where
  type TraceNodeType '(sym,arch) "toplevel_result" = FinalResult sym arch
  prettyNode () _ = "Toplevel Result"
  nodeTags = mkTags @'(sym, arch) @"toplevel_result" [Simplified, Summary]
  jsonNode sym () v = W4S.w4ToJSON sym v

-- | Run a 'PairGraph' computation in the assumption context of
--   a given 'GraphNode'
--   This is a subset of the steps taken in 'visitNode' which
--   sets up the context before performing code discovery and
--   domain widening.
withGraphNode ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  PairGraph sym arch ->
  (PS.SimBundle sym arch v ->
   AbstractDomain sym arch v ->
   EquivM_ sym arch (a, PairGraph sym arch)) ->
  EquivM sym arch (a, PairGraph sym arch)
withGraphNode scope nd pg f = withSym $ \sym -> do
  case getCurrentDomain pg nd of
    Nothing | GraphNode ne <- nd -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks ne)
    Nothing | ReturnNode nr <- nd -> throwHere $ PEE.MissingDomainForFun (nodeFuns nr)
    Just dom_spec ->  do
      d <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) dom_spec
      case nd of
        GraphNode ne -> withAbsDomain ne d pg $ withValidInit scope (nodeBlocks ne) $
          withSimBundle pg (PS.scopeVars scope) ne $ \bundle ->
            withPredomain scope bundle d $
              {- withConditionsAssumed scope bundle d nd pg $ -}
                f bundle d
        ReturnNode nr -> do
          bundle <- noopBundle scope (graphNodeBlocks (ReturnNode nr))
          withPredomain scope bundle d $
            {- withConditionsAssumed scope bundle d (ReturnNode nr) pg $ -}
              f bundle d


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
  simIn_ <- PPa.forBins $ \bin -> do
    blk <- PPa.get bin pPair
    vars' <- PPa.get bin vars
    absSt <- PD.getAbsDomain blk
    return $ PS.SimInput (PS.simVarState vars') blk absSt

  wsolver <- getWrappedSolver

  -- FIXME: should we pass in the archInfo for each binary to each stub separately?
  -- currently it's only used to get the architecture endianness, which realistically
  -- shouldn't change between the patched and original binaries
  origBinary <- PMC.binary <$> getBinCtx' PBi.OriginalRepr
  let archInfo = PA.binArchInfo origBinary

  simOut_ <- IO.withRunInIO $ \runInIO ->
    PA.withStubOverride sym archInfo wsolver ov $ \f -> runInIO $ do
      outSt <- liftIO $ f (PPa.map PS.simInState simIn_)
      blkend <- liftIO $ MCS.initBlockEnd (Proxy @arch) sym MCS.MacawBlockEndReturn
      return $ PPa.map (\st' -> PS.SimOutput st' blkend) outSt

  return $ PS.SimBundle simIn_ simOut_

-- | Bundle that does nothing but end in a jump
noopBundle :: forall sym arch v.
  HasCallStack =>
  PS.SimScope sym arch v ->
  PB.BlockPair arch {- ^ block pair being returned to -} ->
  EquivM sym arch (SimBundle sym arch v)
noopBundle scope pPair = withSym $ \sym -> do
  let vars = PS.scopeVars scope
  simIn_ <- PPa.forBins $ \bin -> do
    blk <- PPa.get bin pPair
    absSt <- PD.getAbsDomain blk
    vars' <- PPa.get bin vars
    return $ PS.SimInput (PS.simVarState vars') blk absSt
  blockEndVal <- liftIO (MCS.initBlockEnd (Proxy @arch) sym MCS.MacawBlockEndJump)

  simOut_ <- PPa.forBins $ \bin -> do
    input <- PPa.get bin simIn_
    return $ PS.SimOutput (PS.simInState input) blockEndVal

  return $ SimBundle simIn_ simOut_

-- | Bundle that transitions from a single-sided analysis to a two-sided analysis.
--   FIXME: do we actually need the bindings here?
data SingleBundle sym arch (v_split :: PS.VarScope) (v_merge :: PS.VarScope) bin where
   SingleBundle ::
    { singleBundle :: SimBundle sym arch (PS.CompositeScope bin v_merge v_split)
    , singleBundleBinds :: PFn.FnBindings sym (PBi.OtherBinary bin) v_merge 
    , singleBundleScope :: PS.SimScope sym arch (PS.CompositeScope bin v_merge v_split)
    , singleBundleDomain :: AbstractDomain sym arch (PS.CompositeScope bin v_merge v_split)
    , singleBundleBlocks :: PPa.PatchPair (PB.ConcreteBlock arch)
    } ->
       SingleBundle sym arch v_split v_merge bin


mergeBundles ::
  forall sym arch v_split v_merge.
  PS.SimScope sym arch v_split ->
  PS.SimScope sym arch v_merge ->
  Qu.QuantEach (NodeEntry' arch) ->
  PairGraph sym arch ->
  EquivM sym arch (PPa.PatchPair (SingleBundle sym arch v_split v_merge), PairGraph sym arch)
mergeBundles splitScope mergeScope snePair pg = withSym $ \sym -> withPG pg $ do
  PS.compositeScopeCases mergeScope splitScope $ \bin scope -> do
    let sne = Qu.quantEach snePair bin
    let dp = singleNodeDivergence sne
    let nd = Qu.coerceToExists dp
    let bin_other = PBi.flipRepr bin
    dpBlk <- PPa.get bin_other (graphNodeBlocks nd)
    let sneBlk = singleNodeBlock sne
    let blks = PPa.mkPair bin sneBlk dpBlk
    bundle <- lift $ noopBundle scope blks
    let sne_other = Qu.quantEach snePair bin_other 
    (st_other,binds) <- liftEqM $ \pg_ -> liftIO $ initFnBindings sym mergeScope (GraphNode sne_other) pg_
    output <- PPa.get bin_other (simOut bundle)
    PS.PopT output' <- return $ PS.fromGlobalScope $ PS.PopT (output { PS.simOutState = st_other })
    domSpec <- liftPG $ getCurrentDomainM (GraphNode $ singleToNodeEntry sne)
    dom <- IO.liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) domSpec
    return $ SingleBundle (bundle { simOut = PPa.set bin_other output' (simOut bundle) }) binds scope dom blks

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
    let sb = PS.unSE $ PS.simStackBase $ PS.simVarState vars
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
asFunctionPair (PPa.PatchPairSingle bin blk) = case PB.asFunctionEntry blk of
  Just fn -> Just (PPa.PatchPairSingle bin fn)
  Nothing -> Nothing
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
    Just fnPair ->  PPa.forBins $ \bin -> do
      vals <- PPa.get bin (PAD.absDomVals d)
      fe <- PPa.get bin fnPair
      let absSt = PAD.domainValsToAbsState vals
      return $ Const (Map.singleton (PB.functionSegAddr fe) absSt)
    Nothing -> do
      -- this is some sub-block in a function, so use the domain for
      -- the function entry point
      let fnPair = PPa.map PB.blockFunctionEntry (nodeBlocks node)  
      case getCurrentDomain gr (GraphNode node) of
        Just preSpec -> PS.viewSpec preSpec $ \_ d' -> PPa.forBins $ \bin -> do
          vals <- PPa.get bin (PAD.absDomVals d')
          fe <- PPa.get bin fnPair
          let absSt = PAD.domainValsToAbsState vals
          return $ Const (Map.singleton (PB.functionSegAddr fe) absSt)
        Nothing -> throwHere $ PEE.MissingDomainForFun fnPair


withCurrentAbsDomain ::
  HasCallStack =>
  NodeEntry arch ->
  PairGraph sym arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withCurrentAbsDomain node gr f = do
  let fnNode = functionEntryOf node
  case getCurrentDomain gr (GraphNode fnNode)  of
    Just d' -> PS.viewSpec d' $ \_ d'' -> withAbsDomain fnNode d'' gr f
    Nothing -> do
      -- this handles the case where we need to find the domain for this
      -- node but we don't have a singleton variant of the entry point
      case getDivergePoint (GraphNode node) of
        Just (GraphNode divergeNode) -> do
          Just (Some bin) <- return $ nodeToSingleRepr (GraphNode node)
          let fnNode_diverge = functionEntryOf divergeNode
          fnNode_diverge_single <- toSingleNode bin fnNode_diverge
          case getCurrentDomain gr (GraphNode fnNode_diverge) of
            Just d' | eqUptoDivergePoint (GraphNode fnNode_diverge_single) (GraphNode fnNode) ->
              PS.viewSpec d' $ \_ d'' -> do
                d_single <- PAD.singletonDomain bin d''
                withAbsDomain fnNode d_single gr f
            _ -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnNode)
        _ -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnNode)

-- | Setup a special-purpose ParsedFunctionMap with this block having a 
--   macaw abstract domain that is augmented with concrete values from
--   'AbstractDomain'
withAbsDomain ::
  HasCallStack =>
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withAbsDomain node d gr f = do
  case asFunctionPair (nodeBlocks node) of
    -- only function entry points have macaw abstract domains (which is what is being overridden here)
    -- so if we pass a non-function node entry then we just want to fetch the domain of its function
    -- entry
    Nothing -> withCurrentAbsDomain node gr f
    Just{} -> do
      PA.SomeValidArch archData <- asks envValidArch
      ovPair <- getFunctionAbs node d gr
      pfm_pair <- PPa.forBins $ \bin -> do
        binCtx <- getBinCtx' bin
        absSt <- PPa.getC bin ovPair
        let
          pfm = PMC.parsedFunctionMap binCtx
          defaultInit = PA.validArchInitAbs archData
        liftIO $ PD.addOverrides defaultInit pfm absSt
      withParsedFunctionMap pfm_pair $ do
        let fnBlks = PPa.map (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) (nodeBlocks node)
        PPa.catBins $ \bin -> do
          pfm <- PMC.parsedFunctionMap <$> getBinCtx
          fnBlks' <- PPa.get bin fnBlks
          (liftIO $ PD.parsedFunctionContaining fnBlks' pfm) >>= \case
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

instance IsTraceNode '(sym,arch) "condition_kind" where
  type TraceNodeType '(sym,arch) "condition_kind" = ConditionKind
  prettyNode () condk = PP.pretty $ conditionPrefix condk
  nodeTags = mkTags @'(sym, arch) @"condition_kind" [Simplified, Summary]

withSatConditionAssumed ::
  PS.SimScope sym arch v ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  GraphNode arch ->
  ConditionKind ->
  PairGraph sym arch ->
  EquivM_ sym arch (PairGraph sym arch) ->
  EquivM sym arch (PairGraph sym arch)
withSatConditionAssumed scope bundle dom nd condK gr0 f = withSym $ \sym -> do
  priority <- thisPriority
  eqCond <- getScopedCondition scope gr0 nd condK
  eqCond_pred <- PEC.toPred sym eqCond
  case W4.asConstantPred eqCond_pred of
    Just True -> f
    _ -> do
      (mtraceT, mtraceF) <- withTracing @"condition_kind" condK $ getTracesForPred scope bundle dom eqCond_pred
      case (mtraceT, mtraceF) of
        -- condition is not necessarily true or false
        (Just{}, Just{}) -> do
            withAssumption eqCond_pred f
        -- condition is necessarily true, so we don't need to do anything
        (Just{}, Nothing) -> f
        -- condition is not satisfiable
        (Nothing, _) -> case shouldPropagate (getPropagationKind gr0 nd condK) of
          True -> do
            gr1 <- return $ addDomainRefinement nd (PruneBranch condK) gr0
            emitTrace @"message" ("Branch dropped as " ++ conditionPrefix condK)
            return $ queueAncestors (priority PriorityPropagation) nd gr1
          -- for non-propagated assumptions we don't attempt to prune this branch,
          -- we just do nothing
          False -> do
            emitTrace @"message" ("Branch is " ++ conditionAction condK ++ " infeasible")
            return gr0

getTracesForPred ::
  PS.SimScope sym arch v ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  W4.Pred sym ->
  EquivM sym arch (Maybe (CE.TraceEvents sym arch), Maybe (CE.TraceEvents sym arch))
getTracesForPred scope bundle dom p = withSym $ \sym -> do
  not_p <- liftIO $ W4.notPred sym p
  emitTraceLabel @"expr" "Predicate" (Some p)
  mtraceT <- withTracing @"message" "With condition assumed" $
    withSatAssumption (PAS.fromPred p) $ do
      traceT <- getSomeGroundTrace scope bundle dom Nothing
      emitTrace @"trace_events" traceT
      return traceT
  mtraceF <- withTracing @"message" "With negation assumed" $
    withSatAssumption (PAS.fromPred not_p) $ do
      traceF <- getSomeGroundTrace scope bundle dom Nothing
      emitTrace @"trace_events" traceF
      return traceF
  withTracing @"message" "Simplified Predicate" $ withForkedSolver_ $ do
    p_pretty <- withTracing @"debug" "simplifier" $ PSi.applySimpStrategy PSi.prettySimplifier p
    emitTrace @"expr" (Some p_pretty)
    (trs, _) <- toConditionTraces scope bundle p_pretty mtraceT mtraceF
    emitTrace @"condition_traces" trs
  return (mtraceT, mtraceF)
  
withConditionsAssumed ::
  PS.SimScope sym arch v ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  GraphNode arch ->
  PairGraph sym arch ->
  EquivM_ sym arch (PairGraph sym arch) ->
  EquivM sym arch (PairGraph sym arch)
withConditionsAssumed scope bundle d node gr0 f = do
  foldr go f' [ConditionEquiv, ConditionAssumed, ConditionAsserted]
  where 
    f' = withSym $ \sym -> case asSingleNode node of
      Just (Some (Qu.AsSingle snode)) -> 
        lookupFnBindings scope snode gr0 >>= \case
          Just binds -> do
            bindsPred <- IO.liftIO $ PFn.toPred sym binds
            emitTraceLabel @"expr" "Bindings" (Some bindsPred)
            withAssumption bindsPred $ f
          Nothing -> f
      _ -> f

    go condK g =
      withSatConditionAssumed scope bundle d node condK gr0 g

accM :: (Monad m, Foldable t) => b -> t a -> (b -> a -> m b) -> m b
accM b ta f = foldM f b ta

processBundle ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  WorkItem arch ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  [(PPa.PatchPair (PB.BlockTarget arch))] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
processBundle scope wi node bundle d exitPairs gr0_ = withSym $ \sym -> do
  priority <- thisPriority
  (filteredPairs, gr0) <- runPG gr0_ $ filterSyncExits priority wi exitPairs

  gr1 <- checkObservables scope node bundle d gr0
  paths <- withTracing @"message" "All Instruction Paths" $ do
    paths <- bundleToInstrTraces bundle
    trees <- instrPathsToTrees paths
    emitTrace @"instruction_trees" trees
    return paths

  -- Follow all the exit pairs we found
  let initBranchState = BranchState { branchGraph = gr1, branchDesyncChoice = Nothing, branchHandled = []}
  st <- subTree @"blocktarget" "Block Exits" $ accM initBranchState (zip [0 ..] filteredPairs) $ \st0 (idx,tgt) -> do
    pg1 <- lift $ queuePendingNodes (branchGraph st0)
    let st1 = st0 { branchGraph = pg1 }
    case checkNodeRequeued gr1 st1 wi of
      True -> return st1
      False -> subTrace tgt $ followExit scope bundle paths node d st1 (idx,tgt)
  -- confirm that all handled exits cover the set of possible exits
  let allHandled = length (branchHandled st) == length filteredPairs
  let anyNonTotal = branchDesyncChoice st == Just AdmitNonTotal
  case (allHandled || anyNonTotal) of
    -- we've handled all outstanding block exits, so we should now check
    -- that the result is total
    True -> do
      -- consider any filtered out pairs as being handled
      let handled = branchHandled st ++ (exitPairs \\ filteredPairs)
      checkTotality node scope bundle d handled (branchGraph st)
    -- some block exits have been intentially skipped,
    -- since we'll be revisiting this node we can skip the totality check as well
    False -> return $ branchGraph st

withValidInit ::
  forall sym arch v a.
  HasCallStack =>
  PS.SimScope sym arch v ->
  PB.BlockPair arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withValidInit scope bPair f = withPair bPair $ do
  let
    vars = PS.scopeVars scope
    varsSt = PPa.map PS.simVarState vars

  validInit <- PVV.validInitState bPair varsSt
  validAbs <- PPa.catBins $ \bin -> do
    blk <- PPa.get bin bPair
    vars' <- PPa.get bin vars
    validAbsValues blk vars'
  withAssumptionSet (validInit <> validAbs) $ f  

withParsedFunctionMap ::
  PPa.PatchPair (PD.ParsedFunctionMap arch) ->
  EquivM_ sym arch a ->
  EquivM sym arch a  
withParsedFunctionMap pfm_pair f = do
  binCtxPair <- asks (PMC.binCtxs . envCtx)
  binCtxPair' <- PPa.update binCtxPair $ \bin -> do
    binCtx <- PPa.get bin binCtxPair
    pfm <- PPa.get bin pfm_pair
    return $ binCtx { PMC.parsedFunctionMap = pfm }
  local (\env -> env { envCtx = (envCtx env) { PMC.binCtxs = binCtxPair' }}) f

withSimBundle ::
  forall sym arch v a.
  PairGraph sym arch ->
  PPa.PatchPair (PS.SimVars sym arch v) ->
  NodeEntry arch ->
  (SimBundle sym arch v -> EquivM_ sym arch a) ->
  EquivM sym arch a
withSimBundle pg vars node f = do
  bundle0 <- mkSimBundle pg node vars
  let bundle1 = bundle0
  --bundle1 <- withTracing @"debug" "simpBundle" $ PSi.applySimpStrategy PSi.coreStrategy bundle0
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
  withPredomain scope bundle d $ 
    widenAlongEdge scope bundle (GraphNode node) d gr target

updateExtraEdges ::
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)   
updateExtraEdges scope node d gr = fnTrace "updateExtraEdges" $ do
  let extra = getExtraEdges gr node
  foldM (\gr' tgt -> handleExtraEdge scope node tgt d gr') gr (Set.toList extra)

checkParsedBlocks ::
  PB.BlockPair arch ->
  EquivM sym arch ()
checkParsedBlocks pPair = PPa.catBins $ \bin -> do
  pfm <- PMC.parsedFunctionMap <$> getBinCtx
  blk <- PPa.get bin pPair
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
  WorkItem arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
visitNode scope wi@(workItemNode -> (GraphNode node@(nodeBlocks -> bPair))) d gr0 = 
  withAbsDomain node d gr0 $ do
    checkParsedBlocks bPair
    withValidInit scope bPair $ do
      d' <- applyCurrentAsms d
      emitTraceLabel @"domain" PAD.Predomain (Some d')
      gr2 <- updateExtraEdges scope node d gr0
      let vars = PS.scopeVars scope
      withSimBundle gr2 vars node $ \bundle -> 
        withPredomain scope bundle d $ do
          runPendingActions nodeActions (GraphNode node) (TupleF3 scope bundle d) gr2 >>= \case
            Just gr3 -> do
              priority <- thisPriority
              return $ queueNode (priority PriorityHandleActions) (GraphNode node) gr3
            Nothing -> withConditionsAssumed scope bundle d (GraphNode node) gr0 $ do
              exitPairs <- PD.discoverPairs bundle    
              processBundle scope wi node bundle d exitPairs gr2

visitNode scope (workItemNode -> (ReturnNode fPair)) d gr0 =  do
  -- propagate the abstract domain of the return node to
  -- all of the known call sites of this function.
  let rets = getReturnVectors gr0 fPair

  case null rets of
    False -> subTree @"entrynode" "Block Returns" $
      foldM (\gr node -> subTrace node $ processReturn gr node) gr0 (getReturnVectors gr0 fPair)
    True -> processFinalReturn gr0
 where
  -- cleanup for a return node that returns nowhere (likely a toplevel return)
  processFinalReturn gr0' = do
    bundle <- noopBundle scope (graphNodeBlocks (ReturnNode fPair))
    emitTraceLabel @"domain" PAD.ExternalPostDomain (Some d)
    withPredomain scope bundle d $ do
      runPendingActions nodeActions (ReturnNode fPair) (TupleF3 scope bundle d) gr0' >>= \case
        Just gr1 -> do
          priority <- thisPriority
          return $ queueNode (priority PriorityHandleActions) (ReturnNode fPair) gr1      
        Nothing -> withTracing @"message" "Toplevel Return" $ do
          withConditionsAssumed scope bundle d (ReturnNode fPair) gr0' $ do
            case isSingleReturn fPair of
              Just{} -> handleOrphanedSingleSidedReturn scope fPair gr0'
              Nothing -> return gr0'

   -- Here, we're using a bit of a trick to propagate abstract domain information to call sites.
   -- We are making up a "dummy" simulation bundle that basically just represents a no-op, and
   -- using the ordinary widening machinery.


  processReturn gr0' node@(nodeBlocks -> ret) = do
    priority <- thisPriority
    let
      vars = PS.scopeVars scope
      varsSt = PPa.map PS.simVarState vars
    validState <- PVV.validInitState ret varsSt
    withCurrentAbsDomain (functionEntryOf node) gr0' $ withAssumptionSet validState $ do
      (asm, bundle) <- returnSiteBundle scope vars d ret
      withAssumptionSet asm $ withPredomain scope bundle d $ do
        runPendingActions nodeActions (ReturnNode fPair) (TupleF3 scope bundle d) gr0' >>= \case
          Just gr1 -> do
            return $ queueNode (priority PriorityHandleActions) (ReturnNode fPair) gr1
          Nothing -> withConditionsAssumed scope bundle d (ReturnNode fPair) gr0 $ do
            traceBundle bundle "Processing return edge"
            -- observable events may occur in return nodes specifically
            -- when they are a synchronization point, since the abstract
            -- domain may now contain traces of deferred observable events for both programs
            --
            -- TODO: formally we could just check the event sequence once for the return node
            -- (rather than once for each return edge)
            -- but it would require some refactoring to make the types match up correctly
            withPG_ gr0' $ do
              liftEqM_ $ checkObservables scope node bundle d
              liftEqM_ $ \pg -> widenAlongEdge scope bundle (ReturnNode fPair) d pg (GraphNode node)
              liftPG $ handleSingleSidedReturnTo priority node

-- | Used to handle the case where a single-sided analysis
--   has continued up to the top-level return.
--   In most cases, this represents a control flow path that
--   is only present in the patched program, and so we
--   simply add as an equivalence condition that this
--   single-sided return isn't taken.
--   We emit a warning as well, however, since this is also potentially
--   a result of some issue with the analysis (e.g. forgetting to
--   provide one of the synchronization points)
handleOrphanedSingleSidedReturn ::
  PS.SimScope sym arch v ->
  NodeReturn arch ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleOrphanedSingleSidedReturn scope nd pg = withSym $ \sym -> do
  priority <- thisPriority
  emitWarning $ PEE.OrphanedSinglesidedAnalysis (nodeFuns nd)
  pg1 <- addToEquivCondition scope (ReturnNode nd) ConditionEquiv (W4.falsePred sym) pg
  return $ queueAncestors (priority PriorityPropagation) (ReturnNode nd) pg1

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
  PS.SimScope sym arch v ->
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  AbstractDomain sym arch v ->
  PB.BlockPair arch {- ^ block pair being returned to -} ->
  EquivM sym arch (PAS.AssumptionSet sym, SimBundle sym arch v)
returnSiteBundle scope vars _preD pPair = withSym $ \sym -> do
  simIn_ <- PPa.forBins $ \bin -> do
    blk <- PPa.get bin pPair
    absSt <- PD.getAbsDomain blk
    vars' <- PPa.get bin vars
    return $ PS.SimInput (PS.simVarState vars') blk absSt
  blockEndVal <- liftIO (MCS.initBlockEnd (Proxy @arch) sym MCS.MacawBlockEndReturn)

  simOut_ <- PPa.forBins $ \bin -> do
    input <- PPa.get bin simIn_
    let inSt = PS.simInState input
    let postSt_ = inSt { PS.simStackBase = PS.simCallerStackBase inSt }
    postFrame <- liftIO $ PS.nextStackBase sym bin postSt_
    let postSt = postSt_ { PS.simCallerStackBase = postFrame }

    return $ PS.SimOutput postSt blockEndVal

  bundle <- applyCurrentAsms $ SimBundle simIn_ simOut_

  -- assert that, upon return, the frame of the callee is the same as its
  -- stack pointer (i.e. interpret the domain as if all of its values were
  -- computed as offsets starting from the call site)
  asms <- PPa.catBins $ \bin -> do
    input <- PPa.get bin simIn_
    let
      inSt = PS.simInState input
      initFrame = PS.simStackBase inSt
      CLM.LLVMPointer _ sp_pre = PSR.macawRegValue $ PS.simSP inSt
    outVars <- PPa.get bin $ (PPa.fromTuple $ PS.bundleOutVars scope bundle)
    blk <- PPa.get bin pPair
    vAbs <- validAbsValues blk outVars
    return $ vAbs <> (PAS.exprBinding (PS.unSE $ initFrame) sp_pre)

  return (asms, bundle)


-- | Strengthen the stack domain by implicitly assuming that out-of-scope
-- slots (i.e. past the current stack pointer) are equivalent.
-- Notably the stack slots must be past *both* the original and patched
-- stack pointers to be assumed equivalent.
strengthenStackDomain ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (AbstractDomain sym arch v)
strengthenStackDomain scope dom = withSym $ \sym -> do
  let stackDom = PEq.eqDomainStackMemory $ PAD.absDomEq dom
  stackDom' <- PEm.traverseWithCell stackDom $ \cell p ->  do
    stack_scope <- PPa.joinPatchPred (\x y -> liftIO $ W4.andPred sym x y ) $ \bin -> do
      regs <- (PS.simRegs . PS.simVarState) <$> PPa.get bin (PS.scopeVars scope)
      let sp = regs ^. MM.boundValue (MM.sp_reg @(MM.ArchReg arch))
      let CLM.LLVMPointer _ cell_off = PMc.cellPtr cell
      let CLM.LLVMPointer _ sp_off = PSR.macawRegValue sp
      liftIO $ PMc.viewCell cell $ W4.bvSge sym cell_off sp_off
    liftIO $ W4.andPred sym p stack_scope

  return $ dom { PAD.absDomEq = (PAD.absDomEq dom) 
    { PEq.eqDomainStackMemory = stackDom' } }

-- | Run the given function a context where the
-- given abstract domain is assumed to hold on the pre-state of the given
-- bundle.
withPredomain ::
  forall sym arch v a.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch a ->
  EquivM sym arch a
withPredomain scope bundle preD f = withSym $ \sym -> do
  eqCtx <- equivalenceContext
  precond <- liftIO $ PAD.absDomainToPrecond sym scope eqCtx bundle preD
  withAssumptionSet precond $ f


checkObservables :: forall sym arch v.
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkObservables scope bPair bundle preD gr0 =
  considerObservableEvent gr0 bPair $
    do (mres, gr) <- doCheckObservables scope bPair bundle preD gr0
       case mres of
         Nothing -> return (Nothing, gr)
         Just res -> withTracing @"observable_result" res $ case res of
          CE.ObservableCheckEq -> do
            traceBundle bundle "Observables agree"
            return (Nothing, gr)
          CE.ObservableCheckError msg -> do
            let msg' = ("Error checking observables: " ++ msg)
            err <- emitError' (PEE.ObservabilityError msg')
            return (Nothing, recordMiscAnalysisError gr (GraphNode bPair) err)
          CE.ObservableCheckCounterexample cex@(ObservableCounterexample _ oSeq pSeq) -> do
            traceBundle bundle ("Obserables disagree!")
            traceBundle bundle ("== Original sequence ==")
            traceBundle bundle (show (vcat (map MT.prettyMemEvent oSeq)))
            traceBundle bundle ("== Patched sequence ==")
            traceBundle bundle (show (vcat (map MT.prettyMemEvent pSeq)))
            emitWarning $ PEE.ObservableDifferenceFound
            return (Just cex, gr)

instance (forall tp. PEM.ExprMappable sym (f tp)) => 
  PEM.ExprMappable sym (MM.RegState r f) where
  mapExpr sym f r = MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) r

doCheckObservables :: forall sym arch v.
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (CE.ObservableCheckResult sym arch), PairGraph sym arch)
doCheckObservables scope ne bundle preD pg = case PS.simOut bundle of
  -- for singleton cases, we consider all events to be trivially
  -- observably equivalent, as we are collecting observable events
  -- for future analysis in the domain
  PPa.PatchPairSingle _ _ -> return (Just CE.ObservableCheckEq, pg)
  PPa.PatchPair outO outP -> withSym $ \sym -> do

       oSeq <- getObservableEvents outO
       pSeq <- getObservableEvents outP

       -- append any accumulated events (deferred from previous single-stepping analysis)
       PPa.PatchPair (PAD.EventSequence eventsO) (PAD.EventSequence eventsP) <- 
        return $ (PAD.absDomEvents preD)
       oSeq' <- IO.liftIO $ appendSymSequence sym oSeq eventsO
       pSeq' <- IO.liftIO $ appendSymSequence sym pSeq eventsP

       eqSeq <- equivalentSequences oSeq' pSeq'

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
       
       priority <- thisPriority
       not_goal <- liftIO $ W4.notPred sym eqSeq
       mres <- withSatAssumption (PAS.fromPred not_goal) $ withTracing @"message" "Observable difference found" $  do
        goalSat "checkObservableSequences" (W4.truePred sym) $ \res -> case res of
          Unsat _ -> throwHere PEE.InconclusiveSAT -- should be impossible
          Unknown -> return (CE.ObservableCheckError "UNKNOWN result when checking observable sequences")
          Sat evalFn' -> do
            withSym $ \sym -> do
              regsO <- MM.traverseRegsWith (\_ -> PEM.mapExpr sym (\x -> concretizeWithModel evalFn' x)) (PS.simOutRegs outO)
              regsP <- MM.traverseRegsWith (\_ -> PEM.mapExpr sym (\x -> concretizeWithModel evalFn' x)) (PS.simOutRegs outP)
              evs <- getTraceFromModel scope evalFn' bundle preD Nothing
              emitTrace @"trace_events" evs
              withGroundEvalFn evalFn' $ \evalFn -> do
                -- NB, observable sequences are stored in reverse order, so we reverse them here to
                -- display the counterexample in a more natural program order
                oSeq'' <- reverse <$> CE.groundObservableSequence sym evalFn oSeq' -- (MT.memSeq oMem)
                pSeq'' <- reverse <$> CE.groundObservableSequence sym evalFn pSeq' -- (MT.memSeq pMem)

                let regsCE = RegsCounterExample regsO regsP

                return (CE.ObservableCheckCounterexample (ObservableCounterexample regsCE oSeq'' pSeq''))
       case mres of
          Nothing -> return (Just CE.ObservableCheckEq, pg)
          Just cex -> do
            heuristicTimeout <- asks (PCfg.cfgHeuristicTimeout . envConfig)
            issat <- isPredSat' heuristicTimeout eqSeq >>= \case
              Just False -> return False
              _ -> return True

            mcondK <- case issat of
              True -> do
                let msg = "Handle observable difference:"
                choose @"()" msg $ \choice -> do
                  -- first (default) action is to keep the observable report but don't change
                  -- anything about the analysis
                  choice "Emit warning and continue" () $ return Nothing
                  -- NB: the only difference between the two assertion types is the priority that the propagation step occurs at
                  -- the verifier will finish any widening steps it has before processing any deferred propagation steps
                  choice "Assert difference is infeasible (defer proof)" () $ return $ Just (ConditionAsserted, RefineUsingExactEquality, PriorityDeferredPropagation)
                  choice "Assert difference is infeasible (prove immediately)" () $ return $ Just (ConditionAsserted, RefineUsingExactEquality, PriorityPropagation)
                  choice "Assume difference is infeasible" () $ return $ Just (ConditionAssumed, RefineUsingExactEquality, PriorityDeferredPropagation)
                  choice "Avoid difference with equivalence condition" () $ return $ Just (ConditionEquiv, RefineUsingExactEquality, PriorityPropagation)
                  choice "Avoid difference with path-sensitive equivalence condition" () $ return $ Just (ConditionEquiv, RefineUsingIntraBlockPaths, PriorityPropagation)
              False -> return Nothing

            case mcondK of
              Just (condK, refineK, p) ->  do
                let do_propagate = case p of
                      PriorityPropagation -> True
                      _ -> shouldPropagate (getPropagationKind pg nd condK)

                simplifier <- PSi.mkSimplifier PSi.deepPredicateSimplifier
                eqSeq_simp <- case refineK of
                  RefineUsingExactEquality -> PSi.applySimplifier simplifier eqSeq
                  RefineUsingIntraBlockPaths -> do
                    eqSeq_paths <- strengthenPredicate [Some eqSeq] eqSeq
                    PSi.applySimplifier simplifier eqSeq_paths

                withPG pg $ do
                  liftEqM_ $ addToEquivCondition scope nd condK eqSeq_simp
                  liftPG $ do
                    when do_propagate $ do
                      modify $ queueAncestors (priority p) nd
                      when ((condK, p) == (ConditionEquiv, PriorityPropagation)) $
                        modify $ setPropagationKind nd ConditionEquiv PropagateOnce
                    modify $ dropPostDomains nd (priority PriorityDomainRefresh)
                    modify $ queueNode (raisePriority (priority PriorityNodeRecheck)) nd
                  return Nothing
              Nothing -> return $ (Just cex, pg)
  where
    nd = GraphNode ne

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

  eqEvent (MT.ExternalCallEventGen nmx x obsx) (MT.ExternalCallEventGen nmy y obsy)
    | nmx == nmy
    , obsx == obsy
    = IO.liftIO $  do
      ps <- mapM (\(x_,y_) -> ET.compareExternalCallData sym x_ y_) (zip x y)
      foldM (W4.andPred sym) (W4.truePred sym) ps

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
  type TraceNodeType '(sym,arch) "totality" = TotalityResult sym arch
  prettyNode () r = case r of
    CasesTotal -> "Cases total"
    TotalityCheckingError msg -> "Error:" <+> PP.pretty msg
    TotalityCheckCounterexample ocex (TotalityCounterexample (oIP,oEnd,oInstr) (pIP,pEnd,pInstr)) -> PP.vsep $
      ["Found extra exit while checking totality:"
      , PP.pretty (showHex oIP "") <+> PP.pretty (MCS.ppExitCase oEnd) <+> PP.pretty (show oInstr)
      , PP.pretty (showHex pIP "") <+> PP.pretty (MCS.ppExitCase pEnd) <+> PP.pretty (show pInstr)
      , ""
      , PP.pretty ocex
      ]
  nodeTags = [(Summary, \_ r -> case r of
                   CasesTotal -> "Total"
                   TotalityCheckingError{} -> "Error"
                   TotalityCheckCounterexample{} -> "Not total")
             ]
   

checkTotality :: forall sym arch v.
  NodeEntry arch ->
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
checkTotality bPair scope bundle preD exits gr =
  considerDesyncEvent gr bPair $
    do tot <- doCheckTotality scope bundle preD exits
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
         TotalityCheckCounterexample _ cex@(TotalityCounterexample (oIP,oEnd,oInstr) (pIP,pEnd,pInstr)) ->
           do traceBundle bundle $ unlines
                ["Found extra exit while checking totality:"
                , showHex oIP "" ++ " " ++ MCS.ppExitCase oEnd ++ " " ++ show oInstr
                , showHex pIP "" ++ " " ++ MCS.ppExitCase pEnd ++ " " ++ show pInstr
                ]
              
              return (Just cex, gr)

data TotalityResult sym arch
  = CasesTotal
  | TotalityCheckingError String
  | TotalityCheckCounterexample (CE.TraceEvents sym arch) (TotalityCounterexample (MM.ArchAddrWidth arch))

{-
-- TODO: use solver to resolve classifier errors by comparing
-- the two binaries
-- | Similar to 'resolveClassifierErrors' but uses 
resolveClassifierErrors2 ::
  forall bin sym arch v.
  PPa.PatchPair (PS.SimInput sym arch v) ->
  PS.SimOutput sym arch v bin ->
  EquivM sym arch (ExtraJumps arch)  
-}

resolveClassifierErrors ::
  forall bin sym arch v.
  PBi.KnownBinary bin =>
  PS.SimInput sym arch v bin ->
  PS.SimOutput sym arch v bin ->
  EquivM sym arch (ExtraJumps arch)
resolveClassifierErrors simIn_ simOut_ = withSym $ \sym -> do
  let (bin :: PBi.WhichBinaryRepr bin) = knownRepr
  let bundle' = PS.SimBundle (PPa.mkSingle bin simIn_) (PPa.mkSingle bin simOut_)
  ctx <- getBinCtx' bin
  let mem_image = MBL.memoryImage $ PMC.binary ctx
  let regs  = PS.simRegs (PS.simOutState simOut_)
  let iPReg = regs ^. MM.curIP
  let mem = PS.simMem (PS.simOutState simOut_)
  let stackBase = PS.unSE $ PS.simStackBase (PS.simInState simIn_)
  let CLM.LLVMPointer _ stackOut = PSR.macawRegValue $ PS.simSP (PS.simOutState simOut_)

  CLM.LLVMPointer retR retV <- IO.liftIO $ PA.archSymReturnAddress sym (PS.simInState simIn_)
  goalTimeout <- asks (PCfg.cfgGoalTimeout . envConfig)

  -- | is it possible to end in a classification failure? If so, find all of the concrete edges that
  --   resulted in failure
  let
    maybeZero :: EquivM_ sym arch Bool
    maybeZero = do
      let ip_sym = PSR.macawRegValue iPReg
      nullptr <- liftIO $ CLM.mkNullPointer sym W4.knownRepr 
      isnull <- liftIO $ MT.llvmPtrEq sym nullptr ip_sym
      goalSat "maybeZero" isnull $ \res -> case res of
        Sat{} -> return True
        _ -> return False

    findTargets :: Set.Set (MM.ArchSegmentOff arch) -> EquivM_ sym arch (Set.Set (MM.ArchSegmentOff arch))
    findTargets previous_results = do
      mresult <- goalSat "resolveClassifierErrors: findTargets" (W4.truePred sym) $ \res -> case res of
        Unsat _ -> return Nothing
        Unknown -> return Nothing
        Sat evalFn' -> do
          mgroundip <- withGroundEvalFn evalFn' $ \evalFn -> 
            groundIPValue sym evalFn iPReg
          case mgroundip of
            Just iPV -> do
              let ip_raw = MM.memWord (fromIntegral iPV)
              case PM.resolveAbsoluteAddress mem_image ip_raw of
                Nothing -> do
                  emitWarning $ PEE.FailedToResolveAddress ip_raw
                  return Nothing
                Just ip_conc -> return $ Just ip_conc
            _ -> return Nothing
      case mresult of
        Nothing -> return previous_results
        Just result -> do
          let ip_sym = PSR.macawRegValue iPReg
          ip_conc <- PD.concreteAddrToLLVM (PAd.segOffToAddr result)
          let eqIPs = PAS.ptrBinding ip_sym ip_conc
          this_ip <- PAS.toPred sym eqIPs
          not_this <- PAS.fromPred <$> (liftIO $ W4.notPred sym this_ip)
          let next_results = Set.insert result previous_results
          fromMaybe next_results <$> (withSatAssumption not_this $ findTargets next_results)

    findOne :: ExtraJumps arch -> EquivM_ sym arch (ExtraJumps arch)
    findOne tried = do
      result <- goalSat "resolveClassifierErrors" (W4.truePred sym) $ \res -> case res of
        Unsat _ -> return Nothing
        Unknown -> return Nothing
        Sat evalFn' -> withGroundEvalFn evalFn' $ \evalFn ->
          fmap fst <$> CE.groundMuxTree sym evalFn (MT.memCurrentInstr mem)
      case result of
        Just instr_addr -> do
          instr_sym <- PD.thisInstr (PS.simOutState simOut_)
          instr_conc <- justPartExpr sym <$> PD.concreteAddrToLLVM (PAd.segOffToAddr instr_addr)
          eqInstr <- liftIO $ PD.liftPartialRel sym (\p1 p2 -> return $ PAS.ptrBinding p1 p2) instr_sym instr_conc
          is_this_instr <- PAS.toPred sym eqInstr
          with_targets <- withAssumption is_this_instr $ do
            maybeZero >>= \case
              True -> asks (PCfg.cfgAlwaysClassifyReturn . envConfig) >>= \case
                True -> return $ Map.insert instr_addr ReturnTarget tried
                False -> chooseBool ("Classifier Failure: Mark " ++ show instr_addr ++ " as return?") >>= \case
                  True -> return $ Map.insert instr_addr ReturnTarget tried
                  False -> return tried
              False -> do
                targets <- findTargets Set.empty
                retV_conc <- concretizeWithSolver retV
                retR_conc <- concretizeWithSolver (W4.natToIntegerPure retR)
                mret <- case (W4.asConcrete retV_conc, W4.asConcrete retR_conc) of
                  (Just (W4.ConcreteBV _ rvc), Just (W4.ConcreteInteger 0))
                    | ret_raw <- MM.memWord (fromIntegral (BV.asUnsigned rvc))
                    -> return $ PM.resolveAbsoluteAddress mem_image ret_raw
                  _ -> return Nothing

                stack_bottom_pred <- IO.liftIO $ W4.isEq sym stackOut stackBase
                stack_bottom <- isPredTrue' goalTimeout stack_bottom_pred
                extra_jump <- case Set.toList targets of
                  [target_addr] -> return $ DirectCall target_addr mret stack_bottom
                  _ -> return $ DirectTargets targets
                return $ Map.insertWith (<>) instr_addr extra_jump tried
          not_this_instr <-  PAS.fromPred <$> (liftIO $ W4.notPred sym is_this_instr)
          fromMaybe with_targets <$> (withSatAssumption not_this_instr $ findOne with_targets)
        Nothing -> return $ tried
  isFailure <- PAS.fromPred <$> PD.matchingExits bundle' MCS.MacawBlockEndFail
  fromMaybe Map.empty <$> (withSatAssumption isFailure $ findOne Map.empty)

doCheckTotality :: forall sym arch v.
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v -> 
  [PPa.PatchPair (PB.BlockTarget arch)] ->
  EquivM sym arch (TotalityResult sym arch)
doCheckTotality scope bundle preD exits =
  withSym $ \sym ->
    do
       -- compute the condition that leads to each of the computed
       -- exit pairs
       cases <- forM exits (\blkts -> PD.matchesBlockTarget bundle blkts >>= PAS.toPred sym)

       -- TODO, I really don't understand this abort case stuff, but it was copied
       -- from the triple verifier.
       isReturn <- do
         bothReturn <- PD.matchingExits bundle MCS.MacawBlockEndReturn
         {-
         -- FIXME: add this back in when we are handling non-trivial abort cases
         outO <- PPa.get PBi.OriginalRepr (simOut bundle)
         abortO <- PAb.isAbortedStatePred outO
         returnP <- liftIO $ MCS.isBlockEndCase (Proxy @arch) sym (PS.simOutBlockEnd $ PS.simOutP bundle) MCS.MacawBlockEndReturn
         abortCase <- liftIO $ W4.andPred sym abortO returnP
         liftIO $ W4.orPred sym bothReturn abortCase
         -}
         return bothReturn

       asm <- liftIO $ (forM (isReturn:cases) (W4.notPred sym) >>= (foldM (W4.andPred sym) (W4.truePred sym)))

       goalSat "doCheckTotality" asm $ \res -> case res of
         Unsat _ -> return CasesTotal
         Unknown -> return (TotalityCheckingError "UNKNOWN result when checking totality")
         Sat evalFn' -> do
           ocex <- getTraceFromModel scope evalFn' bundle preD Nothing
           withGroundEvalFn evalFn' $ \evalFn -> do
           -- We found an execution that does not correspond to one of the
           -- executions listed above, so compute the counterexample.
           --
           -- TODO: if the location being jumped to is unconstrained (e.g., a return where we don't have
           -- information about the calling context) the solver will invent nonsense addresses for
           -- the location.  It might be better to only report concrete values for exit address
           -- if it is unique.
              result <- PPa.runPatchPairT $ PPa.forBinsC $ \bin -> do
                out <- PPa.get bin (PS.simOut bundle)
                let regs  = PS.simRegs (PS.simOutState out)
                let iPReg = regs ^. MM.curIP
                let blockEnd = PS.simOutBlockEnd out
                let mem = PS.simMem (PS.simOutState out)
                blockEndCase <- lift $ groundBlockEndCase sym (Proxy @arch) evalFn blockEnd
                iPV <- lift $ groundIPValue sym evalFn iPReg
                instr <- lift $ CE.groundMuxTree sym evalFn (MT.memCurrentInstr mem)
                case iPV of
                  Just val -> return $ (Just (val, blockEndCase, instr))
                  Nothing -> return $ Nothing
              
              case result of
                PPa.PatchPairC (Just ores) (Just pres) ->
                  return (TotalityCheckCounterexample ocex
                    (TotalityCounterexample ores pres))
                PPa.PatchPairSingle _ (Const (Just r)) ->
                  --FIXME: update the type to use PatchPairC
                  return (TotalityCheckCounterexample ocex
                    (TotalityCounterexample r r))
                _ -> return (TotalityCheckingError ("IP register had unexpected type"))

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
     CE.groundMuxTree sym evalFn mt


data BranchState sym arch =
  BranchState 
    { branchGraph :: PairGraph sym arch
    , branchDesyncChoice :: Maybe DesyncChoice
    , branchHandled :: [PPa.PatchPair (PB.BlockTarget arch)]
    }

updateBranchGraph :: BranchState sym arch -> PPa.PatchPair (PB.BlockTarget arch) -> PairGraph sym arch -> BranchState sym arch
updateBranchGraph st blkt pg = st {branchGraph = pg, branchHandled = blkt : branchHandled st }

checkNodeRequeued ::
  PairGraph sym arch ->
  BranchState sym arch ->
  WorkItem arch ->
  Bool
checkNodeRequeued stPre stPost wi = fromMaybe False $ do
  bc <- branchDesyncChoice stPost
  return $ choiceRequiresRequeue bc
  <|> do
    Nothing <- return $ getQueuedPriority wi stPre
    _ <- getQueuedPriority wi (branchGraph stPost)
    return True

followExit ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  InstructionPaths sym arch {- ^ all possible instruction paths (only used for logging) -} ->
  NodeEntry arch {- ^ current entry point -} ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  BranchState sym arch ->
  (Integer, PPa.PatchPair (PB.BlockTarget arch)) {- ^ next entry point -} ->
  EquivM sym arch (BranchState sym arch)
followExit scope bundle paths currBlock d st (idx, pPair) = do
  let gr = branchGraph st
  traceBundle bundle ("Handling proof case " ++ show idx)
  res <- manifestError $ triageBlockTarget scope bundle paths currBlock st d pPair
  case res of
    Left err -> do
      emitEvent $ PE.ErrorEmitted err
      return $ st {branchGraph = recordMiscAnalysisError gr (GraphNode currBlock) err }
    Right gr' -> return gr'


skippedFnSym :: PB.FunctionSymbol
skippedFnSym = PB.mkFunctionSymbol $ BSC.pack "__pate_skipped"

getFunctionStub ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Maybe PB.FunctionSymbol)
getFunctionStub blk = do
  PA.SomeValidArch archData <- asks envValidArch
  PD.findPLTSymbol blk >>= \case
    Just nm -> return $ Just $ PB.mkFunctionSymbol nm
    Nothing | Just fnEntry <- PB.asFunctionEntry blk -> do
      let mnm = PB.functionSymbol fnEntry
      case mnm of
        Just nm | Just{} <- PA.lookupStubOverride archData nm -> return $ Just nm
        Just nm | PD.isAbortStub nm -> return $ Just nm
        Just nm | PB.functionIgnored fnEntry -> return $ Just nm
        Nothing | PB.functionIgnored fnEntry -> return $ Just skippedFnSym
        Nothing -> asks (PCfg.cfgIgnoreUnnamedFunctions . envConfig) >>= \case
          True -> return $ Just skippedFnSym
          False -> return Nothing
        _ -> return Nothing
    Nothing -> return Nothing

type StubPair = PPa.PatchPairC (Maybe PB.FunctionSymbol)

-- | Return the name of a function if we want to replace its call with
--   stub semantics
getFunctionStubPair ::
  PPa.PatchPair (PB.BlockTarget arch) ->
  EquivM sym arch StubPair
getFunctionStubPair blkts = PPa.forBins $ \bin -> do
  blkt <- PPa.get bin blkts
  case blkt of 
    PB.BlockTarget{} -> Const <$> getFunctionStub (PB.targetCall blkt)
    PB.BlockTargetReturn{} -> return $ Const Nothing

hasStub :: StubPair -> Bool
hasStub stubPair = getAny $ PPa.collapse (Any . isJust . getConst) stubPair

-- | True if either stub has an abort symbol
hasTerminalStub :: StubPair -> Bool
hasTerminalStub stubPair = getAny $ PPa.collapse (Any . fromMaybe False . fmap PD.isAbortStub . getConst) stubPair
 
bothTerminalStub :: StubPair -> Bool
bothTerminalStub stubPair = getAll $ PPa.collapse (All . fromMaybe False . fmap PD.isAbortStub . getConst) stubPair

isIgnoredBlock :: PB.ConcreteBlock arch bin -> Bool
isIgnoredBlock blk = case PB.asFunctionEntry blk of
  Just fnEntry -> PB.functionIgnored fnEntry
  Nothing -> False

{-
isIgnoredBlockPair :: PPa.PatchPair (PB.ConcreteBlock arch) -> Bool
isIgnoredBlockPair blks = isIgnoredBlock (PPa.pOriginal blks) (PPa.pPatched blks)
-}





combineCases :: MCS.MacawBlockEndCase -> MCS.MacawBlockEndCase -> Maybe MCS.MacawBlockEndCase
combineCases c1 c2 = case (c1,c2) of
  (MCS.MacawBlockEndBranch, MCS.MacawBlockEndJump) -> Just MCS.MacawBlockEndJump
  (MCS.MacawBlockEndJump, MCS.MacawBlockEndBranch) -> Just MCS.MacawBlockEndJump
  _ | c1 == c2 -> Just c1
  _ -> Nothing

-- | Regardless of what is in the 'BlockTarget', we consider the return point of
--   a terminal/abort stub to always be 'Nothing', so we don't consider the code
--   at its (non-reachable) return point.
--   This is handled here (rather than when the 'BlockTarget' is created) so that
--   all of the branch/path matching is still consistent.
getTargetReturn :: PBi.KnownBinary bin => PB.BlockTarget arch bin -> EquivM sym arch (Maybe (PB.ConcreteBlock arch bin))
getTargetReturn PB.BlockTargetReturn{} = return Nothing
getTargetReturn blkt = getFunctionStub (PB.targetCall blkt) >>= \case
  Just stub | PD.isAbortStub stub -> return Nothing
  _ -> return $ PB.targetReturn blkt

data InstructionTrees arch = InstructionTrees (PPa.PatchPairC (SymSequenceTree (ET.InstructionEvent arch)))
type InstructionPaths sym arch = PPa.PatchPairC (SymSequence sym (ET.InstructionEvent arch))

ppSet :: PP.Pretty e => Set.Set e -> PP.Doc a
ppSet s | [e] <- Set.toList s = PP.pretty e
ppSet s =
  "{" <> PP.hsep (PP.punctuate "," (map PP.pretty (Set.toList s))) <> "}"

ppTreesSummary :: PA.ValidArch arch => InstructionTrees arch -> PP.Doc a
ppTreesSummary (InstructionTrees trs) = 
  PPa.ppPatchPair' (\(Const s) -> 
    let hds = Set.fromList $ (map ET.instrAddr $ seqTreeHeads s)
        lasts = Set.fromList $ (map ET.instrAddr $ seqTreeLasts s)
    in 
      "[" <> ppSet hds <> ".." <> ppSet lasts <> "]" 
    ) trs 

instrPathsToTrees ::
  InstructionPaths sym arch ->
  EquivM sym arch (InstructionTrees arch)
instrPathsToTrees pathsPair = withSym $ \sym -> fmap InstructionTrees $ PPa.forBinsC $ \bin -> do
  paths <- PPa.getC bin pathsPair
  goalTimeout <- asks (PCfg.cfgGoalTimeout . envConfig)
  paths' <- feasiblePaths sym (withAssumption) (concretePred goalTimeout) paths
  return $ toSequenceTree paths'

instance (PSo.ValidSym sym, PA.ValidArch arch) => IsTraceNode '(sym,arch) "instruction_trees" where
  type TraceNodeType '(sym,arch) "instruction_trees" = InstructionTrees arch
  prettyNode () (InstructionTrees ps) =
    let ppEvs es = PP.vsep $ map (PP.pretty . ET.instrAddr) es 
    in PPa.ppPatchPair' (\(Const s) -> ppSeqTree ppEvs s) ps 
  nodeTags = 
    [ (Summary, \_ v -> ppTreesSummary v)
    , (Simplified, \_ v -> ppTreesSummary v)
    ]
  jsonNode sym () (InstructionTrees ps) = do
    v <- W4S.w4ToJSON sym ps
    nodeToJSON' @'(sym,arch) @"instruction_trees" JSON.Null v

-- | Figure out what kind of control-flow transition we are doing
--   here, and call into the relevant handlers.
triageBlockTarget ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  InstructionPaths sym arch {- ^ all possible instruction paths (only used for logging) -} ->
  NodeEntry arch {- ^ current entry point -} ->
  BranchState sym arch ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PPa.PatchPair (PB.BlockTarget arch) {- ^ next entry point -} ->
  EquivM sym arch (BranchState sym arch)
triageBlockTarget scope bundle' paths currBlock st d blkts = withSym $ \sym -> do
  let gr = branchGraph st
  priority <- thisPriority
  stubPair <- fnTrace "getFunctionStubPair" $ getFunctionStubPair blkts
  matches <- PD.matchesBlockTarget bundle' blkts
  res <- withPathCondition matches $ do
    withTracing @"message" "Instruction Paths to Exit" $ do
      trees <- instrPathsToTrees paths
      emitTrace @"instruction_trees" trees
    let (ecase1, ecase2) = PPa.view PB.targetEndCase blkts
    mrets <- PPa.toMaybeCases <$> 
      PPa.forBinsF (\bin -> PPa.get bin blkts >>= getTargetReturn) 
    case (combineCases ecase1 ecase2,mrets) of
      (Nothing,_) -> handleDivergingPaths scope bundle' currBlock st d blkts
      (_,PPa.PatchPairMismatch{}) -> handleDivergingPaths scope bundle' currBlock st d blkts
      _ | isMismatchedStubs stubPair -> handleDivergingPaths scope bundle' currBlock st d blkts
      (Just ecase, PPa.PatchPairJust rets) -> fmap (updateBranchGraph st blkts) $ do
        let pPair = PPa.map PB.targetCall blkts
        bundle <- PD.associateFrames bundle' ecase (hasStub stubPair)
        getSomeGroundTrace scope bundle d Nothing >>= emitTrace @"trace_events"
        traceBundle bundle ("  Return target " ++ show rets)
        ctx <- view PME.envCtxL
        let isEquatedCallSite = any (PB.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)

        if | isEquatedCallSite -> handleInlineCallee scope bundle currBlock d gr pPair rets
           | hasStub stubPair -> withPG_ gr $ do
              liftEqM_ $ \gr_ -> handleStub scope bundle currBlock d gr_ pPair (Just rets) stubPair
              liftPG $ addReturnPointSync priority currBlock blkts
           | otherwise -> handleOrdinaryFunCall scope bundle currBlock d gr pPair rets

      (Just ecase, PPa.PatchPairNothing) -> fmap (updateBranchGraph st blkts) $ do
        bundle <- PD.associateFrames bundle' ecase (hasStub stubPair)
        getSomeGroundTrace scope bundle d Nothing >>= emitTrace @"trace_events"
        case ecase of
          MCS.MacawBlockEndReturn -> handleReturn scope bundle currBlock d gr
          _ -> do
            let
              pPair = PPa.map PB.targetCall blkts
              nextNode = mkNodeEntry currBlock pPair
            traceBundle bundle "No return target identified"
            emitTrace @"message" "No return target identified"
            -- exits without returns need to either be a jump, branch or tail calls
            -- we consider those cases here (having already assumed a specific
            -- block exit condition)
            case ecase of
              MCS.MacawBlockEndCall | hasStub stubPair ->
                handleStub scope bundle currBlock d gr pPair Nothing stubPair
              MCS.MacawBlockEndCall -> handleTailFunCall scope bundle currBlock d gr pPair
              MCS.MacawBlockEndJump -> fnTrace "handleJump" $ handleJump scope bundle currBlock d gr nextNode
              MCS.MacawBlockEndBranch -> fnTrace "handleJump" $ handleJump scope bundle currBlock d gr nextNode
              _ -> throwHere $ PEE.BlockExitMismatch
  case res of
    Just st' -> return st'
    Nothing -> do
      emitTrace @"message" "Block exit is unreachable"
      return st

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
handleArchStmt scope bundle currBlock d gr endCase pPair mpRetPair = fnTrace "handleArchStmt" $ case endCase of
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
  MCS.MacawBlockEndCall | Just retPair <- mpRetPair -> do
    -- we don't know what to do with arch statements yet, so we just
    -- ignore them and immediately jump to the return address
    _ <- emitWarning $ PEE.NotImplementedYet "handleArchStmt"
    handleJump scope bundle currBlock d gr (mkNodeEntry currBlock retPair)
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
handleInlineCallee _scope _bundle _currBlock _d gr _pPair _pRetPair = fnTrace "handleInlineCallee" $ do
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
handleTailFunCall scope bundle currBlock d gr pPair = fnTrace "handleTailFunCall" $
  case asFunctionPair pPair of
    Just fnPair -> do
      priority <- thisPriority
      emitTraceLabel @"funcall" PB.TailFunCall fnPair
      currBlock' <- asks (PCfg.cfgContextSensitivity . envConfig) >>= \case
        PCfg.SharedFunctionAbstractDomains -> return currBlock
        PCfg.DistinctFunctionAbstractDomains -> return $ addContext pPair currBlock
      -- find the function call block to determine where this tail will ultimately return to
      funEntry <- PPa.forBins $ \bin -> do
        blk <- PPa.get bin $ nodeBlocks currBlock
        return $ PB.blockFunctionEntry blk
      -- node representing the return sites of the caller
      let
        callerFunNode = mkNodeReturn currBlock funEntry
        tailCallFunNode = mkNodeReturn currBlock' fnPair
        tailCallNode = mkNodeEntry currBlock' pPair
        callers = getReturnVectors gr callerFunNode
        gr' = Set.foldl' (\gr'' caller -> addReturnVector gr'' tailCallFunNode caller (tagPriority (show tailCallNode) (priority PriorityHandleReturn))) gr callers
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
handleOrdinaryFunCall scope bundle currBlock d gr pPair pRetPair = fnTrace "handleOrdinaryFunCall" $
   case asFunctionPair pPair of
     Just fnPair ->
       do
          priority <- thisPriority
          emitTraceLabel @"funcall" PB.NormalFunCall fnPair
          -- augmenting this block with the return point as its calling context
          currBlock' <- asks (PCfg.cfgContextSensitivity . envConfig) >>= \case
            PCfg.SharedFunctionAbstractDomains -> return currBlock
            PCfg.DistinctFunctionAbstractDomains -> return $ addContext pRetPair currBlock
          let
            funNode = mkNodeReturn currBlock' fnPair
            returnSite = mkNodeEntry currBlock pRetPair
            callNode = mkNodeEntry currBlock' pPair
            gr' = addReturnVector gr funNode returnSite (tagPriority (show callNode) (priority PriorityHandleReturn))
          matches <- PD.matchingExits bundle MCS.MacawBlockEndCall
          withAssumption matches $
            handleJump scope bundle currBlock d gr' callNode
     _ -> panic Verifier "handleOrdinaryFunCall"
              [ "Ordinary function call jumped to a location that is not a function start!"
              , show currBlock
              , show pPair
              , show pRetPair
              ]

data FnStubKind = DefinedFn | UndefinedFn | SkippedFn | IgnoredFn | DivergedJump | TerminalFn
  deriving (Eq, Ord, Show)

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "fnstub" where
  type TraceNodeType '(sym,arch) "fnstub" = String
  type TraceNodeLabel "fnstub" = FnStubKind
  prettyNode DefinedFn nm = "Defined Function stub call:" <+> PP.pretty nm
  prettyNode UndefinedFn nm = "Undefined Function stub call:" <+> PP.pretty nm
  prettyNode SkippedFn _nm = "Skipped unnamed function"
  prettyNode IgnoredFn nm = "Ignoring function:" <+> PP.pretty nm
  prettyNode DivergedJump nm = "Diverging jump:" <+> PP.pretty nm
  prettyNode TerminalFn nm = "Terminal Function:" <+> PP.pretty nm
  nodeTags = mkTags @'(sym,arch) @"fnstub" [Summary, Simplified]
  jsonNode _ = \v lbl -> return $ JSON.object [ "fnstub" JSON..= lbl, "kind" JSON..= (show v)]
  
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
  let fPair = PPa.map PB.blockFunctionEntry (nodeBlocks node)
  return $ addTerminalNode gr (mkNodeReturn node fPair)

getStubOverrideOne ::
  PB.ConcreteBlock arch bin ->
  Maybe PB.FunctionSymbol ->
  EquivM sym arch (Maybe (PA.StubOverride arch))
getStubOverrideOne blk mstubSymbol = do
  PA.SomeValidArch archData <- asks envValidArch
  case mstubSymbol of
    Just stubSymbol | stubSymbol == skippedFnSym -> do
      emitTraceLabel @"fnstub" SkippedFn ""
      return Nothing
    Just stubSymbol | isIgnoredBlock blk -> do
      emitTraceLabel @"fnstub" IgnoredFn (show stubSymbol)
      return Nothing
    Just stubSymbol | Just f <- PA.lookupStubOverride archData stubSymbol -> do
      emitTraceLabel @"fnstub" DefinedFn (show stubSymbol)
      return $ Just f
    Just stubSymbol | PD.isAbortStub stubSymbol -> do
      emitTraceLabel @"fnstub" TerminalFn (show stubSymbol)
      return Nothing
    Nothing | isIgnoredBlock blk -> do
      emitTraceLabel @"fnstub" IgnoredFn (show skippedFnSym)
      return $ Nothing
    _ -> do
      emitTraceLabel @"fnstub" DivergedJump (show (PP.pretty blk))
      return Nothing
      
combineOverrides ::
  PPa.PatchPairC (PA.StubOverride arch) ->
  PA.StubOverride arch
combineOverrides (PPa.PatchPairSingle _ (Const f)) = f
combineOverrides (PPa.PatchPairC (PA.StubOverride f1) (PA.StubOverride f2)) = PA.StubOverride $ \sym archInfo wsolver -> do
  f1' <- f1 sym archInfo wsolver
  f2' <- f2 sym archInfo wsolver
  let fnPair = PPa.PatchPairC f1' f2'
  return $ PA.StateTransformer $ \(st :: PS.SimState sym arch v bin) -> do
    let (bin :: PBi.WhichBinaryRepr bin) = knownRepr
    Just (PA.StateTransformer fn) <- return $ PPa.getC bin fnPair
    fn st

-- We need to make sure that we only "merge" stubs
-- if we have mismatched stubs, otherwise we will
-- break the stub semantics
mergeStubOverrides ::
  PPa.PatchPairM m =>
  PA.ValidArchData arch ->
  StubPair ->
  PPa.PatchPairC (Maybe (PA.StubOverride arch)) ->
  m (PA.StubOverride arch)
mergeStubOverrides validArch
  (PPa.PatchPairC sym1 sym2)
  (PPa.PatchPairC mov1 mov2) =
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
    (Just nm1, Just nm2) | nm1 == nm2 -> return ov1'
    _ -> return $ combineOverrides (PPa.PatchPairC ov1' ov2')
mergeStubOverrides validArch _ (PPa.PatchPairSingle _ (Const mov)) = case mov of
  Just ov -> return ov
  Nothing -> return $ PA.defaultStubOverride validArch
mergeStubOverrides _ (PPa.PatchPairSingle{}) (PPa.PatchPair{}) = PPa.throwPairErr

-- FIXME: re-evaluate how safe inlining is
{-
bothDefinedOverrides ::
  PPa.PatchPair (Const (Maybe (PA.StubOverride arch))) ->
  Bool
bothDefinedOverrides (PPa.PatchPair (Const (Just{})) (Const (Just{}))) = True
bothDefinedOverrides _ = False
-}

isMismatchedStubs :: StubPair -> Bool
isMismatchedStubs (PPa.PatchPairSingle{}) = False
isMismatchedStubs (PPa.PatchPairC ma mb) = case (ma, mb) of
  (Just a, Just b) -> a /= b
  (Just{}, Nothing) -> True
  (Nothing, Just{}) -> True
  (Nothing, Nothing) -> False

singletonBundle ::
  PBi.WhichBinaryRepr bin ->
  SimBundle sym arch v ->
  EquivM sym arch (SimBundle sym arch v)
singletonBundle bin (SimBundle in_ out_) = 
  SimBundle <$> PPa.toSingleton bin in_ <*> PPa.toSingleton bin out_



{-
-- | Check if the given node has defined sync addresses. If so,
--   connect it to the one-sided Original version of the node and
--   queue it in the worklist.
--   Returns 'Nothing' if the node does not have sync addresses defined
--   (i.e. it is not the start of a split analysis)
handleSplitAnalysis ::
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
handleSplitAnalysis scope node dom pg = do
  let syncAddrs = evalPairGraphM pg $ do
        syncO <- getSyncAddresses PBi.OriginalRepr (GraphNode node)
        syncP <- getSyncAddresses PBi.PatchedRepr (GraphNode node)
        return (syncO, syncP)
  case syncAddrs of
    Right (syncO, syncP) -> do
      currBlockO <- toSingleNode PBi.OriginalRepr node
      currBlockP <- toSingleNode PBi.PatchedRepr node
      subTree @"node" "Split analysis" $ do
        pg' <- subTrace @"node" (GraphNode currBlockO) $ do
          priority <- thisPriority
          emitTraceLabel @"address" "Synchronization Address" syncO
          bundleO <- noopBundle scope (nodeBlocks currBlockO)
          atPriority (raisePriority (priority PriorityHandleDesync)) Nothing $ do
            -- we arbitrarily pick the original program to perform the first step of
            -- the analysis
            -- by convention, we define the sync point of the original program to
            -- connect to the divergence point of the patched program
            widenAlongEdge scope bundleO (GraphNode node) dom pg (GraphNode currBlockO)
        subTrace @"node" (GraphNode currBlockP) $ do
          emitTraceLabel @"address" "Synchronization Address" syncP
        return $ Just pg'
    Left{} -> return Nothing
-}

handleDivergingPaths ::
  HasCallStack =>
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  BranchState sym arch ->
  AbstractDomain sym arch v {- ^ current abstract domain -}  ->
  PPa.PatchPair (PB.BlockTarget arch) {- ^ next entry point -} ->
  EquivM sym arch (BranchState sym arch)  
handleDivergingPaths scope bundle currBlock st dom blkt = fnTrace "handleDivergingPaths" $ do
  let gr0 = branchGraph st
  let mchoice = branchDesyncChoice st
  priority <- thisPriority
  currBlockO <- toSingleNode PBi.OriginalRepr currBlock
  currBlockP <- toSingleNode PBi.PatchedRepr currBlock
  (handled, gr1) <- runPG gr0 $ handleKnownDesync priority currBlock blkt
  case handled of
    True -> do
      emitTrace @"message" $ "Known desynchronization point. Queue split analysis."
      return $ st{ branchGraph = gr1 }
    False -> do
      divergeNode <- toTwoSidedNode $ GraphNode currBlock
      let someDivergeNode = Qu.coerceToExists divergeNode
      let pg = gr1
      let msg = "Control flow desynchronization found at: " ++ show divergeNode
      a <- case mchoice of
        Just bc | choiceRequiresRequeue bc -> return bc
        _ -> do
          () <- withTracing @"message" "Equivalence Counter-example" $ withSym $ \sym -> do
            -- we've already introduced the path condition here, so we just want to see how we got here
            res <- getSomeGroundTrace scope bundle dom Nothing
            emitTrace @"trace_events" res
            return ()
          choose @"()" msg $ \choice -> forM_ [minBound..maxBound] $ \bc ->
            choice (show bc) () $ return bc
      emitTrace @"message" $ "Resolved control flow desynchronization with: " ++ show a
      let st' = st { branchDesyncChoice = Just a }
      case a of
        -- leave block exit as unhandled
        AdmitNonTotal -> return st'
        ChooseSyncPoint -> do
          pg1 <- withPG_ pg $ do
            liftEqM_ $ chooseSyncPoint divergeNode
            liftPG $ addDesyncExits divergeNode blkt
            liftPG $ queueSplitAnalysis (priority PriorityHandleDesync) currBlock
          return $ st'{ branchGraph = pg1 }
          -- handleDivergingPaths scope bundle currBlock (st'{ branchGraph = pg2 }) dom blkt
        ChooseDesyncPoint -> do
          pg1 <- chooseDesyncPoint divergeNode pg
          -- drop domains from any outgoing edges, since the set of outgoing edges
          -- from this node will likely change
          let pg2 = dropPostDomains someDivergeNode (priority PriorityDomainRefresh) pg1
          -- re-queue the node after picking a de-synchronization point
          let pg3 = queueNode (priority PriorityHandleActions) divergeNode pg2
          return $ st'{ branchGraph = pg3 }
        IsInfeasible condK -> do
          gr2 <- pruneCurrentBranch scope (someDivergeNode, GraphNode currBlockO) condK pg
          gr3 <- pruneCurrentBranch scope (someDivergeNode, GraphNode currBlockP) condK gr2
          return $ st'{ branchGraph = gr3 }
        DeferDecision -> do
          -- add this back to the work list at a low priority
          -- this allows, for example, the analysis to determine
          -- that this is unreachable (potentially after refinements) and therefore
          -- doesn't need synchronization
          Just pg1 <- return $ addToWorkList True someDivergeNode (priority PriorityDeferred) pg
          return $ st'{ branchGraph = pg1 }
        AlignControlFlow condK -> fnTrace "AlignControlFlow" $ withSym $ \sym -> do
          traces <- bundleToInstrTraces bundle
          pg2 <- case traces of
            PPa.PatchPairC traceO traceP -> do
              -- NOTE: this predicate is not satisfiable in the current assumption
              -- context: we are assuming a branch condition that leads to
              -- a control flow divergence, and this predicate states exact control
              -- flow equality.
              -- Given this, it can't be simplified using the solver here.
              -- It can be simplified later outside of this context, once it has been
              -- added to the assumptions for the node
              traces_eq_ <- compareSymSeq sym traceO traceP $ \evO evP ->
                return $ W4.backendPred sym (ET.instrDisassembled evO == ET.instrDisassembled evP)
              -- if-then-else expressions for booleans are a bit clumsy and don't work well
              -- with simplification, but the sequence comparison introduces them
              -- at each branch point, so we convert them into implications
              traces_eq <- IO.liftIO $ WEH.iteToImp sym traces_eq_
              pg1 <- addToEquivCondition scope (GraphNode currBlock) condK traces_eq pg
              -- drop all post domains from this node since they all need to be re-computed
              -- under this additional assumption/assertion
              return $ dropPostDomains (GraphNode currBlock) (priority PriorityDomainRefresh) pg1
            _ -> return pg
          return $ st'{ branchGraph = pg2 }

ppMux :: (f -> PP.Doc a) -> MT.MuxTree sym f -> PP.Doc a
ppMux ppf mt = case MT.viewMuxTree mt of
  [] -> error "ppMux"
  [(a,_)] -> ppf a
  xs -> PP.hsep $ PP.punctuate "OR" (["("] ++ (map (\(a,_) -> ppf a) xs) ++ [")"])

bundleToInstrTraces ::
  PS.SimBundle sym arch v ->
  EquivM sym arch (PPa.PatchPairC (ET.InstructionTrace sym arch))
bundleToInstrTraces bundle = withSym $ \sym -> PPa.forBinsC $ \bin -> do
  out_ <- PPa.get bin (simOut bundle)
  let evt = MT.memInstrSeq (PS.simOutMem out_)
  goalTimeout <- asks (PCfg.cfgGoalTimeout . envConfig)
  evt' <- feasiblePaths sym (withAssumption) (concretePred goalTimeout) evt
  shareMuxPrefix sym evt'

data DesyncChoice =
    AdmitNonTotal
  | IsInfeasible ConditionKind
  | ChooseDesyncPoint
  | ChooseSyncPoint
  | DeferDecision
  | AlignControlFlow ConditionKind
  deriving (Eq,Ord)

allDesyncChoice :: [DesyncChoice]
allDesyncChoice =
      [AdmitNonTotal
      ] ++ map IsInfeasible [minBound..maxBound]
      ++
      [ ChooseDesyncPoint
      , ChooseSyncPoint
      , DeferDecision
      ] ++ map AlignControlFlow [minBound..maxBound]

instance Bounded DesyncChoice where
  minBound = head allDesyncChoice
  maxBound = last allDesyncChoice

instance Enum DesyncChoice where
  toEnum i = allDesyncChoice !! i
  fromEnum e = fromMaybe minBound (findIndex ((==) e) allDesyncChoice)

instance Show DesyncChoice where
  show = \case
    ChooseSyncPoint -> "Choose synchronization points"
    ChooseDesyncPoint -> "Choose desynchronization points"
    AdmitNonTotal -> "Ignore divergence (admit a non-total result)"
    IsInfeasible ConditionAsserted -> "Assert divergence is infeasible"
    IsInfeasible ConditionAssumed -> "Assume divergence is infeasible"
    IsInfeasible ConditionEquiv -> "Remove divergence in equivalence condition"
    DeferDecision -> "Defer decision"
    AlignControlFlow ConditionEquiv -> "Align control flow in equivalence condition"
    AlignControlFlow condK -> conditionAction condK ++ " control flow alignment"


choiceRequiresRequeue :: DesyncChoice -> Bool
choiceRequiresRequeue = \case
  AdmitNonTotal -> False
  ChooseSyncPoint -> False
  _ -> True

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
handleStub scope bundle currBlock d gr0_ pPair mpRetPair stubPair = fnTrace "handleStub" $ withSym $ \sym -> do 
  gr0 <- case hasTerminalStub stubPair of
    True -> handleTerminalFunction currBlock gr0_
    False -> return gr0_
  PA.SomeValidArch archData <- asks envValidArch
  ovPair <- PPa.forBins $ \bin -> do
    blk <- PPa.get bin pPair
    Const stub <- PPa.get bin stubPair
    Const <$> getStubOverrideOne blk stub
  case bothTerminalStub stubPair of
    True -> return gr0
    False -> do
      ov <- mergeStubOverrides archData stubPair ovPair
      wsolver <- getWrappedSolver
      -- FIXME: should we pass in the archInfo for each binary to each stub separately?
      -- currently it's only used to get the architecture endianness, which realistically
      -- shouldn't change between the patched and original binaries
      origBinary <- PMC.binary <$> getBinCtx' PBi.OriginalRepr
      let archInfo = PA.binArchInfo origBinary
      unfold_simplifier <- PSi.mkSimplifier PSi.unfoldDefsStrategy
      pretty_simplifier <- PSi.mkSimplifier PSi.prettySimplifier

      outputs <- IO.withRunInIO $ \runInIO ->
        PA.withStubOverride sym archInfo wsolver ov $ \f -> runInIO $ do
          {- out <- PSi.applySimplifier unfold_simplifier (TF.fmapF PS.simOutState (PS.simOut bundle))
          nextStPair_ <- liftIO $ f out
          nextStPair <- PSi.applySimplifier unfold_simplifier nextStPair_ -}
          nextStPair <- liftIO $ f (PPa.map PS.simOutState (PS.simOut bundle))
          PPa.forBins $ \bin -> do
            nextSt <- PPa.get bin nextStPair
            output <- PPa.get bin (PS.simOut bundle)
            return $ output { PS.simOutState = nextSt }
      let bundle' = bundle { PS.simOut = outputs }
      gr1 <- checkObservables scope currBlock bundle' d gr0
      case mpRetPair of
        Just pRetPair -> handleJump scope bundle' currBlock d gr1 (mkNodeEntry currBlock pRetPair)
        -- FIXME: unclear what to do here?
        Nothing -> fnTrace "handeReturn" $ handleReturn scope bundle' currBlock d gr1

handleReturn ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
handleReturn scope bundle currBlock d gr =
 do let fPair = PPa.map PB.blockFunctionEntry (nodeBlocks currBlock)
    let ret = mkNodeReturn currBlock fPair
    let next = ReturnNode ret
    withTracing @"node" next $ 
      widenAlongEdge scope bundle (GraphNode currBlock) d gr next

handleJump ::
  HasCallStack =>
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
  forall sym arch v.
  PairGraph sym arch ->
  NodeEntry arch ->
  PPa.PatchPair (PS.SimVars sym arch v) {- ^ initial variables -} ->
  EquivM sym arch (SimBundle sym arch v)
mkSimBundle _pg node varsPair = fnTrace "mkSimBundle" $ do
  results_pair <- PPa.forBins $ \bin -> withTracing @"binary" (Some bin) $ do
    vars <- PPa.get bin varsPair
    simIn_ <- mkSimIn node vars
    simOut_ <- mkSimOut simIn_
    return $ TupleF2 simIn_ simOut_
  let 
    simIn_pair = PPa.map (\(TupleF2 x _) -> x) results_pair
    simOut_pair = PPa.map (\(TupleF2 _ x) -> x) results_pair
  return (PS.SimBundle simIn_pair simOut_pair)

mkSimOut ::
  forall bin sym arch v.
  PBi.KnownBinary bin =>
  PS.SimInput sym arch v bin ->
  EquivM sym arch (PS.SimOutput sym arch v bin)
mkSimOut simIn_ = do
  let (bin :: PBi.WhichBinaryRepr bin) = knownRepr
  binCtx <- getBinCtx' bin
  let pfm = PMC.parsedFunctionMap binCtx
  simOut_ <- mkSimOut' simIn_
  newEdges <- resolveClassifierErrors simIn_ simOut_ 
  case Map.null newEdges of
    True -> return $ simOut_
    False -> do
      withTracing @"debug" ("Retrying with extra edges: " ++ show newEdges) $ do
        liftIO $ PD.addExtraEdges pfm newEdges
        mkSimOut' simIn_

mkSimIn ::
  forall bin sym arch v.
  PBi.KnownBinary bin =>
  NodeEntry arch ->
  PS.SimVars sym arch v bin ->
  EquivM sym arch (PS.SimInput sym arch v bin)
mkSimIn node vars = fnTrace "mkSimIn" $ do
  let (bin :: PBi.WhichBinaryRepr bin) = knownRepr
  let pPair = nodeBlocks node
  let varState = PS.simVarState vars
  blk <- PPa.get bin pPair
  absState <- PD.getAbsDomain blk
  return $ PS.SimInput varState blk absState  

mkSimOut' ::
  forall bin sym arch v.
  PBi.KnownBinary bin =>
  PS.SimInput sym arch v bin ->
  EquivM sym arch (PS.SimOutput sym arch v bin)
mkSimOut' simIn_ = do
  let (bin :: PBi.WhichBinaryRepr bin) = knownRepr
  binCtx <- getBinCtx' bin
  let pfm = PMC.parsedFunctionMap binCtx
  extraTargets <- liftIO $ PD.getExtraTargets pfm
  emitTraceLabel @"debug" ("Extra Targets for: " ++ show (PS.simInBlock simIn_)) (show extraTargets)
  let 
    isKilled :: forall ids. MD.ParsedBlock arch ids -> Bool
    isKilled pblk = Set.member (MD.pblockAddr pblk) extraTargets
  (_asm, simOut_) <- PVSy.simulate simIn_ isKilled
  return $ simOut_