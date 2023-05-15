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

module Pate.Verification.StrongestPosts
  ( pairGraphComputeFixpoint
  , runVerificationLoop
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( view, (^.) )
import           Control.Monad (foldM, forM, unless, void, when)
import           Control.Monad.IO.Class
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Reader (asks, local)
import           Control.Monad.Except (catchError)
import           Control.Monad.Trans (lift)
import           Numeric (showHex)
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (findIndex)
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
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof.Instances as PPI
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Register.Traversal as PRt
import           Pate.Discovery.PLT (extraJumpClassifier, ExtraJumps(..), ExtraJumpTarget(..))

import           Pate.TraceTree
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.ConditionalEquiv as PVC
import qualified Pate.Verification.Simplify as PSi

import           Pate.Verification.PairGraph
import           Pate.Verification.PairGraph.Node ( GraphNode(..), NodeEntry, mkNodeEntry, mkNodeReturn, nodeBlocks, addContext, returnToEntry, graphNodeBlocks, returnOfEntry, NodeReturn (nodeFuns), asSingleReturn, rootEntry, rootReturn, getDivergePoint, asSingleNode, mkNodeEntry', functionEntryOf, eqUptoDivergePoint, asSingleGraphNode )
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
          pg0 <- chooseEntryPoint pPairs emptyPairGraph
          result <- catchError (do
            -- Do the main work of computing the dataflow fixpoint
            pg <- pairGraphComputeFixpoint pPairs pg0
            -- Report a summary of any errors we found during analysis
            pg1 <- handleDanglingReturns pPairs pg
            reportAnalysisErrors (envLogger env) pg1
            pairGraphComputeVerdict pg1) (pure . PE.Errored)

          emitEvent (PE.StrongestPostOverallResult result)

          

          -- TODO, does reporting these kind of statistics make sense for this verification method?
          -- Currently, we only really do this to make the types fit at the call site.
          statVar <- asks envStatistics
          stats <- liftIO $ MVar.readMVar statVar

          return (result, stats)

asEntry :: PB.FunPair arch -> NodeEntry arch
asEntry fnPair = 
  let 
  bPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair
  in (rootEntry bPair)

asRootEntry :: GraphNode arch -> Maybe (PB.FunPair arch )
asRootEntry (GraphNode ne) = Just (TF.fmapF PB.blockFunctionEntry (nodeBlocks ne))
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
        resetBlockCache envExitPairsCache
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
        (ret :_) | shouldAddOrphans -> choice_outer "Add orphaned return nodes?" () $ fmap Just $ do
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
          {-
          [dual] -> do
            Just dom1 <- return $ getCurrentDomain pg0 (ReturnNode ret)
            Just dom2 <- return $ getCurrentDomain pg0 (ReturnNode dual)
            Just combined <- return $ combineNodes (ReturnNode ret) (ReturnNode dual)
            mergeDualNodes (ReturnNode ret) (ReturnNode dual) dom1 dom2 combined pg0
           -}
          _ -> do
            let fn_single_ = PPa.mkSingle (PB.functionBinRepr fn_single) fn_single
            err <- emitError' (PEE.OrphanedSingletonAnalysis fn_single_)
            return $ recordMiscAnalysisError pg0 (ReturnNode ret) err
         
  foldM go pg single_rets 



-- If the given 'GraphNode' is a synchronization point (i.e. it has
-- a corresponding synchronization edge), then we need to pop it from
-- the worklist and instead enqueue the corresponding biprogram nodes
handleSyncPoint ::
  PairGraph sym arch ->
  GraphNode arch ->
  PAD.AbstractDomainSpec sym arch ->
  EquivM sym arch (Maybe (PairGraph sym arch))
handleSyncPoint pg nd _spec = case getDivergePoint nd of
  -- not a diverging node
  Nothing -> return Nothing
  Just divergeNode -> do
    Just (Some bin) <- return $ singleNodeRepr nd
    case getSyncPoint pg bin divergeNode of
      Just sync  -> do
        case nd == sync of
          True -> Just <$> updateCombinedSyncPoint divergeNode pg
           -- We have a sync node but it hasn't been processed yet, so continue execution
          False -> return Nothing
      Nothing -> return Nothing


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

-- | Given a source divergent node, pick a synchronization point where
--   control flow should again match between the two binaries
chooseSyncPoint :: 
  GraphNode arch -> 
  PairGraph sym arch -> 
  EquivM sym arch (PairGraph sym arch)
chooseSyncPoint nd pg0 = do
  divergePair@(PPa.PatchPairC divergeO divergeP) <- PPa.forBinsC $ \bin -> do
    let ret = case nd of
          GraphNode ne -> returnOfEntry ne
          ReturnNode nr -> nr
    blk <- PPa.get bin (graphNodeBlocks nd)
    pblks <- PD.lookupBlocks blk
    retSingle <- asSingleReturn bin nd ret
    divergeSingle <- asSingleGraphNode bin nd
    return $ (retSingle, divergeSingle, Some blk, pblks)
  (sync, Some syncBin) <- pickSyncPoint [divergeO, divergeP]
  let otherBin = PBi.flipRepr syncBin
  pg1 <- setSyncPoint pg0 nd sync

  case sync of
    GraphNode{} -> do
      diverge <- PPa.getC otherBin divergePair
      syncOther <- fst <$> pickSyncPoint [diverge]
      setSyncPoint pg1 nd syncOther
    ReturnNode{} -> do
      (retSingle, _, _, _) <- PPa.getC otherBin divergePair
      setSyncPoint pg1 nd (ReturnNode retSingle)

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

pickSyncPoint ::
  [(NodeReturn arch, GraphNode arch, Some (PB.ConcreteBlock arch), PD.ParsedBlocks arch)] -> 
  EquivM sym arch (GraphNode arch, Some PBi.WhichBinaryRepr)
pickSyncPoint inputs = do
  (sync, Some bin, maddr) <- choose @"node" "Choose a synchronization point:" $ \choice -> do
    forM_ inputs $ \(retSingle, divergeSingle, Some blk, PD.ParsedBlocks pblks) -> do
      let bin = PB.blockBinRepr blk
      forM_ pblks $ \pblk -> forM_ (getIntermediateAddrs pblk) $ \addr -> do
        -- FIXME: block entry kind is unused at the moment?
        let concBlk = PB.mkConcreteBlock blk PB.BlockEntryJump addr
        let node = mkNodeEntry' divergeSingle (PPa.mkSingle bin concBlk)
        choice "" (GraphNode node) $ do
          
          return (GraphNode node, Some bin, Just (addr, Some concBlk))
      choice "" (ReturnNode retSingle) $ return (ReturnNode retSingle, Some bin, Nothing)
  case maddr of
    Just (addr, Some blk) -> do
      _ <- addIntraBlockCut addr blk
      -- this is a heuristic that attempts to capture the fact that
      -- the patched binary likely has additional control flow that we
      -- want to analyze as part of the synchronization block, but only
      -- up to exactly the instruction where control flow re-synchronizes
      case bin of
        PBi.OriginalRepr -> cutAfterAddress addr blk
        PBi.PatchedRepr -> return ()
    Nothing -> return ()
  return (sync, Some bin)

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

{-
handleSyncPoint _ (GraphNode{}) _ = return Nothing
handleSyncPoint pg (ReturnNode nd) spec = case nodeFuns nd of
  PPa.PatchPair{} -> do
    ndO <- asSingleReturn PBi.OriginalRepr nd
    ndP <- asSingleReturn PBi.PatchedRepr nd
    -- if both single-sided cases have finished processing, then we can process
    -- the return as usual
    case (getCurrentDomain pg (ReturnNode ndO), getCurrentDomain pg (ReturnNode ndP)) of
      (Just{}, Just{}) -> return Nothing
      -- if either single-sided is not finished, we pop this return from the work
      -- list under the assumption that it will be handled later
      _ -> return $ Just pg
  PPa.PatchPair{} -> return Nothing
  PPa.PatchPairSingle bin _ -> case getSyncPoint pg nd of
    Just syncs -> do
      let go gr' nd' = case asSingleReturn (PBi.flipRepr bin) nd' of
            Just nd_other -> case getCurrentDomain pg (ReturnNode nd_other) of
              -- dual node has a spec, so we can merge them and add the result to the graph
              -- as the sync point
              Just{} | PPa.PatchPairC ndO ndP <- PPa.mkPair bin (Const nd) (Const nd') -> 
                chooseSyncPoint (ReturnNode ndO) (ReturnNode ndP) pg
              -- if the dual node is not present in the graph, we assume it will
              -- be handled when the dual case is pushed through the verifier, so
              -- we drop it here
              _ -> return gr'
            Nothing -> PPa.throwPairErr
      Just <$> foldM go pg (Set.elems syncs)
    Nothing -> return Nothing
-}



-- FIXME: this is pretty brittle, as it makes a bunch of assumptions about
-- the graph state
updateCombinedSyncPoint ::
  GraphNode arch {- ^ diverging node -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
updateCombinedSyncPoint divergeNode pg = fnTrace "updateCombinedSyncPoint" $ case getCombinedSyncPoint pg divergeNode of
  Nothing -> do
    emitTrace @"message" ("No sync node found for: " ++ show divergeNode)
    return pg
  Just (combinedNode, _) -> do
    PPa.PatchPairC (syncO, mdomO) (syncP, mdomP) <-
      PPa.forBinsC $ \bin -> do
        Just sync <- return $ getSyncPoint pg bin divergeNode
        mdom <- return $ getCurrentDomain pg sync
        return $ (sync, mdom)
    case (mdomO, mdomP) of
      -- if we have finished analyzing the original program up to the sync point,
      -- then we need to attach this to the divergence point of the patched program
      (Just{}, Nothing) -> do
        priority <- thisPriority
        case getCurrentDomain pg divergeNode of
          Nothing -> return $ queueNode (priority PriorityHandleDesync) divergeNode pg 
          Just dom_spec -> do
            fmap (\x -> PS.viewSpecBody x PS.unWS) $ PS.forSpec dom_spec $ \scope dom -> fmap PS.WithScope $ do
              domP <- PAD.singletonDomain PBi.PatchedRepr dom
              divergeNodeP <- asSingleGraphNode PBi.PatchedRepr divergeNode
              bundle <- noopBundle scope (graphNodeBlocks divergeNodeP)
              pg1 <- case getCurrentDomain pg divergeNodeP of
                Nothing -> return $ updateDomain' pg syncO divergeNodeP (PS.mkSimSpec scope domP) (priority PriorityWidening)
                Just{} -> return pg
              withPredomain scope bundle domP $ withConditionsAssumed scope syncO pg1 $
                widenAlongEdge scope bundle syncO domP pg1 divergeNodeP
      (Just domO_spec, Just domP_spec) -> do
      -- similarly if we've finished analyzing the patched program, then by convention
      -- we connect the post-domain of the to the merged sync point
        mergeDualNodes syncO syncP domO_spec domP_spec combinedNode pg
      _ -> withTracing @"message" "Missing domain(s) for sync points" $ do
        priority <- thisPriority
        divergeNodeO <- asSingleGraphNode PBi.OriginalRepr divergeNode
        return $ queueNode (priority PriorityDomainRefresh) divergeNodeO $ queueAncestors (priority PriorityHandleDesync) syncO pg

{-
-- | Connect two nodes with a no-op
atomicJump ::
  (GraphNode arch, GraphNode arch) -> 
  PAD.AbstractDomainSpec sym arch -> 
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
atomicJump (from,to) domSpec gr0 = withSym $ \sym -> do
-}

addImmediateEqDomRefinementChoice ::
  GraphNode arch ->
  PAD.AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
addImmediateEqDomRefinementChoice nd preD gr0 = do
  let gr1 = gr0
  choose @"()" ("Refine equivalence domain for sync point?") $ \choice -> do
    let go condK = do
          let msg = conditionAction condK
          choice (msg ++ " condition") () $ do
            locFilter <- refineEquivalenceDomain preD
            return $ addDomainRefinement nd (LocationRefinement condK RefineUsingExactEquality locFilter) gr1
          choice (msg ++ " condition (using intra-block path conditions)") () $ do
            locFilter <- refineEquivalenceDomain preD
            return $ addDomainRefinement nd (LocationRefinement condK RefineUsingIntraBlockPaths locFilter) gr1
          choice (msg ++ " that branch is infeasible") () $
            return $ addDomainRefinement nd (PruneBranch condK) gr1
    choice ("No refinements") () $ return gr1
    mapM_ go [minBound..maxBound]

mergeDualNodes ::
  GraphNode arch {- ^ first program node -} ->
  GraphNode arch {- ^ second program node -} ->
  PAD.AbstractDomainSpec sym arch {- ^ first node domain -} ->
  PAD.AbstractDomainSpec sym arch {- ^ second node domain -} ->
  GraphNode arch {- ^  combined sync node -} ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
mergeDualNodes in1 in2 spec1 spec2 syncNode gr0 = fnTrace "mergeDualNodes" $ withSym $ \sym -> do
  let gr2 = gr0

  let blkPair1 = graphNodeBlocks in1
  let blkPair2 = graphNodeBlocks in2

  fmap (\x -> PS.viewSpecBody x PS.unWS) $ withFreshScope (graphNodeBlocks syncNode) $ \scope -> fmap PS.WithScope $ 
    withValidInit scope blkPair1 $ withValidInit scope blkPair2 $ do
      (_, dom1) <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) spec1
      (_, dom2) <- liftIO $ PS.bindSpec sym (PS.scopeVarsPair scope) spec2
      dom <- PAD.zipSingletonDomains sym dom1 dom2
      bundle <- noopBundle scope (graphNodeBlocks syncNode)
      withPredomain scope bundle dom $ withConditionsAssumed scope in2 gr2 $ do
        withTracing @"node" in2 $ do
          emitTraceLabel @"domain" PAD.Predomain (Some dom)
          widenAlongEdge scope bundle in2 dom gr2 syncNode

-- | Choose some work item (optionally interactively)
chooseWorkItemM ::
  PA.ValidArch arch =>
  PairGraph sym arch ->
  EquivM sym arch (Maybe (NodePriority, PairGraph sym arch, GraphNode arch, PAD.AbstractDomainSpec sym arch))
chooseWorkItemM gr0 = do
  gr0' <- queuePendingNodes gr0
  case chooseWorkItem gr0' of
    Nothing -> return Nothing
    Just (priority, gr1, nd, spec) -> atPriority priority Nothing $ PS.viewSpec spec $ \scope d -> do
      runPendingActions refineActions nd (TupleF2 scope d) gr1 >>= \case
        Just gr2 -> chooseWorkItemM gr2
        Nothing -> return $ Just (priority, gr1, nd, spec)

{-
  let nodes = Set.toList $ pairGraphWorklist gr
  case nodes of
    [] -> return Nothing
    [node] -> return (Just $ popWorkItem gr node)
    _ -> 
    _ -> choose @"node" "chooseWorkItem" $ \choice -> forM_ nodes $ \nd -> 
      choice "" nd $ return (Just $ popWorkItem gr nd)
-}

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
    go (gr0 :: PairGraph sym arch) = (lift $ chooseWorkItemM gr0) >>= \case
      Nothing -> return gr0
      Just (priority, gr1, nd, preSpec) -> do
        gr4 <- subTraceLabel @"node" (printPriorityKind priority) nd $ startTimer $ do
          shouldProcessNode nd >>= \case
            False -> do
              emitWarning $ PEE.SkippedInequivalentBlocks (graphNodeBlocks nd)
              return gr1
            True -> do
              emitTrace @"priority" priority
              atPriority priority (Just (show nd)) $ do
                handleSyncPoint gr1 nd preSpec >>= \case
                  Just gr2 -> return gr2
                  Nothing -> PS.viewSpec preSpec $ \scope d -> do
                    d' <- asks (PCfg.cfgStackScopeAssume . envConfig) >>= \case
                      True -> strengthenStackDomain scope d
                      False -> return d
                    withAssumptionSet (PS.scopeAsm scope) $ do
                      gr2 <- addRefinementChoice nd gr1
                      gr3 <- visitNode scope nd d' gr2
                      emitEvent $ PE.VisitedNode nd
                      return gr3
        go gr4
    
    go_outer :: PairGraph sym arch -> EquivM_ sym arch (PairGraph sym arch)
    go_outer gr = do
      gr1 <- withSubTraces $ go gr
      gr2 <- handleDanglingReturns entries gr1
      refineFinalResult entries gr2 >>= \case
        Just gr3 -> go_outer gr3
        Nothing -> showFinalResult gr2 >> return gr2
  go_outer gr_init

showFinalResult :: PairGraph sym arch -> EquivM sym arch ()
showFinalResult pg = withTracing @"final_result" () $ withSym $ \sym -> do
  subTree @"node" "Observable Counter-examples" $ do
    forM_ (Map.toList (pairGraphObservableReports pg)) $ \(nd,report) -> 
      subTrace (GraphNode nd) $ 
        emitTrace @"observable_result" (ObservableCheckCounterexample report)
  subTree @"node" "Assumed Equivalence Conditions" $ do
    forM_ (getAllNodes pg) $ \nd -> do
       case getCondition pg nd ConditionEquiv of
        Just eqCondSpec -> subTrace nd $ do 
          _ <- PS.forSpec eqCondSpec $ \_scope eqCond -> do
            () <- do
              eqCondPred <- PEE.someExpr sym <$> PEC.toPred sym eqCond
              emitTraceLabel @"eqcond" (eqCondPred) (Some eqCond)
              return ()
            return eqCond
          return ()
        Nothing -> return ()
  result <- pairGraphComputeVerdict pg
  emitTrace @"equivalence_result" result

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
  simOut_ <- IO.withRunInIO $ \runInIO ->
    PA.withStubOverride sym wsolver ov $ \f -> runInIO $ PPa.forBins $ \bin -> do
      input <- PPa.get bin simIn_
      let inSt = PS.simInState input
      outSt <- liftIO $ f inSt
      blkend <- liftIO $ MCS.initBlockEnd (Proxy @arch) sym MCS.MacawBlockEndReturn
      return $ PS.SimOutput outSt blkend

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
      let fnPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks node)  
      case getCurrentDomain gr (GraphNode node) of
        Just preSpec -> PS.viewSpec preSpec $ \_ d' -> PPa.forBins $ \bin -> do
          vals <- PPa.get bin (PAD.absDomVals d')
          fe <- PPa.get bin fnPair
          let absSt = PAD.domainValsToAbsState vals
          return $ Const (Map.singleton (PB.functionSegAddr fe) absSt)
        Nothing -> throwHere $ PEE.MissingDomainForFun fnPair


-- | Setup a special-purpose ParsedFunctionMap with this block having a special
--   domain 
withAbsDomain ::
  HasCallStack =>
  NodeEntry arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM_ sym arch a ->
  EquivM sym arch a
withAbsDomain node d gr f = do
  case asFunctionPair (nodeBlocks node) of
    Nothing -> do
      let fnNode = functionEntryOf node
      case getCurrentDomain gr (GraphNode fnNode)  of
        Just d' -> PS.viewSpec d' $ \_ d'' -> withAbsDomain fnNode d'' gr f
        Nothing -> do
          -- this handles the case where we need to find the domain for this
          -- node but we don't have a singleton variant of the entry point
          case getDivergePoint (GraphNode node) of
            Just (GraphNode divergeNode) -> do
              Just (Some bin) <- return $ singleNodeRepr (GraphNode node)
              let fnNode_diverge = functionEntryOf divergeNode
              fnNode_diverge_single <- asSingleNode bin fnNode_diverge
              case getCurrentDomain gr (GraphNode fnNode_diverge) of
                Just d' | eqUptoDivergePoint (GraphNode fnNode_diverge_single) (GraphNode fnNode) ->
                  PS.viewSpec d' $ \_ d'' -> do
                    d_single <- PAD.singletonDomain bin d''
                    withAbsDomain fnNode d_single gr f
                _ -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnNode)
            _ -> throwHere $ PEE.MissingDomainForBlock (nodeBlocks fnNode)
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
        let fnBlks = TF.fmapF (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) (nodeBlocks node)
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

withSatConditionAssumed ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  ConditionKind ->
  PairGraph sym arch ->
  EquivM_ sym arch (PairGraph sym arch) ->
  EquivM sym arch (PairGraph sym arch)  
withSatConditionAssumed scope nd condK gr0 f = withSym $ \sym -> do
  priority <- thisPriority
  eqCond <- getScopedCondition scope gr0 nd condK
  eqCond_pred <- PEC.toPred sym eqCond
  (withSatAssumption (PAS.fromPred eqCond_pred) (traceEqCond condK eqCond >> f)) >>= \case
    Just result -> return result
    -- for propagated assumptions and assertions, we mark this branch as infeasible
    Nothing | shouldPropagate (getPropagationKind gr0 nd condK) -> do
      gr1 <- return $ addDomainRefinement nd (PruneBranch condK) gr0
      emitTrace @"message" ("Branch dropped as " ++ conditionPrefix condK)
      return $ queueAncestors (priority PriorityPropagation) nd gr1
    -- for non-propagated assumptions we don't attempt to prune this branch,
    -- we just do nothing
    Nothing -> do
      emitTrace @"message" ("Branch is " ++ conditionAction condK ++ " infeasible")
      return gr0


withConditionsAssumed ::
  PS.SimScope sym arch v ->
  GraphNode arch ->
  PairGraph sym arch ->
  EquivM_ sym arch (PairGraph sym arch) ->
  EquivM sym arch (PairGraph sym arch)
withConditionsAssumed scope node gr0 f = do
  foldr go f [minBound..maxBound]
  where 
    go condK g =
      withSatConditionAssumed scope node condK gr0 g

processBundle ::
  forall sym arch v.
  PS.SimScope sym arch v ->
  NodeEntry arch ->
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
processBundle scope node bundle d gr0 = do
  exitPairs <- PD.discoverPairs bundle

  gr1 <- checkObservables node bundle d gr0

  gr2 <- checkTotality node bundle d exitPairs gr1

  gr3 <- return gr2
  -- disable this check for now as we refactor the treatment
  -- for "return" block exits
  {-
  gr3 <- case mgr3 of
    Just gr3 -> return gr3
    Nothing ->
      case exitPairs of
      -- if we find a busy loop, try to continue the analysis assuming we
      -- break out of the loop, even if the semantics say it can't happen
      -- TODO: ideally we should handle this as an "extra" edge rather than
      -- directly handling the widening here.
      [PPa.PatchPair (PB.BlockTarget tgtO Nothing _ _) (PB.BlockTarget tgtP Nothing _ _)] |
        PPa.PatchPair tgtO tgtP == (PS.simPair bundle) ->
        asks (PCfg.cfgAddOrphanEdges . envConfig) >>= \case
          True -> do
            emitWarning $ PEE.BlockHasNoExit (PS.simPair bundle)
            nextBlocks <- PPa.forBins $ \bin -> do
              blk <- PPa.get bin (PS.simPair bundle)
              PD.nextBlock blk >>= \case
                Just nb -> return nb
                Nothing -> throwHere $ PEE.MissingParsedBlockEntry "processBundle" blk
            return $ addExtraEdge gr2 node (GraphNode (mkNodeEntry node nextBlocks))
            --bundle' <- PD.associateFrames bundle MCS.MacawBlockEndJump False
            --widenAlongEdge scope bundle' (GraphNode node) d gr2 (GraphNode (mkNodeEntry node nextBlocks))
          False -> return gr2
      _ -> return gr2
   -}
  -- Follow all the exit pairs we found
  fmap fst $ subTree @"blocktarget" "Block Exits" $
    foldM (\x y@(_,tgt) -> subTrace tgt $ followExit scope bundle node d x y) (gr3, Nothing) (zip [0 ..] exitPairs)

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
    varsSt = TF.fmapF PS.simVarState vars

  validInit <- PVV.validInitState (Just bPair) varsSt
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
  GraphNode arch ->
  AbstractDomain sym arch v ->
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch)
visitNode scope (GraphNode node@(nodeBlocks -> bPair)) d gr0 = 
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
            Nothing -> withConditionsAssumed scope (GraphNode node) gr0 $ processBundle scope node bundle d gr2

visitNode scope (ReturnNode fPair) d gr0 =  do
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
          withConditionsAssumed scope (ReturnNode fPair) gr0' $ 
            return gr0'

   -- Here, we're using a bit of a trick to propagate abstract domain information to call sites.
   -- We are making up a "dummy" simulation bundle that basically just represents a no-op, and
   -- using the ordinary widening machinery.


  processReturn gr0' node@(nodeBlocks -> ret) = withPair ret $ withAbsDomain node d gr0 $ do
    let
      vars = PS.scopeVars scope
      varsSt = TF.fmapF PS.simVarState vars
    validState <- PVV.validInitState (Just ret) varsSt
    withAssumptionSet validState $ do
      (asm, bundle) <- returnSiteBundle scope vars d ret
      withAssumptionSet asm $ withPredomain scope bundle d $ do
        runPendingActions nodeActions (ReturnNode fPair) (TupleF3 scope bundle d) gr0' >>= \case
          Just gr1 -> do
            priority <- thisPriority
            return $ queueNode (priority PriorityHandleActions) (ReturnNode fPair) gr1
          Nothing -> withConditionsAssumed scope (ReturnNode fPair) gr0 $ do
            traceBundle bundle "Processing return edge"
            -- observable events may occur in return nodes specifically
            -- when they are a synchronization point, since the abstract
            -- domain may now contain traces of deferred observable events for both programs
            --
            -- TODO: formally we could just check the event sequence once for the return node
            -- (rather than once for each return edge)
            -- but it would require some refactoring to make the types match up correctly
            gr1' <- checkObservables node bundle d gr0'
    --        traceBundle bundle "== bundle asm =="
    --        traceBundle bundle (show (W4.printSymExpr asm))
            widenAlongEdge scope bundle (ReturnNode fPair) d gr1' (GraphNode node)


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
    postFrame <- liftIO $ PS.freshStackBase sym bin (Proxy @arch)
    let postSt = inSt { PS.simStackBase = PS.simCallerStackBase inSt, PS.simCallerStackBase = postFrame }
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



data ObservableCheckResult sym arch
  = ObservableCheckEq
  | ObservableCheckCounterexample
    (ObservableCounterexample sym arch)
  | ObservableCheckError String

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "observable_result" where
  type TraceNodeType '(sym,arch) "observable_result" = ObservableCheckResult sym arch
  prettyNode () = \case
    ObservableCheckEq -> "Observably Equivalent"
    ObservableCheckCounterexample (ObservableCounterexample regsCE oSeq pSeq) -> PP.vsep $ 
       ["Observable Inequivalence Detected:"
       -- FIXME: this is useful but needs better presentation
       , "== Diverging Registers =="
       , prettyRegsCE regsCE
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
             ] ++
             [(Simplified, \() res -> case res of
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
           ObservableCheckCounterexample cex@(ObservableCounterexample _ oSeq pSeq) -> do
             do traceBundle bundle ("Obserables disagree!")
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
  SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  EquivM sym arch (ObservableCheckResult sym arch)
doCheckObservables bundle preD = case PS.simOut bundle of
  -- for singleton cases, we consider all events to be trivially
  -- observably equivalent, as we are collecting observable events
  -- for future analysis in the domain
  PPa.PatchPairSingle _ _ -> return ObservableCheckEq
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
       not_goal <- liftIO $ W4.notPred sym eqSeq
       goalSat "checkObservableSequences" not_goal $ \res -> case res of
         Unsat _ -> return ObservableCheckEq
         Unknown -> return (ObservableCheckError "UNKNOWN result when checking observable sequences")
         Sat evalFn' -> do
          regsO <- MM.traverseRegsWith (\_ -> PEM.mapExpr sym (\x -> concretizeWithModel evalFn' x)) (PS.simOutRegs outO)
          regsP <- MM.traverseRegsWith (\_ -> PEM.mapExpr sym (\x -> concretizeWithModel evalFn' x)) (PS.simOutRegs outP)
          withGroundEvalFn evalFn' $ \evalFn -> do
           -- NB, observable sequences are stored in reverse order, so we reverse them here to
           -- display the counterexample in a more natural program order
           oSeq'' <- reverse <$> groundObservableSequence sym evalFn oSeq' -- (MT.memSeq oMem)
           pSeq'' <- reverse <$> groundObservableSequence sym evalFn pSeq' -- (MT.memSeq pMem)


           let regsCE = RegsCounterExample regsO regsP

           return (ObservableCheckCounterexample (ObservableCounterexample regsCE oSeq'' pSeq''))

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
          fmap fst <$> groundMuxTree sym evalFn (MT.memCurrentInstr mem)
      case result of
        Just instr_addr -> do
          instr_sym <- PD.thisInstr (PS.simOutState simOut_)
          instr_conc <- justPartExpr sym <$> PD.concreteAddrToLLVM (PAd.segOffToAddr instr_addr)
          eqInstr <- liftIO $ PD.liftPartialRel sym (\p1 p2 -> return $ PAS.ptrBinding p1 p2) instr_sym instr_conc
          is_this_instr <- PAS.toPred sym eqInstr
          with_targets <- withAssumption is_this_instr $ do
            maybeZero >>= \case
              True -> chooseBool ("Classifier Failure: Mark " ++ show instr_addr ++ " as return?") >>= \case
                True -> return $ Map.insert instr_addr ReturnTarget tried
                False -> return tried
              False -> do
                targets <- findTargets Set.empty
                return $ Map.insertWith (<>) instr_addr (DirectTargets targets) tried
          not_this_instr <-  PAS.fromPred <$> (liftIO $ W4.notPred sym is_this_instr)
          fromMaybe with_targets <$> (withSatAssumption not_this_instr $ findOne with_targets)
        Nothing -> return $ tried
  isFailure <- PAS.fromPred <$> PD.matchingExits bundle' MCS.MacawBlockEndFail
  fromMaybe Map.empty <$> (withSatAssumption isFailure $ findOne Map.empty)

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
         Sat evalFn' -> withGroundEvalFn evalFn' $ \evalFn -> do
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
                instr <- lift $ groundMuxTree sym evalFn (MT.memCurrentInstr mem)
                case iPV of
                  Just val -> return $ (Just (val, blockEndCase, instr))
                  Nothing -> return $ Nothing
              case result of
                PPa.PatchPairC (Just ores) (Just pres) ->
                  return (TotalityCheckCounterexample
                    (TotalityCounterexample ores pres))
                PPa.PatchPairSingle _ (Const (Just r)) ->
                  --FIXME: update the type to use PatchPairC
                  return (TotalityCheckCounterexample
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
  (PairGraph sym arch, Maybe DesyncChoice) ->
  (Integer, PPa.PatchPair (PB.BlockTarget arch)) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch, Maybe DesyncChoice)
followExit scope bundle currBlock d (gr, mchoice) (idx, pPair) = do
  traceBundle bundle ("Handling proof case " ++ show idx) 
  res <- manifestError $
    case getQueuedPriority (GraphNode currBlock) gr of
      Just{} -> do
        emitTrace @"message" "Node was re-queued, skipping analysis"
        return (gr,mchoice)
      Nothing -> triageBlockTarget scope bundle currBlock mchoice d gr pPair
  case res of
    Left err -> do
      emitEvent $ PE.ErrorEmitted err
      return (recordMiscAnalysisError gr (GraphNode currBlock) err, mchoice)
    Right gr' -> return gr'


skippedFnName :: BS.ByteString
skippedFnName = BSC.pack "__pate_skipped"

getFunctionStub ::
  forall sym arch bin.
  PBi.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (Maybe BS.ByteString)
getFunctionStub blk = do
  PA.SomeValidArch archData <- asks envValidArch
  PD.findPLTSymbol blk >>= \case
    Just nm -> return $ Just nm
    Nothing | Just fnEntry <- PB.asFunctionEntry blk -> do
      let mnm = PB.functionSymbol fnEntry
      case mnm of
        Just nm | Just{} <- PA.lookupStubOverride archData nm -> return $ Just nm
        Just nm | PD.isAbortStub nm -> return $ Just nm
        Just nm | PB.functionIgnored fnEntry -> return $ Just nm
        Nothing | PB.functionIgnored fnEntry -> return $ Just skippedFnName
        Nothing -> asks (PCfg.cfgIgnoreUnnamedFunctions . envConfig) >>= \case
          True -> return $ Just skippedFnName
          False -> return Nothing
        _ -> return Nothing
    Nothing -> return Nothing

type StubPair = PPa.PatchPairC (Maybe BS.ByteString)

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



-- | Figure out what kind of control-flow transition we are doing
--   here, and call into the relevant handlers.
triageBlockTarget ::
  PS.SimScope sym arch v ->
  SimBundle sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  Maybe DesyncChoice ->
  AbstractDomain sym arch v {- ^ current abstract domain -} ->
  PairGraph sym arch ->
  PPa.PatchPair (PB.BlockTarget arch) {- ^ next entry point -} ->
  EquivM sym arch (PairGraph sym arch, Maybe DesyncChoice)
triageBlockTarget scope bundle' currBlock mchoice d gr blkts =
  do
     stubPair <- fnTrace "getFunctionStubPair" $ getFunctionStubPair blkts
     matches <- PD.matchesBlockTarget bundle' blkts
     maybeUpdate (gr,mchoice) $ withPathCondition matches $ do
      let (ecase1, ecase2) = PPa.view PB.targetEndCase blkts
      mrets <- PPa.toMaybeCases <$> 
        PPa.forBinsF (\bin -> PB.targetReturn <$> PPa.get bin blkts)
      case (combineCases ecase1 ecase2,mrets) of
        (Nothing,_) -> handleDivergingPaths scope currBlock mchoice d gr
        (_,PPa.PatchPairMismatch{}) -> handleDivergingPaths scope currBlock mchoice d gr
        _ | isMismatchedStubs stubPair -> handleDivergingPaths scope currBlock mchoice d gr
        (Just ecase, PPa.PatchPairJust rets) -> fmap (\x -> (x,Nothing)) $ do
          let pPair = TF.fmapF PB.targetCall blkts
          bundle <- PD.associateFrames bundle' ecase (hasStub stubPair)
          traceBundle bundle ("  Return target " ++ show rets)
          isPreArch <- case (PPa.view PB.concreteBlockEntry pPair) of
            (PB.BlockEntryPreArch, PB.BlockEntryPreArch) -> return True
            (entryO, entryP) | entryO == entryP -> return False
            _ -> throwHere $ PEE.BlockExitMismatch
          ctx <- view PME.envCtxL
          let isEquatedCallSite = any (PB.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)

          if | isPreArch -> handleArchStmt scope bundle currBlock d gr ecase pPair (Just rets)
             | isEquatedCallSite -> handleInlineCallee scope bundle currBlock d gr pPair rets
             | hasStub stubPair -> handleStub scope bundle currBlock d gr pPair (Just rets) stubPair
             | otherwise -> handleOrdinaryFunCall scope bundle currBlock d gr pPair rets

        (Just ecase, PPa.PatchPairNothing) -> fmap (\x -> (x,Nothing)) $ do
          bundle <- PD.associateFrames bundle' ecase (hasStub stubPair)
          case ecase of
            MCS.MacawBlockEndReturn -> handleReturn scope bundle currBlock d gr
            _ -> do
              let
                pPair = TF.fmapF PB.targetCall blkts
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
  PPa.PatchPairC (PA.StubOverride arch) ->
  PA.StubOverride arch
combineOverrides (PPa.PatchPairSingle _ (Const f)) = f
combineOverrides (PPa.PatchPairC (PA.StubOverride f1) (PA.StubOverride f2)) = PA.StubOverride $ \sym wsolver -> do
  f1' <- f1 sym wsolver
  f2' <- f2 sym wsolver
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
  SimBundle <$> PPa.asSingleton bin in_ <*> PPa.asSingleton bin out_

handleDivergingPaths ::
  HasCallStack =>
  PS.SimScope sym arch v ->
  NodeEntry arch {- ^ current entry point -} ->
  Maybe DesyncChoice {- ^ previous choice for how to handle desync -} -> 
  AbstractDomain sym arch v {- ^ current abstract domain -}  -> 
  PairGraph sym arch ->
  EquivM sym arch (PairGraph sym arch, Maybe DesyncChoice)  
handleDivergingPaths scope currBlock mchoice dom gr0 = fnTrace "handleDivergingPaths" $ do
  priority <- thisPriority
  currBlockO <- asSingleNode PBi.OriginalRepr currBlock
  currBlockP <- asSingleNode PBi.PatchedRepr currBlock

  case (getSyncPoint gr0 PBi.OriginalRepr (GraphNode currBlock), getSyncPoint gr0 PBi.PatchedRepr (GraphNode currBlock)) of
    (Just{},Just{}) -> do
      bundleO <- noopBundle scope (nodeBlocks currBlockO)

      atPriority (raisePriority (priority PriorityHandleDesync)) Nothing $ do
        -- we arbitrarily pick the original program to perform the first step of
        -- the analysis
        -- by convention, we define the sync point of the original program to
        -- connect to the divergence point of the patched program
        gr1 <- withTracing @"node" (GraphNode currBlockO) $ 
          widenAlongEdge scope bundleO (GraphNode currBlock) dom gr0 (GraphNode currBlockO)
        return (gr1, mchoice)
    _ -> do
      let divergeNode = GraphNode currBlock
      let pg = gr0
      let msg = "Control flow desynchronization found at: " ++ show divergeNode
      a <- case mchoice of
        Just DeferDecision -> return DeferDecision
        Just ChooseSyncPoint -> return DeferDecision
        _ -> choose @"()" msg $ \choice -> do
          choice "Choose synchronization points" () $ return ChooseSyncPoint
          choice "Assert divergence is infeasible" () $ return (IsInfeasible ConditionAsserted)
          choice "Assume divergence is infeasible" () $ return (IsInfeasible ConditionAssumed)
          choice "Remove divergence in equivalence condition" () $ return (IsInfeasible ConditionEquiv)
          choice "Defer decision" () $ return DeferDecision


      case a of
        ChooseSyncPoint -> do
          pg1 <- chooseSyncPoint divergeNode pg
          pg2 <- updateCombinedSyncPoint divergeNode pg1
          handleDivergingPaths scope currBlock (Just a) dom pg2
        IsInfeasible condK -> do
          gr2 <- pruneCurrentBranch scope (divergeNode, GraphNode currBlockO) condK pg
          gr3 <- pruneCurrentBranch scope (divergeNode, GraphNode currBlockP) condK gr2
          return (gr3, Just a)
        DeferDecision -> do
          -- add this back to the work list at a low priority
          -- this allows, for example, the analysis to determine
          -- that this is unreachable (potentially after refinements) and therefore
          -- doesn't need synchronization
          Just pg1 <- return $ addToWorkList divergeNode (priority PriorityDeferred) pg
          return $ (pg1, Just a)

data DesyncChoice = ChooseSyncPoint | IsInfeasible ConditionKind | DeferDecision
  deriving Eq

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
  case bothTerminalStub stubPair of
    True -> return gr0
    False -> do
      PA.SomeValidArch archData <- asks envValidArch
      ovPair <- PPa.forBins $ \bin -> do
        blk <- PPa.get bin pPair
        Const stub <- PPa.get bin stubPair
        Const <$> getStubOverrideOne blk stub
      ov <- mergeStubOverrides archData stubPair ovPair
      wsolver <- getWrappedSolver

      outputs <- IO.withRunInIO $ \runInIO ->
        PA.withStubOverride sym wsolver ov $ \f -> runInIO $ PPa.forBins $ \bin -> do
          output <- PPa.get bin $ PS.simOut bundle
          nextSt <- liftIO $ f (PS.simOutState output)
          return $ output { PS.simOutState = nextSt }
      let bundle' = bundle { PS.simOut = outputs }
      gr1 <- checkObservables currBlock bundle' d gr0
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
 do let fPair = TF.fmapF PB.blockFunctionEntry (nodeBlocks currBlock)
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
    simIn_pair = TF.fmapF (\(TupleF2 x _) -> x) results_pair
    simOut_pair = TF.fmapF (\(TupleF2 _ x) -> x) results_pair
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