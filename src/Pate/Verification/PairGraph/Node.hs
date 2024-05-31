{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Pate.Verification.PairGraph.Node (
    GraphNode(..)
  , NodeEntry
  , NodeReturn
  , CallingContext
  , pattern GraphNodeEntry
  , pattern GraphNodeReturn
  , nodeContext
  , graphNodeContext
  , divergePoint
  , graphNodeBlocks
  , mkNodeEntry
  , mkNodeEntry'
  , mkSingleNodeEntry
  , addContext
  , mkNodeReturn
  , rootEntry
  , rootReturn
  , nodeBlocks
  , nodeFuns
  , returnToEntry
  , functionEntryOf
  , returnOfEntry
  , toSingleReturn
  , toSingleNode
  , toSingleGraphNode
  , isSingleNode
  , isSingleNodeEntry
  , isSingleReturn
  , splitGraphNode
  , getDivergePoint
  , eqUptoDivergePoint
  , mkMergedNodeEntry
  , mkMergedNodeReturn
  , SingleNodeEntry
  , singleEntryBin
  , singleNodeDivergePoint
  , asSingleNodeEntry
  , singleToNodeEntry
  , singleNodeBlock
  , combineSingleEntries
  , singleNodeDivergence
  , toSingleNodeEntry
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>), Doc )
import qualified Data.Aeson as JSON
import qualified Compat.Aeson as HMS
import qualified Data.Parameterized.TraversableF as TF

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.PatchPair as PPa
import           Pate.TraceTree
import qualified Pate.Binary as PB
import qualified Prettyprinter as PP
import Data.Parameterized (Some(..), Pair (..))
import qualified What4.JSON as W4S
import Control.Monad (guard)
import Data.Parameterized.Classes
import Pate.Panic

-- | Nodes in the program graph consist either of a pair of
--   program points (GraphNode), or a synthetic node representing
--   the return point of a function (ReturnNode).  In terms of
--   the dataflow analysis, basic blocks that return propagate
--   their abstract domains directly to the corresponding
--   ReturnNode for the current function under analysis.
--   When a ReturnNode is visited in the analysis, its abstract
--   domain is propagated to all the potential return sites for
--   that function, which are recorded separately in the
--   "return vectors" map.
data GraphNode arch
  = GraphNode (NodeEntry arch)
  | ReturnNode (NodeReturn arch)
 deriving (Eq, Ord)

instance PA.ValidArch arch => JSON.ToJSON (GraphNode arch) where
  toJSON = \case
    GraphNode nd -> JSON.object [ ("graph_node_type", "entry"), "entry_body" JSON..= nd]
    ReturnNode nd -> JSON.object [ ("graph_node_type", "return"), "return_body" JSON..= nd]

instance PA.ValidArch arch => W4S.W4Serializable sym (GraphNode arch) where
  w4Serialize r = return $ JSON.toJSON r

instance PA.ValidArch arch => W4S.W4Serializable sym (NodeEntry arch) where
  w4Serialize r = return $ JSON.toJSON r

data NodeContent arch e = 
  NodeContent { nodeContentCtx :: CallingContext arch, nodeContent :: e }
  deriving (Eq, Ord)

type NodeEntry arch = NodeContent arch (PB.BlockPair arch)

pattern NodeEntry :: CallingContext arch -> PB.BlockPair arch -> NodeEntry arch
pattern NodeEntry ctx bp = NodeContent ctx bp
{-# COMPLETE NodeEntry #-}


nodeBlocks :: NodeEntry arch -> PB.BlockPair arch
nodeBlocks = nodeContent

graphNodeContext :: NodeEntry arch -> CallingContext arch
graphNodeContext = nodeContentCtx

type NodeReturn arch = NodeContent arch (PB.FunPair arch)

nodeFuns :: NodeReturn arch -> PB.FunPair arch
nodeFuns = nodeContent

returnNodeContext :: NodeReturn arch -> CallingContext arch
returnNodeContext = nodeContentCtx

pattern NodeReturn :: CallingContext arch -> PB.FunPair arch -> NodeReturn arch
pattern NodeReturn ctx bp = NodeContent ctx bp
{-# COMPLETE NodeReturn #-}

graphNodeBlocks :: GraphNode arch -> PB.BlockPair arch
graphNodeBlocks (GraphNode ne) = nodeBlocks ne
graphNodeBlocks (ReturnNode ret) = TF.fmapF PB.functionEntryToConcreteBlock (nodeFuns ret)

nodeContext :: GraphNode arch -> CallingContext arch
nodeContext (GraphNode nd) = nodeContentCtx nd
nodeContext (ReturnNode ret) = nodeContentCtx ret

pattern GraphNodeEntry :: PB.BlockPair arch -> GraphNode arch
pattern GraphNodeEntry blks <- (GraphNode (NodeContent _ blks))

pattern GraphNodeReturn :: PB.FunPair arch -> GraphNode arch
pattern GraphNodeReturn blks <- (ReturnNode (NodeContent _ blks))

{-# COMPLETE GraphNodeEntry, GraphNodeReturn #-}

-- | Additional context used to distinguish function calls
--   "Freezing" one binary in a node indicates that it should not continue
--   execution until the other binary has returned
data CallingContext arch = CallingContext { _ctxAncestors :: [PB.BlockPair arch], divergePoint :: Maybe (GraphNode arch) }
  deriving (Eq, Ord)


instance PA.ValidArch arch => Pretty (CallingContext arch) where
  pretty (CallingContext bps mdivisionPoint) =
    let
      bs = [ pretty bp | bp <- bps ]
      divP = case mdivisionPoint of
        Just _p -> [] -- ["Diverged at:", pretty p] -- too noisy
        Nothing -> []
    in sep (((zipWith (<+>) ( "via:" : repeat "<-") bs)) ++ divP)

instance PA.ValidArch arch => JSON.ToJSON (CallingContext arch) where
  toJSON (CallingContext bps mdivisionPoint) = JSON.object [ "ancestors" JSON..= bps, "divergedAt" JSON..= mdivisionPoint]

getDivergePoint :: GraphNode arch -> Maybe (GraphNode arch)
getDivergePoint nd = case nd of
  GraphNode (NodeEntry ctx _) -> divergePoint ctx
  ReturnNode (NodeReturn ctx _) -> divergePoint ctx

rootEntry :: PB.BlockPair arch -> NodeEntry arch
rootEntry pPair = NodeEntry (CallingContext [] Nothing) pPair

rootReturn :: PB.FunPair arch -> NodeReturn arch
rootReturn pPair = NodeReturn (CallingContext [] Nothing) pPair

addContext :: PB.BlockPair arch -> NodeEntry arch -> NodeEntry arch
addContext newCtx ne@(NodeEntry (CallingContext ctx d) blks) = 
  case elem newCtx ctx of
    -- avoid recursive loops
    True -> ne
    False -> NodeEntry (CallingContext (newCtx:ctx) d) blks

-- Strip diverge points from two-sided nodes. This is used so that
-- merged nodes (which are two-sided) can meaningfully retain their
-- diverge point, but it will be stripped on any subsequent nodes.
mkNextContext :: PPa.PatchPair a -> CallingContext arch -> CallingContext arch
mkNextContext (PPa.PatchPair{}) cctx = dropDivergePoint cctx
mkNextContext _ cctx = cctx

dropDivergePoint :: CallingContext arch -> CallingContext arch
dropDivergePoint  (CallingContext cctx _) = CallingContext cctx Nothing

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (mkNextContext pPair (graphNodeContext node)) pPair

mkNodeEntry' :: GraphNode arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry' (GraphNode ne) pPair = mkNodeEntry ne pPair
mkNodeEntry' (ReturnNode node) pPair = NodeEntry (mkNextContext pPair (returnNodeContext node)) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (mkNextContext fPair (graphNodeContext node)) fPair

mkMergedNodeEntry :: 
  GraphNode arch -> 
  PB.ConcreteBlock arch PB.Original ->
  PB.ConcreteBlock arch PB.Patched -> 
  NodeEntry arch
mkMergedNodeEntry nd blkO blkP = NodeEntry (CallingContext cctx (Just nd)) (PPa.PatchPair blkO blkP)
  where
    CallingContext cctx _ = nodeContext nd

mkMergedNodeReturn :: 
  GraphNode arch -> 
  PB.FunctionEntry arch PB.Original ->
  PB.FunctionEntry arch PB.Patched -> 
  NodeReturn arch
mkMergedNodeReturn nd fnO fnP = NodeReturn (CallingContext cctx (Just nd)) (PPa.PatchPair fnO fnP)
  where
    CallingContext cctx _ = nodeContext nd


-- | Project the given 'NodeReturn' into a singleton node for the given binary
toSingleReturn :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode arch -> NodeReturn arch -> m (NodeReturn arch)
toSingleReturn bin divergedAt (NodeReturn ctx fPair) = do
  fPair' <- PPa.toSingleton bin fPair
  return $ NodeReturn (ctx {divergePoint = Just divergedAt}) fPair'

-- | Project the given 'NodeEntry' into a singleton node for the given binary
toSingleNode:: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> NodeEntry arch -> m (NodeEntry arch)
toSingleNode bin node@(NodeEntry ctx bPair) = do
  fPair' <- PPa.toSingleton bin bPair
  return $ NodeEntry (ctx {divergePoint = Just (GraphNode node)}) fPair'

toSingleGraphNode :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode arch -> m (GraphNode arch)
toSingleGraphNode bin node = case node of
  GraphNode ne -> GraphNode <$> toSingleNode bin ne
  ReturnNode nr -> ReturnNode <$> toSingleReturn bin node nr  

isSingleNodeEntry :: 
  PPa.PatchPairM m => 
  NodeEntry arch -> 
  m (Some PB.WhichBinaryRepr)
isSingleNodeEntry (NodeEntry _ bPair) = do
  Pair bin _ <- PPa.asSingleton bPair
  return $ Some bin

isSingleReturn ::
  PPa.PatchPairM m => 
  NodeReturn arch -> 
  m (Some PB.WhichBinaryRepr)
isSingleReturn (NodeReturn _ bPair) = do
  Pair bin _ <- PPa.asSingleton bPair
  return $ Some bin

-- | If the given 'GraphNode' is a singleton, return the corresponding
--   'PB.WhichBinaryRepr'
isSingleNode ::
  PPa.PatchPairM m => 
  GraphNode arch -> 
  m (Some PB.WhichBinaryRepr)
isSingleNode (GraphNode nd) = isSingleNodeEntry nd
isSingleNode (ReturnNode nd) = isSingleReturn nd

-- | Relaxed node equality that ignores differences in divergence points
eqUptoDivergePoint ::
  GraphNode arch ->
  GraphNode arch ->
  Bool
eqUptoDivergePoint (GraphNode (NodeEntry ctx1 blks1)) (GraphNode (NodeEntry ctx2 blks2))
  | (ctx1{divergePoint = Nothing} == ctx2{divergePoint = Nothing})
  , blks1 == blks2
  = True
eqUptoDivergePoint (ReturnNode (NodeReturn ctx1 blks1)) (ReturnNode (NodeReturn ctx2 blks2))
  | (ctx1{divergePoint = Nothing} == ctx2{divergePoint = Nothing})
  , blks1 == blks2
  = True
eqUptoDivergePoint _ _ = False

-- | Split a graph node into two single-sided nodes (original, patched)
--   The input node is marked as the diverge point in the two resulting nodes.
splitGraphNode :: PPa.PatchPairM m => GraphNode arch -> m (GraphNode arch, GraphNode arch)
splitGraphNode nd = do
  nodes <- PPa.forBinsC $ \bin -> toSingleGraphNode bin nd
  nodeO <- PPa.getC PB.OriginalRepr nodes
  nodeP <- PPa.getC PB.PatchedRepr nodes
  return (nodeO, nodeP)

-- | Get the node corresponding to the entry point for the function
returnToEntry :: NodeReturn arch -> NodeEntry arch
returnToEntry (NodeReturn ctx fns) = NodeEntry (mkNextContext fns ctx) (TF.fmapF PB.functionEntryToConcreteBlock fns)

-- | Get the return node that this entry would return to
returnOfEntry :: NodeEntry arch -> NodeReturn arch
returnOfEntry (NodeEntry ctx blks) = NodeReturn (mkNextContext blks ctx) (TF.fmapF PB.blockFunctionEntry blks)

-- | For an intermediate entry point in a function, find the entry point
--   corresponding to the function start
functionEntryOf :: NodeEntry arch -> NodeEntry arch
functionEntryOf (NodeEntry ctx blks) = NodeEntry (mkNextContext blks ctx) (TF.fmapF (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) blks)

instance PA.ValidArch arch => Show (CallingContext arch) where
  show c = show (pretty c)

instance PA.ValidArch arch => Show (NodeEntry arch) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (NodeEntry arch) where
  pretty e = case functionEntryOf e == e of
    True -> case graphNodeContext e of
      CallingContext [] _ -> pretty (nodeBlocks e)
      _ -> pretty (nodeBlocks e) <+> "[" <+> pretty (graphNodeContext e) <+> "]"
    False -> PPa.ppPatchPair' PB.ppBlockAddr (nodeBlocks e)
      <+> "[" <+> pretty (graphNodeContext (addContext (nodeBlocks (functionEntryOf e)) e)) <+> "]"

instance PA.ValidArch arch => Pretty (NodeReturn arch) where
  pretty e = case returnNodeContext e of
    CallingContext [] _ -> pretty (nodeFuns e)
    _ -> pretty (nodeFuns e) <+> "[" <+> pretty (returnNodeContext e) <+> "]"

instance PA.ValidArch arch => Show (NodeReturn arch) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (GraphNode arch) where
  pretty (GraphNode e) = "GraphNode" <+> pretty e
  pretty (ReturnNode e) = "ReturnNode" <+> pretty e

instance PA.ValidArch arch => Show (GraphNode arch) where
  show e = show (pretty e)

tracePrettyNode ::
  PA.ValidArch arch => GraphNode arch -> String -> Doc a
tracePrettyNode nd msg = case nd of
  GraphNode e -> case (functionEntryOf e == e,msg) of
    (True,"") -> "Function Entry" <+> pretty e
    (True,_) -> "Function Entry" <+> pretty e <+> PP.parens (pretty msg)
    (False,"") -> pretty e
    (False,_) -> pretty e <+> PP.parens (pretty msg)
  ReturnNode ret -> case msg of
    "" -> "Return" <+> pretty ret
    _ -> "Return" <+> pretty ret <+> PP.parens (pretty msg)

instance PA.ValidArch arch => JSON.ToJSON (NodeEntry arch) where
  toJSON e = JSON.object 
    [ "type" JSON..= entryType
    , "context" JSON..= graphNodeContext e 
    , "blocks" JSON..= nodeBlocks e
    ]
    where
      entryType :: String
      entryType = case (functionEntryOf e == e) of
          True ->  "function_entry"
          False -> "function_body"
  
instance PA.ValidArch arch => JSON.ToJSON (NodeReturn arch) where
  toJSON e = JSON.object 
    [ "context" JSON..= returnNodeContext e
    , "functions" JSON..= nodeFuns e 
    ]
  
  -- HMS.fromList [ ("data", JSON.Object content) ]





instance forall sym arch. PA.ValidArch arch => IsTraceNode '(sym, arch) "node" where
  type TraceNodeType '(sym, arch) "node" = GraphNode arch
  type TraceNodeLabel "node" = String
  prettyNode msg nd = tracePrettyNode nd msg
  nodeTags = mkTags @'(sym,arch) @"node" [Simplified, Summary]  
    ++ [("debug", \lbl v -> tracePrettyNode v lbl <+> case divergePoint (nodeContext v) of
         Just dp -> "diverged: (" <> tracePrettyNode dp "" <> ")"
         Nothing -> ""
         )
       ]
  jsonNode _ = nodeToJSON @'(sym,arch) @"node"

instance forall sym arch. PA.ValidArch arch => IsTraceNode '(sym, arch) "entrynode" where
  type TraceNodeType '(sym, arch) "entrynode" = NodeEntry arch
  prettyNode () = pretty
  nodeTags = mkTags @'(sym,arch) @"entrynode" [Simplified, Summary]
  jsonNode _ = nodeToJSON @'(sym,arch) @"entrynode"

-- | Equivalent to a 'NodeEntry' but necessarily a single-sided node.
--   Converting a 'SingleNodeEntry' to a 'NodeEntry' is always defined,
--   while converting a 'NodeEntry' to a 'SingleNodeEntry' is partial.
data SingleNodeEntry arch bin = 
  SingleNodeEntry 
    { singleEntryBin :: PB.WhichBinaryRepr bin
    , _singleEntry :: NodeContent arch (PB.ConcreteBlock arch bin)
    }

mkSingleNodeEntry :: NodeEntry arch -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
mkSingleNodeEntry node blk = SingleNodeEntry (PB.blockBinRepr blk) (NodeContent (graphNodeContext node) blk)

instance TestEquality (SingleNodeEntry arch) where
  testEquality se1 se2 | EQF <- compareF se1 se2 = Just Refl
  testEquality _ _ = Nothing

instance Eq (SingleNodeEntry arch bin) where
  se1 == se2 = compare se1 se2 == EQ

instance Ord (SingleNodeEntry arch bin) where
  compare (SingleNodeEntry _ se1) (SingleNodeEntry _ se2) = compare se1 se2

instance OrdF (SingleNodeEntry arch) where
  compareF (SingleNodeEntry bin1 se1) (SingleNodeEntry bin2 se2) =
    lexCompareF bin1 bin2 $ fromOrdering (compare se1 se2)

instance PA.ValidArch arch => Show (SingleNodeEntry arch bin) where
  show e = show (singleToNodeEntry e)

singleNodeDivergePoint :: SingleNodeEntry arch bin -> GraphNode arch
singleNodeDivergePoint (SingleNodeEntry _ (NodeContent cctx _)) = case divergePoint cctx of
  Just dp -> dp
  Nothing -> panic Verifier "singleNodeDivergePoint" ["missing diverge point for SingleNodeEntry"]

asSingleNodeEntry :: PPa.PatchPairM m => NodeEntry arch -> m (Some (SingleNodeEntry arch))
asSingleNodeEntry (NodeEntry cctx bPair) = do
  Pair bin blk <- PPa.asSingleton bPair
  case divergePoint cctx of
    Just{} -> return $ Some (SingleNodeEntry bin (NodeContent cctx blk))
    Nothing -> PPa.throwPairErr

singleNodeBlock :: SingleNodeEntry arch bin -> PB.ConcreteBlock arch bin
singleNodeBlock (SingleNodeEntry _ (NodeContent _ blk)) = blk

-- | Returns a 'SingleNodeEntry' for a given 'NodeEntry' if it has an entry
--   for the given 'bin'.
--   Note that, in contrast to
--   'asSingleNodeEntry' this does not require the given 'NodeEntry' to be a singleton
toSingleNodeEntry :: 
  PPa.PatchPairM m => 
  PB.WhichBinaryRepr bin -> 
  NodeEntry arch -> 
  m (SingleNodeEntry arch bin)
toSingleNodeEntry bin ne = do
  case toSingleNode bin ne of
    Just (NodeEntry cctx bPair) -> do
      blk <- PPa.get bin bPair
      return $ SingleNodeEntry bin (NodeContent cctx blk)
    _ -> PPa.throwPairErr

singleToNodeEntry :: SingleNodeEntry arch bin -> NodeEntry arch
singleToNodeEntry (SingleNodeEntry bin (NodeContent cctx v)) = 
  NodeEntry cctx (PPa.PatchPairSingle bin v)

singleNodeDivergence :: SingleNodeEntry arch bin -> GraphNode arch
singleNodeDivergence (SingleNodeEntry _ (NodeContent cctx _)) = case divergePoint cctx of
  Just dp -> dp
  Nothing -> panic Verifier "singleNodeDivergence" ["Unexpected missing divergence point"]

combineSingleEntries' :: 
  SingleNodeEntry arch PB.Original -> 
  SingleNodeEntry arch PB.Patched ->
  Maybe (NodeEntry arch)
combineSingleEntries' (SingleNodeEntry _ eO) (SingleNodeEntry _ eP) = do
  GraphNode divergeO <- divergePoint $ nodeContentCtx eO
  GraphNode divergeP <- divergePoint $ nodeContentCtx eP
  guard $ divergeO == divergeP
  let blksO = nodeContent eO
  let blksP = nodeContent eP
  return $ mkNodeEntry divergeO (PPa.PatchPair blksO blksP)

-- | Create a combined two-sided 'NodeEntry' based on
--   a pair of single-sided entries. The given entries
--   must have the same diverge point (returns 'Nothing' otherwise),
--   and the calling context of the resulting node is inherited from
--   that point (i.e. any additional context accumulated during
--   the either single-sided analysis is discarded)
combineSingleEntries :: 
  SingleNodeEntry arch bin -> 
  SingleNodeEntry arch (PB.OtherBinary bin) ->
  Maybe (NodeEntry arch)
combineSingleEntries sne1 sne2 = case singleEntryBin sne1 of
  PB.OriginalRepr -> combineSingleEntries' sne1 sne2
  PB.PatchedRepr -> combineSingleEntries' sne2 sne1