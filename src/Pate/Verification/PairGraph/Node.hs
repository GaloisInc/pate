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

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Verification.PairGraph.Node (
    GraphNode(..)
  , NodeEntry
  , NodeReturn
  , CallingContext
  , pattern GraphNodeEntry
  , pattern GraphNodeReturn
  , nodeContext
  , divergePoint
  , graphNodeBlocks
  , mkNodeEntry
  , mkNodeEntry'
  , addContext
  , mkNodeReturn
  , rootEntry
  , rootReturn
  , nodeBlocks
  , nodeFuns
  , returnToEntry
  , functionEntryOf
  , returnOfEntry
  , asSingleReturn
  , asSingleNode
  , asSingleGraphNode
  , splitGraphNode
  , getDivergePoint
  , eqUptoDivergePoint
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

-- A frozen binary 
data NodeEntry arch =
  NodeEntry { graphNodeContext :: CallingContext arch, nodeBlocks :: PB.BlockPair arch }
  deriving (Eq, Ord)

data NodeReturn arch =
  NodeReturn { returnNodeContext :: CallingContext arch, nodeFuns :: PB.FunPair arch }
  deriving (Eq, Ord)

graphNodeBlocks :: GraphNode arch -> PB.BlockPair arch
graphNodeBlocks (GraphNode ne) = nodeBlocks ne
graphNodeBlocks (ReturnNode ret) = TF.fmapF PB.functionEntryToConcreteBlock (nodeFuns ret)

nodeContext :: GraphNode arch -> CallingContext arch
nodeContext (GraphNode nd) = graphNodeContext nd
nodeContext (ReturnNode ret) = returnNodeContext ret

pattern GraphNodeEntry :: PB.BlockPair arch -> GraphNode arch
pattern GraphNodeEntry blks <- (GraphNode (NodeEntry _ blks))

pattern GraphNodeReturn :: PB.FunPair arch -> GraphNode arch
pattern GraphNodeReturn blks <- (ReturnNode (NodeReturn _ blks))

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

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (graphNodeContext node) pPair

mkNodeEntry' :: GraphNode arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry' (GraphNode node) pPair = NodeEntry (graphNodeContext node) pPair
mkNodeEntry' (ReturnNode node) pPair = NodeEntry (returnNodeContext node) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (graphNodeContext node) fPair

-- | Project the given 'NodeReturn' into a singleton node for the given binary
asSingleReturn :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode arch -> NodeReturn arch -> m (NodeReturn arch)
asSingleReturn bin divergedAt (NodeReturn ctx fPair) = do
  fPair' <- PPa.asSingleton bin fPair
  return $ NodeReturn (ctx {divergePoint = Just divergedAt}) fPair'

-- | Project the given 'NodeEntry' into a singleton node for the given binary
asSingleNode:: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> NodeEntry arch -> m (NodeEntry arch)
asSingleNode bin node@(NodeEntry ctx bPair) = do
  fPair' <- PPa.asSingleton bin bPair
  return $ NodeEntry (ctx {divergePoint = Just (GraphNode node)}) fPair'

asSingleGraphNode :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode arch -> m (GraphNode arch)
asSingleGraphNode bin node = case node of
  GraphNode ne -> GraphNode <$> asSingleNode bin ne
  ReturnNode nr -> ReturnNode <$> asSingleReturn bin node nr  

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
  nodes <- PPa.forBinsC $ \bin -> asSingleGraphNode bin nd
  nodeO <- PPa.getC PB.OriginalRepr nodes
  nodeP <- PPa.getC PB.PatchedRepr nodes
  return (nodeO, nodeP)

-- | Get the node corresponding to the entry point for the function
returnToEntry :: NodeReturn arch -> NodeEntry arch
returnToEntry (NodeReturn ctx fns) = NodeEntry ctx (TF.fmapF PB.functionEntryToConcreteBlock fns)

-- | Get the return node that this entry would return to
returnOfEntry :: NodeEntry arch -> NodeReturn arch
returnOfEntry (NodeEntry ctx blks) = NodeReturn ctx (TF.fmapF PB.blockFunctionEntry blks)

-- | For an intermediate entry point in a function, find the entry point
--   corresponding to the function start
functionEntryOf :: NodeEntry arch -> NodeEntry arch
functionEntryOf (NodeEntry ctx blks) = NodeEntry ctx (TF.fmapF (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) blks)

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
  jsonNode _ = nodeToJSON @'(sym,arch) @"node"

instance forall sym arch. PA.ValidArch arch => IsTraceNode '(sym, arch) "entrynode" where
  type TraceNodeType '(sym, arch) "entrynode" = NodeEntry arch
  prettyNode () = pretty
  nodeTags = mkTags @'(sym,arch) @"entrynode" [Simplified, Summary]
  jsonNode _ = nodeToJSON @'(sym,arch) @"entrynode"
