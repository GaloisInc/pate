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

module Pate.Verification.PairGraph.Node (
    GraphNode(..)
  , NodeEntry
  , NodeReturn
  , CallingContext
  , pattern GraphNodeEntry
  , pattern GraphNodeReturn
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
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>), Doc )

import qualified Data.Parameterized.TraversableF as TF

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.PatchPair as PPa
import           Pate.TraceTree
import qualified Pate.Binary as PB

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
        Just p -> ["Diverged at:", pretty p]
        Nothing -> []
    in sep (((zipWith (<+>) ( "via:" : repeat "<-") bs)) ++ divP)

getDivergePoint :: GraphNode arch -> Maybe (GraphNode arch)
getDivergePoint nd = case nd of
  GraphNode (NodeEntry ctx _) -> divergePoint ctx
  ReturnNode (NodeReturn ctx _) -> divergePoint ctx

rootEntry :: PB.BlockPair arch -> NodeEntry arch
rootEntry pPair = NodeEntry (CallingContext [] Nothing) pPair

rootReturn :: PB.FunPair arch -> NodeReturn arch
rootReturn pPair = NodeReturn (CallingContext [] Nothing) pPair

addContext :: PB.BlockPair arch -> NodeEntry arch -> NodeEntry arch
addContext newCtx (NodeEntry (CallingContext ctx d) blks) = NodeEntry (CallingContext (newCtx:ctx) d) blks

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (graphNodeContext node) pPair

mkNodeEntry' :: GraphNode arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry' (GraphNode node) pPair = NodeEntry (graphNodeContext node) pPair
mkNodeEntry' (ReturnNode node) pPair = NodeEntry (returnNodeContext node) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (graphNodeContext node) fPair

-- | Project the given 'NodeReturn' into a singleton node for the given binary
asSingleReturn :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> NodeReturn arch -> m (NodeReturn arch)
asSingleReturn bin node@(NodeReturn ctx fPair) = do
  fPair' <- PPa.asSingleton bin fPair
  return $ NodeReturn (ctx {divergePoint = Just (ReturnNode node)}) fPair'

-- | Project the given 'NodeEntry' into a singleton node for the given binary
asSingleNode:: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> NodeEntry arch -> m (NodeEntry arch)
asSingleNode bin node@(NodeEntry ctx bPair) = do
  fPair' <- PPa.asSingleton bin bPair
  return $ NodeEntry (ctx {divergePoint = Just (GraphNode node)}) fPair'

asSingleGraphNode :: PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode arch -> m (GraphNode arch)
asSingleGraphNode bin node = case node of
  GraphNode ne -> GraphNode <$> asSingleNode bin ne
  ReturnNode nr -> ReturnNode <$> asSingleReturn bin nr  

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
  PA.ValidArch arch => GraphNode arch -> Doc a
tracePrettyNode nd = case nd of
  GraphNode e -> case functionEntryOf e == e of
    True -> "Function Entry" <+> pretty e
    False -> pretty e
  ReturnNode ret -> "Return" <+> pretty ret

instance forall sym arch. PA.ValidArch arch => IsTraceNode '(sym, arch) "node" where
  type TraceNodeType '(sym, arch) "node" = GraphNode arch
  prettyNode () nd = tracePrettyNode nd
  nodeTags = mkTags @'(sym,arch) @"node" [Simplified, Summary]

instance forall sym arch. PA.ValidArch arch => IsTraceNode '(sym, arch) "entrynode" where
  type TraceNodeType '(sym, arch) "entrynode" = NodeEntry arch
  prettyNode () = pretty
  nodeTags = mkTags @'(sym,arch) @"entrynode" [Simplified, Summary]
