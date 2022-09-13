{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE OverloadedStrings #-}
module Pate.Verification.PairGraph.Node (
    GraphNode(..)
  , NodeEntry
  , NodeReturn
  , CallingContext
  , graphNodeCases
  , mkNodeEntry
  , addContext
  , mkNodeReturn
  , rootEntry
  , nodeBlocks
  , nodeFuns
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>) )

import qualified Pate.Arch as PA
import qualified Pate.PatchPair as PPa
import           Pate.TraceTree

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

data NodeEntry arch =
  NodeEntry { graphNodeContext :: CallingContext arch, nodeBlocks :: PPa.BlockPair arch }
  deriving (Eq, Ord)

data NodeReturn arch =
  NodeReturn { returnNodeContext :: CallingContext arch, nodeFuns :: PPa.FunPair arch }
  deriving (Eq, Ord)

graphNodeCases :: GraphNode arch -> Either (PPa.BlockPair arch) (PPa.FunPair arch)
graphNodeCases (GraphNode (NodeEntry _ blks)) = Left blks
graphNodeCases (ReturnNode (NodeReturn _ funs)) = Right funs

-- | Additional context used to distinguish function calls
newtype CallingContext arch = CallingContext [PPa.BlockPair arch]
  deriving (Eq, Ord, Semigroup, Monoid)

instance PA.ValidArch arch => Pretty (CallingContext arch) where
  pretty (CallingContext bps) =
    let bs = [ pretty bp | bp <- bps ]
    in sep (zipWith (<+>) ("[" : repeat "->") bs) <+> "]"


rootEntry :: PPa.BlockPair arch -> NodeEntry arch
rootEntry pPair = NodeEntry mempty pPair

addContext :: PPa.BlockPair arch -> NodeEntry arch -> NodeEntry arch
addContext newCtx (NodeEntry (CallingContext ctx) blks) = NodeEntry (CallingContext (newCtx:ctx)) blks

mkNodeEntry :: NodeEntry arch -> PPa.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (graphNodeContext node) pPair

mkNodeReturn :: NodeEntry arch -> PPa.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (graphNodeContext node) fPair

instance PA.ValidArch arch => Show (CallingContext arch) where
  show c = show (pretty c)

instance PA.ValidArch arch => Show (NodeEntry arch) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (NodeEntry arch) where
  pretty e = case graphNodeContext e of
    CallingContext [] -> pretty (nodeBlocks e)
    _ -> pretty (graphNodeContext e) <+> ":" <+> pretty (nodeBlocks e)

instance PA.ValidArch arch => Pretty (NodeReturn arch) where
  pretty e = case returnNodeContext e of
    CallingContext [] -> pretty (nodeFuns e)
    _ -> pretty (returnNodeContext e) <+> ":" <+> pretty (nodeFuns e)

instance PA.ValidArch arch => Show (NodeReturn arch) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (GraphNode arch) where
  pretty (GraphNode e) = "GraphNode" <+> pretty e
  pretty (ReturnNode e) = "ReturnNode" <+> pretty e

instance PA.ValidArch arch => Show (GraphNode arch) where
  show e = show (pretty e)

instance PA.ValidArch arch => IsTraceNode '(sym, arch) "node" where
  type TraceNodeType '(sym, arch) "node" = GraphNode arch
  prettyNode () = pretty
