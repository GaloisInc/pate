{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

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
  , returnToEntry
  , functionEntryOf
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>) )

import qualified Data.Parameterized.TraversableF as TF

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
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
  NodeEntry { graphNodeContext :: CallingContext arch, nodeBlocks :: PB.BlockPair arch }
  deriving (Eq, Ord)

data NodeReturn arch =
  NodeReturn { returnNodeContext :: CallingContext arch, nodeFuns :: PB.FunPair arch }
  deriving (Eq, Ord)

graphNodeCases :: GraphNode arch -> Either (PB.BlockPair arch) (PB.FunPair arch)
graphNodeCases (GraphNode (NodeEntry _ blks)) = Left blks
graphNodeCases (ReturnNode (NodeReturn _ funs)) = Right funs

-- | Additional context used to distinguish function calls
newtype CallingContext arch = CallingContext [PB.BlockPair arch]
  deriving (Eq, Ord, Semigroup, Monoid)

instance PA.ValidArch arch => Pretty (CallingContext arch) where
  pretty (CallingContext bps) =
    let bs = reverse $ [ pretty bp | bp <- bps ]
    in sep (zipWith (<+>) ("[" : repeat "->") bs) <+> "]"


rootEntry :: PB.BlockPair arch -> NodeEntry arch
rootEntry pPair = NodeEntry mempty pPair

addContext :: PB.BlockPair arch -> NodeEntry arch -> NodeEntry arch
addContext newCtx (NodeEntry (CallingContext ctx) blks) = NodeEntry (CallingContext (newCtx:ctx)) blks

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (graphNodeContext node) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (graphNodeContext node) fPair

-- | Get the node corresponding to the entry point for the function
returnToEntry :: NodeReturn arch -> NodeEntry arch
returnToEntry (NodeReturn ctx fns) = NodeEntry ctx (TF.fmapF PB.functionEntryToConcreteBlock fns)

-- | For an intermediate entry point in a function, find the entry point
--   corresponding to the function start
functionEntryOf :: NodeEntry arch -> NodeEntry arch
functionEntryOf (NodeEntry ctx blks) = NodeEntry ctx (TF.fmapF (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) blks)

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

instance PA.ValidArch arch => IsTraceNode '(sym, arch) "entrynode" where
  type TraceNodeType '(sym, arch) "entrynode" = NodeEntry arch
  prettyNode () = pretty
