{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Interactive.Render.SliceGraph (
  renderSliceGraph
  ) where

import qualified Data.Aeson as JSON
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HMS
import qualified Data.Map.Strict as Map
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import qualified Data.Vector as DV
import           Graphics.UI.Threepenny ( (#) )
import qualified Graphics.UI.Threepenny as TP
import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MDS

import qualified Pate.Arch as PA
import qualified Pate.Event as PE

addrIdent :: (PA.ValidArch arch) => proxy arch -> MC.ArchSegmentOff arch -> T.Text
addrIdent _ = T.pack . show

-- | Convert a 'MD.ParsedBlock' to the format described in the documentation of
-- 'renderSliceGraph' (adding it to the accumulated map)
blockNode
  :: forall arch ids
   . (PA.ValidArch arch)
  => Map.Map (MC.ArchSegmentOff arch) JSON.Value
  -> MD.ParsedBlock arch ids
  -> Map.Map (MC.ArchSegmentOff arch) JSON.Value
blockNode m pb =
  Map.insert (MD.pblockAddr pb) (JSON.Object node) m
  where
    node = HMS.fromList [ (T.pack "data", JSON.Object content)
                        ]
    content = HMS.fromList [ (T.pack "id", JSON.String (addrIdent (Proxy @arch) (MD.pblockAddr pb)))
                           , (T.pack "text", JSON.String (T.pack (show (PP.pretty pb))))
                           ]

blockEdges
  :: forall arch ids v
   . (PA.ValidArch arch)
  => Map.Map (MC.ArchSegmentOff arch) v
  -> [[JSON.Value]]
  -> MD.ParsedBlock arch ids
  -> [[JSON.Value]]
blockEdges nodes edges pb =
  [ toEdge (MD.pblockAddr pb) controlFlowSuccessor
  | controlFlowSuccessor <- MDS.parsedTermSucc (MD.pblockTermStmt pb)
  , Map.member controlFlowSuccessor nodes
  ] : edges
  where
    toEdge src dst =
      let srcLabel = addrIdent (Proxy @arch) src
          tgtLabel = addrIdent (Proxy @arch) dst
          edgeLabel = srcLabel <> tgtLabel
          content = HMS.fromList [ (T.pack "id", JSON.String edgeLabel)
                                 , (T.pack "source", JSON.String srcLabel)
                                 , (T.pack "target", JSON.String tgtLabel)
                                 ]
      in JSON.Object (HMS.fromList [(T.pack "data", JSON.Object content)])

initializeGraph :: String -> JSON.Value -> TP.JSFunction ()
initializeGraph divId graphData = TP.ffi "initializeGraphIn(null, %1, sliceGraphConfig, %2)" divId graphData

-- | Render a set of blocks (a slice) as a graph in the UI (using cytoscape)
--
-- This sets up the necessary DOM elements (easy) and translates the block
-- structure into a graph suitable for display in cytoscape. It uses the FFI
-- mechanism of threepenny-gui to sent the graph data to JS.
--
-- The cytoscape API expects a list of JS objects; it turns out that threepenny
-- can just use the Aeson Value type for that.
--
-- The format of the data should be a JS object with two top-level fields:
--
-- 1. nodes: A list of {data: {id : <ident>, text: <desc>}}
--
-- 2. edges: A list of {data: {id: <edgeLabel>, source: <src>, target: <tgt>}}
--
-- Note that this code uses block addresses (stringified) as identifiers.
renderSliceGraph
  :: (PA.ValidArch arch)
  => String
  -> PE.Blocks arch bkind
  -> (TP.UI TP.Element, TP.UI ())
renderSliceGraph divId (PE.Blocks _ _ parsedBlocks) =
  (TP.div # TP.set TP.id_ divId, TP.runFunction (initializeGraph divId (JSON.Object graph)))
  where
    nodes = F.foldl' blockNode Map.empty parsedBlocks
    edges = F.foldl' (blockEdges nodes) [] parsedBlocks
    graph = HMS.fromList [ (T.pack "nodes", JSON.Array (DV.fromList (Map.elems nodes)))
                         , (T.pack "edges", JSON.Array (DV.fromList (concat edges)))
                         ]

