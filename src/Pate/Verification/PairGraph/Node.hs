{-# LANGUAGE StandaloneDeriving #-}
module Pate.Verification.PairGraph.Node (
  GraphNode(..)
  ) where

import           Prettyprinter ( Pretty(..), viaShow )

import qualified Pate.Arch as PA
import qualified Pate.PatchPair as PPa

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
  = GraphNode (PPa.BlockPair arch)
  | ReturnNode (PPa.FunPair arch)
 deriving (Eq, Ord)

deriving instance PA.ValidArch arch => Show (GraphNode arch)

instance PA.ValidArch arch => Pretty (GraphNode arch) where
  pretty = viaShow
