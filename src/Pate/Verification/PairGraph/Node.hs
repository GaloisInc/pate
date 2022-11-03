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

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Verification.PairGraph.Node (
    GraphNode(..)
  , NodeEntry
  , NodeReturn
  , CallingContext
  , FrozenContext(..)
  , graphNodeCases
  , graphNodeBlocks
  , mkNodeEntry
  , addContext
  , mkNodeReturn
  , rootEntry
  , rootReturn
  , nodeBlocks
  , nodeFuns
  , returnToEntry
  , functionEntryOf
  , getFrozen
  , freezeNode
  , isThisFrozen
  , applyFreeze
  , unfreezeReturn
  , frozenRepr
  , freezeNodeFn
  , returnOfEntry
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>), Doc )

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
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

graphNodeCases :: GraphNode arch -> Either (PB.BlockPair arch) (PB.FunPair arch)
graphNodeCases (GraphNode (NodeEntry _ blks)) = Left blks
graphNodeCases (ReturnNode (NodeReturn _ funs)) = Right funs

-- | Additional context used to distinguish function calls
--   "Freezing" one binary in a node indicates that it should not continue
--   execution until the other binary has returned
data CallingContext arch = CallingContext { _ctxAncestors :: [PB.BlockPair arch], ctxFrozen :: FrozenContext arch }
  deriving (Eq, Ord)

data FrozenContext arch where
  FrozenBlock :: PBi.WhichBinaryRepr bin -> FrozenContext arch
  FrozenReturn :: PBi.WhichBinaryRepr bin -> FrozenContext arch
  NotFrozen :: FrozenContext arch

instance Eq (FrozenContext arch) where
  FrozenBlock repr1 == FrozenBlock repr2 | Just Refl <- testEquality repr1 repr2 = True
  FrozenReturn repr1 == FrozenReturn repr2 | Just Refl <- testEquality repr1 repr2 = True
  NotFrozen == NotFrozen = True
  _ == _ = False

instance Ord (FrozenContext arch) where
  compare frzn1 frzn2 = case (frzn1, frzn2) of
    (FrozenBlock repr1, FrozenBlock repr2) -> toOrdering (compareF repr1 repr2)
    (FrozenBlock{},FrozenReturn{}) -> GT
    (FrozenBlock{},NotFrozen) -> GT

    (FrozenReturn{}, FrozenBlock{}) -> LT
    (FrozenReturn repr1, FrozenReturn repr2) -> toOrdering (compareF repr1 repr2)
    (FrozenReturn{},NotFrozen) -> GT

    (NotFrozen, NotFrozen) -> EQ
    (NotFrozen, _) -> LT

frozenRepr :: FrozenContext arch -> Maybe (Some PBi.WhichBinaryRepr)
frozenRepr (FrozenBlock bin) = Just (Some bin)
frozenRepr (FrozenReturn bin) = Just (Some bin)
frozenRepr NotFrozen = Nothing

freezeBlock :: PBi.WhichBinaryRepr bin -> CallingContext arch -> CallingContext arch
freezeBlock bin (CallingContext ctx _) = CallingContext ctx (FrozenBlock bin)

freezeReturnCtx ::  PBi.WhichBinaryRepr bin -> CallingContext arch -> CallingContext arch
freezeReturnCtx bin (CallingContext ctx _) = CallingContext ctx (FrozenReturn bin)

unfreezeCtx :: CallingContext arch -> CallingContext arch
unfreezeCtx (CallingContext blks _) = CallingContext blks NotFrozen

instance PA.ValidArch arch => Pretty (CallingContext arch) where
  pretty (CallingContext bps frzn) =
    let
      bs = [ pretty bp | bp <- bps ]
    in sep ((zipWith (<+>) ( "via:" : repeat "<-") bs) ++ case frozenRepr frzn of
               Just (Some PBi.OriginalRepr) -> ["<<patched>>"]
               Just (Some PBi.PatchedRepr) -> ["<<original>>"]
               Nothing -> [])

freezeNodeFn :: PBi.WhichBinaryRepr bin ->  NodeEntry arch -> NodeEntry arch
freezeNodeFn bin (NodeEntry ctx blks) = NodeEntry (freezeReturnCtx bin ctx) blks

freezeNode :: PBi.WhichBinaryRepr bin -> NodeEntry arch -> NodeEntry arch
freezeNode bin (NodeEntry ctx blks) = NodeEntry (freezeBlock bin ctx) blks

freezeReturn :: PBi.WhichBinaryRepr bin -> NodeReturn arch -> NodeReturn arch
freezeReturn bin (NodeReturn ctx fns) = NodeReturn (freezeBlock bin ctx) fns

unfreezeReturn :: NodeReturn arch -> NodeReturn arch
unfreezeReturn (NodeReturn ctx fns) = NodeReturn (unfreezeCtx ctx) fns


getFrozen :: NodeEntry arch -> FrozenContext arch
getFrozen (NodeEntry ctx _) = ctxFrozen ctx

isThisFrozen :: (forall tp. PPa.PatchPair tp -> tp bin) -> NodeEntry arch -> Bool
isThisFrozen get node = frozenRepr (getFrozen node) == Just (Some (get PPa.patchPairRepr))


applyFreeze ::
  PBi.WhichBinaryRepr bin ->
  NodeEntry arch {- ^ current entry point -} ->
  PPa.PatchPair (PB.ConcreteBlock arch) {- ^ target -} ->
  NodeEntry arch
applyFreeze bin (NodeEntry ctx blks) pPair =
  let
    blk = PPa.getPair' bin pPair
    blks' = PPa.setPair bin blk blks
  in NodeEntry (freezeBlock bin ctx) blks'


rootEntry :: PB.BlockPair arch -> NodeEntry arch
rootEntry pPair = NodeEntry (CallingContext [] NotFrozen) pPair

rootReturn :: PB.FunPair arch -> NodeReturn arch
rootReturn pPair = NodeReturn (CallingContext [] NotFrozen) pPair

addContext :: PB.BlockPair arch -> NodeEntry arch -> NodeEntry arch
addContext newCtx (NodeEntry (CallingContext ctx frzn) blks) = NodeEntry (CallingContext (newCtx:ctx) frzn) blks

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (graphNodeContext node) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (graphNodeContext node) fPair

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
