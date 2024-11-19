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
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pate.Verification.PairGraph.Node (
   
    GraphNode
  , pattern ReturnNode
  , pattern GraphNode
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
  , singleNodeAddr
  , pattern SingleNodeReturn
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>), Doc )
import qualified Data.Aeson as JSON
import qualified Compat.Aeson as HMS
import qualified Data.Parameterized.TraversableF as TF

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.PatchPair as PPa
import           Pate.TraceTree
import qualified Pate.Binary as PBi
import qualified Prettyprinter as PP
import Data.Parameterized (Some(..), Pair (..))
import qualified What4.JSON as W4S
import Control.Monad (guard)
import Data.Parameterized.Classes
import Pate.Panic
import qualified Pate.Address as PAd

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
data GraphNodeGen arch (bin :: PBi.BinaryType)
  = GraphNodeGen (NodeEntryGen arch bin)
  | ReturnNodeGen (NodeReturnGen arch bin)
 deriving (Eq, Ord)

type GraphNode arch = PBi.SomeBinary (GraphNodeGen arch)

pattern GraphNode :: NodeEntry arch -> GraphNode arch
pattern GraphNode ne <- 
  ((\(PBi.SomeBinary bin l) -> case l of GraphNodeGen ne -> Just (PBi.SomeBinary bin ne); _ -> Nothing) -> Just ne)
  where
    GraphNode (PBi.SomeBinary bin ne) = PBi.SomeBinary bin (GraphNodeGen ne)

pattern ReturnNode :: NodeReturn arch -> GraphNode arch
pattern ReturnNode ne <- 
  ((\(PBi.SomeBinary bin l) -> case l of ReturnNodeGen ne -> Just (PBi.SomeBinary bin ne); _ -> Nothing) -> Just ne)
  where
    ReturnNode (PBi.SomeBinary bin ne) = PBi.SomeBinary bin (ReturnNodeGen ne)

{-# COMPLETE GraphNode, ReturnNode #-}

-- | Calling context for a given graphnode
data CallingContext arch = CallingContext { _ctxAncestors :: [PB.BlockPair arch], divergePoint :: Maybe (GraphNode arch) }
  deriving (Eq, Ord)

data NodeContentGen arch e bin = 
  NodeContentGen { nodeContentCtxGen :: CallingContext arch, nodeContentGen :: PBi.BinaryPair e bin }

deriving instance (forall wbin. Eq (e wbin)) => Eq (NodeContentGen arch e bin)
deriving instance (forall wbin. Ord (e wbin)) => Ord (NodeContentGen arch e bin)

type NodeEntryGen arch = NodeContentGen arch (PB.ConcreteBlock arch)
type NodeReturnGen arch = NodeContentGen arch (PB.FunctionEntry arch)

type NodeContent arch e = PBi.SomeBinary (NodeContentGen arch e)

nodeContentCtx :: NodeContent arch e -> CallingContext arch
nodeContentCtx (NodeContent ctx _) = ctx

nodeContent :: NodeContent arch e -> PPa.PatchPair e
nodeContent (NodeContent _ e) = e

pattern NodeContent :: CallingContext arch -> PPa.PatchPair e -> NodeContent arch e
pattern NodeContent ctx blks <- 
  ((\l -> case l of (PBi.SomeBinary _ (NodeContentGen ctx blks)) -> Just (ctx, PPa.fromBinaryPair blks); _ -> Nothing) -> Just (ctx, blks))
  where
    NodeContent ctx blks = case PPa.asBinaryPair blks of
      PBi.SomeBinary bin blks' -> PBi.SomeBinary bin (NodeContentGen ctx blks')

{-# COMPLETE NodeContent #-}

type NodeEntry arch = NodeContent arch (PB.ConcreteBlock arch)
type NodeReturn arch = NodeContent arch (PB.FunctionEntry arch)


pattern GraphNodeEntry :: PB.BlockPair arch -> GraphNode arch
pattern GraphNodeEntry blks <- GraphNode (NodeContent _ blks)

pattern GraphNodeReturn :: PB.FunPair arch -> GraphNode arch
pattern GraphNodeReturn blks <- ReturnNode (NodeContent _ blks)

{-# COMPLETE GraphNodeEntry, GraphNodeReturn #-}

instance PA.ValidArch arch => JSON.ToJSON (GraphNode arch) where
  toJSON = \case
    GraphNode nd -> JSON.object [ ("graph_node_type", "entry"), "entry_body" JSON..= nd]
    ReturnNode nd -> JSON.object [ ("graph_node_type", "return"), "return_body" JSON..= nd]

instance PA.ValidArch arch => W4S.W4Serializable sym (GraphNode arch) where
  w4Serialize r = return $ JSON.toJSON r

instance PA.ValidArch arch => W4S.W4Serializable sym (NodeEntry arch) where
  w4Serialize r = return $ JSON.toJSON r


pattern NodeEntry :: CallingContext arch -> PB.BlockPair arch -> NodeEntry arch
pattern NodeEntry ctx bp = NodeContent ctx bp
{-# COMPLETE NodeEntry #-}

pattern NodeReturn :: CallingContext arch -> PB.FunPair arch -> NodeReturn arch
pattern NodeReturn ctx bp = NodeContent ctx bp
{-# COMPLETE NodeReturn #-}

nodeBlocks :: NodeEntry arch -> PB.BlockPair arch
nodeBlocks = nodeContent

graphNodeContext :: NodeEntry arch -> CallingContext arch
graphNodeContext = nodeContentCtx

nodeFuns :: NodeReturn arch -> PB.FunPair arch
nodeFuns = nodeContent

returnNodeContext :: NodeReturn arch -> CallingContext arch
returnNodeContext = nodeContentCtx



graphNodeBlocks :: GraphNode arch -> PB.BlockPair arch
graphNodeBlocks (GraphNode ne) = nodeBlocks ne
graphNodeBlocks (ReturnNode ret) = TF.fmapF PB.functionEntryToConcreteBlock (nodeFuns ret)

nodeContext :: GraphNode arch -> CallingContext arch
nodeContext (GraphNode nd) = nodeContentCtx nd
nodeContext (ReturnNode ret) = nodeContentCtx ret


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
  PB.ConcreteBlock arch PBi.Original ->
  PB.ConcreteBlock arch PBi.Patched -> 
  NodeEntry arch
mkMergedNodeEntry nd blkO blkP = NodeEntry (CallingContext cctx (Just nd)) (PPa.PatchPair blkO blkP)
  where
    CallingContext cctx _ = nodeContext nd

mkMergedNodeReturn :: 
  GraphNode arch -> 
  PB.FunctionEntry arch PBi.Original ->
  PB.FunctionEntry arch PBi.Patched -> 
  NodeReturn arch
mkMergedNodeReturn nd fnO fnP = NodeReturn (CallingContext cctx (Just nd)) (PPa.PatchPair fnO fnP)
  where
    CallingContext cctx _ = nodeContext nd


-- | Project the given 'NodeReturn' into a singleton node for the given binary
toSingleReturn :: PPa.PatchPairM m => PBi.WhichBinaryRepr bin -> GraphNode arch -> NodeReturn arch -> m (NodeReturn arch)
toSingleReturn bin divergedAt (NodeReturn ctx fPair) = do
  fPair' <- PPa.toSingleton bin fPair
  return $ NodeReturn (ctx {divergePoint = Just divergedAt}) fPair'

-- | Project the given 'NodeEntry' into a singleton node for the given binary
toSingleNode:: PPa.PatchPairM m => PBi.WhichBinaryRepr bin -> NodeEntry arch -> m (NodeEntry arch)
toSingleNode bin node@(NodeEntry ctx bPair) = do
  fPair' <- PPa.toSingleton bin bPair
  return $ NodeEntry (ctx {divergePoint = Just (GraphNode node)}) fPair'

toSingleGraphNode :: PPa.PatchPairM m => PBi.WhichBinaryRepr bin -> GraphNode arch -> m (GraphNode arch)
toSingleGraphNode bin node = case node of
  GraphNode ne -> GraphNode <$> toSingleNode bin ne
  ReturnNode nr -> ReturnNode <$> toSingleReturn bin node nr  

isSingleNodeEntry :: 
  PPa.PatchPairM m => 
  NodeEntry arch -> 
  m (Some PBi.WhichBinaryRepr)
isSingleNodeEntry (NodeEntry _ bPair) = do
  Pair bin _ <- PPa.asSingleton bPair
  return $ Some bin

isSingleReturn ::
  PPa.PatchPairM m => 
  NodeReturn arch -> 
  m (Some PBi.WhichBinaryRepr)
isSingleReturn (NodeReturn _ bPair) = do
  Pair bin _ <- PPa.asSingleton bPair
  return $ Some bin

-- | If the given 'GraphNode' is a singleton, return the corresponding
--   'PB.WhichBinaryRepr'
isSingleNode ::
  PPa.PatchPairM m => 
  GraphNode arch -> 
  m (Some PBi.WhichBinaryRepr)
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
  nodeO <- PPa.getC PBi.OriginalRepr nodes
  nodeP <- PPa.getC PBi.PatchedRepr nodes
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

type SingleGraphNode arch = PBi.AsSingle (GraphNodeGen arch)
type SingleNodeEntry arch = PBi.AsSingle (NodeEntryGen arch)
type SingleNodeReturn arch = PBi.AsSingle (NodeReturnGen arch)

singleEntryBin :: SingleNodeEntry arch bin -> PBi.WhichBinaryRepr bin
singleEntryBin (SingleNodeEntry bin _ _) = bin

pattern SingleNodeEntry :: PBi.WhichBinaryRepr bin -> CallingContext arch -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
pattern SingleNodeEntry bin cctx blk <- 
  ((\(PBi.AsSingle bin sne) -> case nodeContentGen sne of PBi.BinarySingle _ blk -> (nodeContentCtxGen sne, bin, blk)) -> (cctx,bin,blk))
  where
    SingleNodeEntry bin cctx blk = PBi.AsSingle bin (NodeContentGen cctx (PBi.BinarySingle bin blk))

pattern SingleNodeReturn :: PBi.WhichBinaryRepr bin -> CallingContext arch -> PB.FunctionEntry arch bin -> SingleNodeReturn arch bin
pattern SingleNodeReturn bin cctx blk <- 
  ((\(PBi.AsSingle bin sne) -> case nodeContentGen sne of PBi.BinarySingle _ blk -> (nodeContentCtxGen sne, bin, blk)) -> (cctx,bin,blk))
  where
    SingleNodeReturn bin cctx blk = PBi.AsSingle bin (NodeContentGen cctx (PBi.BinarySingle bin blk))


{-# COMPLETE SingleNodeEntry #-}

singleNodeAddr :: SingleNodeEntry arch bin -> PPa.WithBin (PAd.ConcreteAddress arch) bin
singleNodeAddr se = PPa.WithBin (singleEntryBin se) (PB.concreteAddress (singleNodeBlock se))

mkSingleNodeEntry :: NodeEntry arch -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
mkSingleNodeEntry node blk = SingleNodeEntry (PB.blockBinRepr blk) (graphNodeContext node) blk

instance PA.ValidArch arch => Show (SingleNodeEntry arch bin) where
  show e = show (singleToNodeEntry e)

singleNodeDivergePoint :: SingleNodeEntry arch bin -> GraphNode arch
singleNodeDivergePoint (SingleNodeEntry _ cctx _) = case divergePoint cctx of
  Just dp -> dp
  Nothing -> panic Verifier "singleNodeDivergePoint" ["missing diverge point for SingleNodeEntry"]

asSingleNodeEntry :: PPa.PatchPairM m => NodeEntry arch -> m (Some (SingleNodeEntry arch))
asSingleNodeEntry (NodeEntry cctx bPair) = do
  Pair bin blk <- PPa.asSingleton bPair
  case divergePoint cctx of
    Just{} -> return $ Some (SingleNodeEntry bin cctx blk)
    Nothing -> PPa.throwPairErr

singleNodeBlock :: SingleNodeEntry arch bin -> PB.ConcreteBlock arch bin
singleNodeBlock (SingleNodeEntry _ _ blk) = blk

-- | Returns a 'SingleNodeEntry' for a given 'NodeEntry' if it has an entry
--   for the given 'bin'.
--   Note that, in contrast to
--   'asSingleNodeEntry' this does not require the given 'NodeEntry' to be a singleton
toSingleNodeEntry :: 
  PPa.PatchPairM m => 
  PBi.WhichBinaryRepr bin -> 
  NodeEntry arch -> 
  m (SingleNodeEntry arch bin)
toSingleNodeEntry bin ne = do
  case toSingleNode bin ne of
    Just (NodeEntry cctx bPair) -> do
      blk <- PPa.get bin bPair
      return $ SingleNodeEntry bin cctx blk
    _ -> PPa.throwPairErr

singleToNodeEntry :: SingleNodeEntry arch bin -> NodeEntry arch
singleToNodeEntry (SingleNodeEntry bin cctx blk) = 
  NodeEntry cctx (PPa.PatchPairSingle bin blk)

singleNodeDivergence :: SingleNodeEntry arch bin -> GraphNode arch
singleNodeDivergence (SingleNodeEntry _ cctx _) = case divergePoint cctx of
  Just dp -> dp
  Nothing -> panic Verifier "singleNodeDivergence" ["Unexpected missing divergence point"]

combineSingleEntries' :: 
  SingleNodeEntry arch PBi.Original -> 
  SingleNodeEntry arch PBi.Patched ->
  Maybe (NodeEntry arch)
combineSingleEntries' (SingleNodeEntry _ cctxO blkO) (SingleNodeEntry _ cctxP blkP) = do
  GraphNode divergeO <- divergePoint $ cctxO
  GraphNode divergeP <- divergePoint $ cctxP
  guard $ divergeO == divergeP
  return $ mkNodeEntry divergeO (PPa.PatchPair blkO blkP)

-- | Create a combined two-sided 'NodeEntry' based on
--   a pair of single-sided entries. The given entries
--   must have the same diverge point (returns 'Nothing' otherwise),
--   and the calling context of the resulting node is inherited from
--   that point (i.e. any additional context accumulated during
--   the either single-sided analysis is discarded)
combineSingleEntries :: 
  SingleNodeEntry arch bin -> 
  SingleNodeEntry arch (PBi.OtherBinary bin) ->
  Maybe (NodeEntry arch)
combineSingleEntries sne1 sne2 = case singleEntryBin sne1 of
  PBi.OriginalRepr -> combineSingleEntries' sne1 sne2
  PBi.PatchedRepr -> combineSingleEntries' sne2 sne1

