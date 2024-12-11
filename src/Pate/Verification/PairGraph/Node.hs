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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}

module Pate.Verification.PairGraph.Node (
    GraphNode
  , GraphNode'(..)
  , NodeEntry'
  , NodeReturn'
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
  , toSingleNodeEntry
  , singleNodeAddr
  , SingleNodeReturn
  , SingleGraphNode
  , pattern SingleNodeReturn
  , singleNodeRepr
  , singleNodeDivergePoint
  , singleNodeDivergence
  ) where

import           Prettyprinter ( Pretty(..), sep, (<+>), Doc )
import qualified Data.Aeson as JSON
import qualified Compat.Aeson as HMS

import qualified Data.Quant as Qu
import           Data.Quant ( Quant(..), QuantK, ExistsK )

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
import qualified Pate.Address as PAd
import Data.Kind (Type)

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
data GraphNode' arch (bin :: QuantK PB.WhichBinary)
  = GraphNode (NodeEntry' arch bin)
  | ReturnNode (NodeReturn' arch bin)
 deriving (Eq, Ord)

type GraphNode arch = GraphNode' arch ExistsK

instance TestEquality (GraphNode' arch) where
  testEquality nd1 nd2 | Just Refl <- testEquality (nodeRepr nd1) (nodeRepr nd2), nd1 == nd2 = Just Refl
  testEquality _ _ = Nothing

instance OrdF (GraphNode' arch) where
  compareF nd1 nd2 = lexCompareF (nodeRepr nd1) (nodeRepr nd2) $ fromOrdering $ compare nd1 nd2

instance Qu.QuantCoercible (GraphNode' arch) where
  coerceQuant = \case
    GraphNode ne -> GraphNode (Qu.coerceQuant ne)
    ReturnNode nr -> ReturnNode (Qu.coerceQuant nr)

instance PA.ValidArch arch => JSON.ToJSON (GraphNode' arch bin) where
  toJSON = \case
    GraphNode nd -> JSON.object [ ("graph_node_type", "entry"), "entry_body" JSON..= nd]
    ReturnNode nd -> JSON.object [ ("graph_node_type", "return"), "return_body" JSON..= nd]

instance PA.ValidArch arch => W4S.W4Serializable sym (GraphNode' arch bin) where
  w4Serialize r = return $ JSON.toJSON r

instance PA.ValidArch arch => W4S.W4Serializable sym (NodeEntry' arch bin) where
  w4Serialize r = return $ JSON.toJSON r

data NodeContent arch (f :: PB.WhichBinary -> Type) (qbin :: QuantK PB.WhichBinary) = 
  NodeContent { nodeContentCtx :: CallingContext arch, nodeContent :: Quant f qbin }

deriving instance (forall x. Eq (f x)) => Eq (NodeContent arch f qbin)
deriving instance (forall x. Ord (f x)) => Ord (NodeContent arch f qbin)

instance (forall x. Eq (f x)) => TestEquality (NodeContent arch f) where
  testEquality (NodeContent cctx1 x1) (NodeContent cctx2 x2) | cctx1 == cctx2, Just Refl <- testEquality x1 x2 = Just Refl
  testEquality _ _ = Nothing

instance (forall x. Ord (f x)) => OrdF (NodeContent arch f) where
  compareF (NodeContent cctx1 x1) (NodeContent cctx2 x2) = lexCompareF x1 x2 $ fromOrdering (compare cctx1 cctx2)

type NodeEntry' arch = NodeContent arch (PB.ConcreteBlock arch)
type NodeEntry arch = NodeEntry' arch ExistsK

instance Qu.QuantCoercible (NodeEntry' arch) where
  coerceQuant (NodeEntry cctx blks) = NodeEntry cctx (Qu.coerceQuant blks)

pattern NodeEntry :: CallingContext arch -> Quant (PB.ConcreteBlock arch) bin -> NodeEntry' arch bin
pattern NodeEntry ctx bp = NodeContent ctx bp
{-# COMPLETE NodeEntry #-}

nodeEntryRepr :: NodeEntry' arch qbin -> Qu.QuantRepr qbin
nodeEntryRepr ne = Qu.quantToRepr $ nodeBlocks ne

nodeBlocks :: NodeEntry' arch bin -> Quant (PB.ConcreteBlock arch) bin
nodeBlocks = nodeContent

graphNodeContext :: NodeEntry' arch bin -> CallingContext arch
graphNodeContext = nodeContentCtx

type NodeReturn' arch = NodeContent arch (PB.FunctionEntry arch)
type NodeReturn arch = NodeReturn' arch ExistsK

nodeReturnRepr :: NodeReturn' arch qbin -> Qu.QuantRepr qbin
nodeReturnRepr ne = Qu.quantToRepr $ nodeFuns ne

nodeFuns :: NodeReturn' arch bin -> Quant (PB.FunctionEntry arch) bin
nodeFuns = nodeContent

nodeRepr :: GraphNode' arch qbin -> Qu.QuantRepr qbin
nodeRepr (GraphNode ne) = nodeEntryRepr ne
nodeRepr (ReturnNode rn) = nodeReturnRepr rn

returnNodeContext :: NodeReturn' arch bin -> CallingContext arch
returnNodeContext = nodeContentCtx

pattern NodeReturn :: CallingContext arch -> Quant (PB.FunctionEntry arch) bin -> NodeReturn' arch bin
pattern NodeReturn ctx bp = NodeContent ctx bp
{-# COMPLETE NodeReturn #-}

instance Qu.QuantCoercible (NodeReturn' arch) where
  coerceQuant (NodeReturn cctx fns) = NodeReturn cctx (Qu.coerceQuant fns)

graphNodeBlocks :: GraphNode' arch bin -> Quant (PB.ConcreteBlock arch) bin
graphNodeBlocks (GraphNode ne) = nodeBlocks ne
graphNodeBlocks (ReturnNode ret) = Qu.map PB.functionEntryToConcreteBlock (nodeFuns ret)

nodeContext :: GraphNode' arch qbin  -> CallingContext arch
nodeContext (GraphNode nd) = nodeContentCtx nd
nodeContext (ReturnNode ret) = nodeContentCtx ret

pattern GraphNodeEntry :: Quant (PB.ConcreteBlock arch) bin -> GraphNode' arch bin
pattern GraphNodeEntry blks <- (GraphNode (NodeContent _ blks))

pattern GraphNodeReturn :: Quant (PB.FunctionEntry arch) bin -> GraphNode' arch bin
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

rootEntry :: PB.BinaryPair (PB.ConcreteBlock arch) qbin -> NodeEntry' arch qbin
rootEntry pPair = NodeEntry (CallingContext [] Nothing) pPair

rootReturn :: PB.BinaryPair (PB.FunctionEntry arch) qbin -> NodeReturn' arch qbin
rootReturn pPair = NodeReturn (CallingContext [] Nothing) pPair

addContext :: PB.BinaryPair (PB.ConcreteBlock arch) qbin1 -> NodeEntry' arch qbin2 -> NodeEntry' arch qbin2
addContext newCtx' ne@(NodeEntry (CallingContext ctx d) blks) = 
  case elem newCtx ctx of
    -- avoid recursive loops
    True -> ne
    False -> NodeEntry (CallingContext (newCtx:ctx) d) blks
    where
      newCtx = Qu.QuantSome newCtx'

-- Strip diverge points from two-sided nodes. This is used so that
-- merged nodes (which are two-sided) can meaningfully retain their
-- diverge point, but it will be stripped on any subsequent nodes.
mkNextContext :: Quant a (bin :: QuantK PB.WhichBinary) -> CallingContext arch -> CallingContext arch
mkNextContext q cctx = case q of
  Qu.All{} -> dropDivergePoint cctx
  Qu.Single{} -> cctx

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
returnToEntry :: NodeReturn' arch bin -> NodeEntry' arch bin
returnToEntry (NodeReturn ctx fns) = NodeEntry (mkNextContext fns ctx) (Qu.map PB.functionEntryToConcreteBlock fns)

-- | Get the return node that this entry would return to
returnOfEntry :: NodeEntry' arch bin -> NodeReturn' arch bin
returnOfEntry (NodeEntry ctx blks) = NodeReturn (mkNextContext blks ctx) (Qu.map PB.blockFunctionEntry blks)

-- | For an intermediate entry point in a function, find the entry point
--   corresponding to the function start
functionEntryOf :: NodeEntry' arch bin -> NodeEntry' arch bin
functionEntryOf (NodeEntry ctx blks) = NodeEntry (mkNextContext blks ctx) (Qu.map (PB.functionEntryToConcreteBlock . PB.blockFunctionEntry) blks)

instance PA.ValidArch arch => Show (CallingContext arch) where
  show c = show (pretty c)

instance PA.ValidArch arch => Show (NodeEntry' arch bin) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (NodeEntry' arch bin) where
  pretty e = case functionEntryOf e == e of
    True -> case graphNodeContext e of
      CallingContext [] _ -> pretty (nodeBlocks e)
      _ -> pretty (nodeBlocks e) <+> "[" <+> pretty (graphNodeContext e) <+> "]"
    False -> PB.ppBinaryPair' PB.ppBlockAddr (nodeBlocks e)
      <+> "[" <+> pretty (graphNodeContext (addContext (nodeBlocks (functionEntryOf e)) e)) <+> "]"

instance PA.ValidArch arch => Pretty (NodeReturn' arch qbin) where
  pretty e = case returnNodeContext e of
    CallingContext [] _ -> pretty (nodeFuns e)
    _ -> pretty (nodeFuns e) <+> "[" <+> pretty (returnNodeContext e) <+> "]"

instance PA.ValidArch arch => Show (NodeReturn' arch qbin) where
  show e = show (pretty e)

instance PA.ValidArch arch => Pretty (GraphNode' arch qbin) where
  pretty (GraphNode e) = "GraphNode" <+> pretty e
  pretty (ReturnNode e) = "ReturnNode" <+> pretty e

instance PA.ValidArch arch => Show (GraphNode' arch qbin) where
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

instance PA.ValidArch arch => JSON.ToJSON (NodeEntry' arch bin) where
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
  
instance PA.ValidArch arch => JSON.ToJSON (NodeReturn' arch bin) where
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

type SingleNodeEntry arch bin = NodeEntry' arch (Qu.OneK bin)

pattern SingleNodeEntry :: CallingContext arch -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
pattern SingleNodeEntry cctx blk <- ((\l -> case l of NodeEntry cctx (Qu.Single _ blk) -> (cctx,blk)) -> (cctx,blk))
  where
    SingleNodeEntry cctx blk = NodeEntry cctx (Qu.Single (PB.blockBinRepr blk) blk)

{-# COMPLETE SingleNodeEntry #-}

singleEntryBin :: SingleNodeEntry arch bin -> PB.WhichBinaryRepr bin
singleEntryBin (nodeEntryRepr -> Qu.QuantOneRepr repr) = repr

singleNodeAddr :: SingleNodeEntry arch bin -> PPa.WithBin (PAd.ConcreteAddress arch) bin
singleNodeAddr se = PPa.WithBin (singleEntryBin se) (PB.concreteAddress (singleNodeBlock se))

mkSingleNodeEntry :: NodeEntry' arch qbin -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
mkSingleNodeEntry node blk = SingleNodeEntry (graphNodeContext node) blk


singleNodeDivergePoint :: SingleGraphNode arch bin -> GraphNode arch
singleNodeDivergePoint sgn = case divergePoint (nodeContext sgn) of
  Just dp -> dp
  Nothing -> panic Verifier "singleNodeDivergePoint" ["missing diverge point for SingleNodeEntry"]


singleNodeDivergence :: SingleNodeEntry arch bin -> GraphNode arch
singleNodeDivergence sne = singleNodeDivergePoint (GraphNode sne)


asSingleNodeEntry :: PPa.PatchPairM m => NodeEntry' arch qbin -> m (Some (Qu.AsSingle (NodeEntry' arch)))
asSingleNodeEntry (NodeEntry cctx blks) = do
  Pair _ blk <- PPa.asSingleton blks
  case divergePoint cctx of
    Just{} -> return $ Some (Qu.AsSingle $ SingleNodeEntry cctx blk)
    Nothing -> PPa.throwPairErr

singleNodeBlock :: SingleNodeEntry arch bin -> PB.ConcreteBlock arch bin
singleNodeBlock (SingleNodeEntry _ blk) = blk

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
      return $ SingleNodeEntry cctx blk
    _ -> PPa.throwPairErr

singleToNodeEntry :: SingleNodeEntry arch bin -> NodeEntry arch
singleToNodeEntry sne = Qu.coerceQuant sne

singleToGraphNode :: SingleGraphNode arch bin -> GraphNode arch
singleToGraphNode sgn = Qu.coerceQuant sgn

combineSingleEntries' :: 
  SingleNodeEntry arch PB.Original -> 
  SingleNodeEntry arch PB.Patched ->
  Maybe (NodeEntry arch)
combineSingleEntries' (SingleNodeEntry cctxO blksO) (SingleNodeEntry cctxP blksP) = do
  GraphNode divergeO <- divergePoint $ cctxO
  GraphNode divergeP <- divergePoint $ cctxP
  guard $ divergeO == divergeP
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

type SingleNodeReturn arch bin = NodeReturn' arch (Qu.OneK bin)

pattern SingleNodeReturn :: CallingContext arch -> PB.FunctionEntry arch bin -> SingleNodeReturn arch bin
pattern SingleNodeReturn cctx fn <- ((\l -> case l of NodeReturn cctx (Qu.Single _ fn) -> (cctx,fn)) -> (cctx,fn))
  where
    SingleNodeReturn cctx fn = NodeReturn cctx (Qu.Single (PB.functionBinRepr fn) fn)

type SingleGraphNode arch bin = GraphNode' arch (Qu.OneK bin)

singleNodeRepr :: SingleGraphNode arch bin -> PB.WhichBinaryRepr bin
singleNodeRepr sgn = case nodeRepr sgn of Qu.QuantOneRepr repr -> repr