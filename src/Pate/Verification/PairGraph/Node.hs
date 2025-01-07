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
  , toSingleNode
  , toSingleGraphNode
  , isSingleNode
  , isSingleNodeEntry
  , isSingleReturn
  , getDivergePoint
  , getDivergePoint'
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
  , withKnownBin
  , toTwoSidedNode
  , asSingleNode
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
import Data.Parameterized.WithRepr

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

coerceContext :: Qu.QuantCoercion t1 t2 -> GraphNode' arch t1 -> CallingContext' arch t1 -> CallingContext' arch t2
coerceContext qc nd x@(CallingContext' cctx dp) = case qc of
  Qu.CoerceAllToOne repr -> case divergePoint' (nodeContext nd) of
    DivergePoint nd' -> CallingContext' cctx (DivergePointSingle repr nd')
    NoDivergePoint -> CallingContext' cctx (DivergePointSingle repr nd)
  Qu.CoerceToExists _ -> CallingContext' cctx (divergePointExists dp)
  Qu.CoerceRefl{} -> x

instance Qu.QuantCoercible (GraphNode' arch) where
  applyQuantCoercion qc nd = case nd of
    GraphNode (NodeEntry cctx blks) -> GraphNode (NodeEntry (coerceContext qc nd cctx) (Qu.applyQuantCoercion qc blks))
    ReturnNode (NodeReturn cctx fns) -> ReturnNode (NodeReturn (coerceContext qc nd cctx) (Qu.applyQuantCoercion qc fns))

instance Qu.QuantConvertible (CallingContext' arch) where
  applyQuantConversion qc (CallingContext' cctx dp) = CallingContext' <$> pure cctx <*> Qu.applyQuantConversion qc dp

instance Qu.QuantConvertible (GraphNode' arch) where
  convertQuant = \case
    GraphNode (NodeEntry cctx blks) -> (\cctx' blks' -> GraphNode (NodeEntry cctx' blks')) <$> Qu.convertQuant cctx <*> Qu.convertQuant blks
    ReturnNode (NodeReturn cctx fns) -> (\cctx' fns' -> ReturnNode (NodeReturn cctx' fns')) <$> Qu.convertQuant cctx <*> Qu.convertQuant fns

withKnownBin :: GraphNode' arch qbin -> ((KnownRepr Qu.QuantRepr qbin, Qu.IsExistsOr qbin qbin) => a) -> a
withKnownBin nd f = case graphNodeBlocks nd of
  Qu.All{} -> f
  Qu.Single{} -> f

instance PA.ValidArch arch => JSON.ToJSON (GraphNode' arch bin) where
  toJSON = \case
    GraphNode nd -> JSON.object [ ("graph_node_type", "entry"), "entry_body" JSON..= nd]
    ReturnNode nd -> JSON.object [ ("graph_node_type", "return"), "return_body" JSON..= nd]

instance PA.ValidArch arch => W4S.W4Serializable sym (GraphNode' arch bin) where
  w4Serialize r = return $ JSON.toJSON r

instance PA.ValidArch arch => W4S.W4Serializable sym (NodeEntry' arch bin) where
  w4Serialize r = return $ JSON.toJSON r

data NodeContent arch (f :: PB.WhichBinary -> Type) (qbin :: QuantK PB.WhichBinary) = 
  NodeContent { nodeContentCtx :: CallingContext' arch qbin, nodeContent :: Quant f qbin }

deriving instance (forall x. Eq (f x)) => Eq (NodeContent arch f qbin)
deriving instance (forall x. Ord (f x)) => Ord (NodeContent arch f qbin)

instance (forall x. Eq (f x)) => TestEquality (NodeContent arch f) where
  testEquality (NodeContent cctx1 x1) (NodeContent cctx2 x2) | Just Refl <- testEquality x1 x2, cctx1 == cctx2 = Just Refl
  testEquality _ _ = Nothing

instance (forall x. Ord (f x)) => OrdF (NodeContent arch f) where
  compareF (NodeContent cctx1 x1) (NodeContent cctx2 x2) = lexCompareF x1 x2 $ fromOrdering (compare cctx1 cctx2)

type NodeEntry' arch = NodeContent arch (PB.ConcreteBlock arch)
type NodeEntry arch = NodeEntry' arch ExistsK

pattern NodeEntry :: CallingContext' arch bin -> Quant (PB.ConcreteBlock arch) bin -> NodeEntry' arch bin
pattern NodeEntry ctx bp = NodeContent ctx bp
{-# COMPLETE NodeEntry #-}

nodeEntryRepr :: NodeEntry' arch qbin -> Qu.QuantRepr qbin
nodeEntryRepr ne = Qu.quantToRepr $ nodeBlocks ne

nodeBlocks :: NodeEntry' arch bin -> Quant (PB.ConcreteBlock arch) bin
nodeBlocks = nodeContent

graphNodeContext :: NodeEntry' arch bin -> CallingContext' arch bin
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

returnNodeContext :: NodeReturn' arch bin -> CallingContext' arch bin
returnNodeContext = nodeContentCtx

pattern NodeReturn :: CallingContext' arch bin -> Quant (PB.FunctionEntry arch) bin -> NodeReturn' arch bin
pattern NodeReturn ctx bp = NodeContent ctx bp
{-# COMPLETE NodeReturn #-}

graphNodeBlocks :: GraphNode' arch bin -> Quant (PB.ConcreteBlock arch) bin
graphNodeBlocks (GraphNode ne) = nodeBlocks ne
graphNodeBlocks (ReturnNode ret) = Qu.map PB.functionEntryToConcreteBlock (nodeFuns ret)

nodeContext :: GraphNode' arch qbin  -> CallingContext' arch qbin
nodeContext (GraphNode nd) = nodeContentCtx nd
nodeContext (ReturnNode ret) = nodeContentCtx ret

pattern GraphNodeEntry :: Quant (PB.ConcreteBlock arch) bin -> GraphNode' arch bin
pattern GraphNodeEntry blks <- (GraphNode (NodeContent _ blks))

pattern GraphNodeReturn :: Quant (PB.FunctionEntry arch) bin -> GraphNode' arch bin
pattern GraphNodeReturn blks <- (ReturnNode (NodeContent _ blks))

{-# COMPLETE GraphNodeEntry, GraphNodeReturn #-}

data DivergePoint arch (tp :: Qu.QuantK PB.WhichBinary) where
  DivergePointSingle :: PB.WhichBinaryRepr bin -> GraphNode' arch Qu.AllK -> DivergePoint arch (Qu.OneK bin)
  NoDivergePointCtor :: DivergePoint arch Qu.AllK
  SomeDivergePoint :: Maybe (GraphNode' arch Qu.AllK) -> DivergePoint arch Qu.ExistsK

divergePointExists :: DivergePoint arch tp -> DivergePoint arch Qu.ExistsK
divergePointExists = \case
  DivergePointSingle _ nd -> SomeDivergePoint (Just nd)
  NoDivergePointCtor -> SomeDivergePoint Nothing
  x@SomeDivergePoint{} -> x

instance Qu.QuantConvertible (DivergePoint arch) where
  applyQuantConversion qc dp = case (qc, dp) of
    (Qu.ConvertExistsToAll, SomeDivergePoint (Just _)) -> Nothing -- invalid case
    (Qu.ConvertExistsToAll, SomeDivergePoint Nothing) -> Just $ NoDivergePointCtor
    (Qu.ConvertExistsToOne repr, SomeDivergePoint (Just nd)) -> Just $ (DivergePointSingle repr nd)
    (Qu.ConvertExistsToOne{}, SomeDivergePoint Nothing) -> Nothing
    (Qu.ConvertRefl _, _) -> Just dp
    (Qu.ConvertNone{},_) -> Nothing


deriving instance Eq (DivergePoint arch tp)
deriving instance Ord (DivergePoint arch tp)


data DivergePointProof arch tp where
  DivergePointProof :: (KnownRepr Qu.QuantRepr tp, Qu.IsExistsOr tp tp, Qu.NotAllK tp) => GraphNode' arch Qu.AllK -> DivergePointProof arch tp

divergePointProof :: DivergePoint arch tp -> Maybe (DivergePointProof arch tp)
divergePointProof = \case
  DivergePointSingle repr nd -> withRepr repr $ Just $ DivergePointProof nd
  NoDivergePointCtor -> Nothing
  SomeDivergePoint (Just nd) -> Just $ DivergePointProof nd
  SomeDivergePoint Nothing -> Nothing

pattern DivergePoint :: forall arch tp. () => (KnownRepr Qu.QuantRepr tp, Qu.IsExistsOr tp tp, Qu.NotAllK tp) => GraphNode' arch Qu.AllK -> DivergePoint arch tp
pattern DivergePoint nd <- (divergePointProof -> Just (DivergePointProof nd)) where
  DivergePoint nd = case knownRepr :: Qu.QuantRepr tp of
    Qu.QuantOneRepr repr -> DivergePointSingle repr nd
    Qu.QuantSomeRepr -> SomeDivergePoint (Just (Qu.coerceQuant nd))

data NoDivergePointProof arch tp where
  NoDivergePointProof :: (Qu.IsExistsOr tp Qu.AllK, KnownRepr Qu.QuantRepr tp) => NoDivergePointProof arch tp

noDivergePointProof :: DivergePoint arch tp -> Maybe (NoDivergePointProof arch tp)
noDivergePointProof = \case
  NoDivergePointCtor -> Just NoDivergePointProof
  SomeDivergePoint Nothing -> Just NoDivergePointProof
  _ -> Nothing

pattern NoDivergePoint :: forall arch tp. () => (KnownRepr Qu.QuantRepr tp, Qu.IsExistsOr tp Qu.AllK) => DivergePoint arch tp
pattern NoDivergePoint <- (noDivergePointProof -> Just NoDivergePointProof) where
  NoDivergePoint = case knownRepr :: Qu.QuantRepr tp of
    Qu.QuantAllRepr -> NoDivergePointCtor
    Qu.QuantSomeRepr -> SomeDivergePoint Nothing

{-# COMPLETE NoDivergePoint, DivergePoint #-}

divergePointNode :: DivergePoint arch tp -> Maybe (GraphNode' arch Qu.AllK)
divergePointNode = \case
  DivergePoint nd -> Just nd
  NoDivergePoint -> Nothing

divergePoint :: CallingContext' arch tp -> Maybe (GraphNode' arch Qu.AllK)
divergePoint cctx = divergePointNode $ divergePoint' cctx


-- | Additional context used to distinguish function calls
--   "Freezing" one binary in a node indicates that it should not continue
--   execution until the other binary has returned
data CallingContext' arch (tp :: Qu.QuantK PB.WhichBinary) = CallingContext' { ctxAncestors :: [PB.BlockPair arch], divergePoint' :: DivergePoint arch tp }
  deriving (Eq, Ord)

type CallingContext arch = CallingContext' arch Qu.ExistsK

data CallingContextProof arch tp where
  CallingContextProof :: (Qu.IsExistsOr tp2 tp1, KnownRepr Qu.QuantRepr tp1, KnownRepr Qu.QuantRepr tp2) => [PB.BlockPair arch] -> DivergePoint arch tp1 -> CallingContextProof arch tp2

callingContextProof :: CallingContext' arch tp -> CallingContextProof arch tp
callingContextProof cctx = let dp = divergePoint' cctx in case dp of
  DivergePoint{} -> CallingContextProof (ctxAncestors cctx) dp
  NoDivergePoint -> CallingContextProof (ctxAncestors cctx) dp

pattern CallingContext :: forall arch tp2. () => forall tp1. (Qu.IsExistsOr tp2 tp1, KnownRepr Qu.QuantRepr tp2, KnownRepr Qu.QuantRepr tp1) => [PB.BlockPair arch] -> DivergePoint arch tp1 -> CallingContext' arch tp2
pattern CallingContext blks dp <- (callingContextProof -> CallingContextProof blks dp) where
  CallingContext blks (dp :: DivergePoint arch tp1) = case Qu.isExistsOr @_ @tp2 @tp1 of
    Qu.ExistsOrExists -> case dp of
      DivergePoint nd -> CallingContext' blks (SomeDivergePoint (Just (Qu.coerceQuant nd)))
      NoDivergePoint -> CallingContext' blks (SomeDivergePoint Nothing)
    Qu.ExistsOrRefl -> CallingContext' blks dp


{-# COMPLETE CallingContext #-}

instance PA.ValidArch arch => Pretty (CallingContext' arch qbin) where
  pretty (CallingContext bps mdivisionPoint) =
    let
      bs = [ pretty bp | bp <- bps ]
      divP = case mdivisionPoint of
        DivergePoint _p -> [] -- ["Diverged at:", pretty p] -- too noisy
        NoDivergePoint -> []
    in sep (((zipWith (<+>) ( "via:" : repeat "<-") bs)) ++ divP)

instance PA.ValidArch arch => JSON.ToJSON (CallingContext' arch qbin) where
  toJSON (CallingContext bps mdivisionPoint) = JSON.object [ "ancestors" JSON..= bps, "divergedAt" JSON..= divergePointNode mdivisionPoint]

getDivergePoint :: GraphNode arch -> Maybe (GraphNode arch)
getDivergePoint nd = fmap Qu.coerceQuant $ getDivergePoint' nd

getDivergePoint' :: GraphNode' arch qbin -> Maybe (GraphNode' arch Qu.AllK)
getDivergePoint' nd = case nodeContext nd of
  CallingContext _ (DivergePoint dp) -> Just dp
  CallingContext _ NoDivergePoint -> Nothing

rootEntry :: PPa.PatchPair (PB.ConcreteBlock arch) -> NodeEntry arch
rootEntry pPair = NodeEntry (CallingContext [] (SomeDivergePoint Nothing)) pPair

rootReturn :: PPa.PatchPair (PB.FunctionEntry arch) -> NodeReturn arch
rootReturn pPair = NodeReturn (CallingContext [] (SomeDivergePoint Nothing)) pPair

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
mkNextContext :: Quant a (bin :: QuantK PB.WhichBinary) -> CallingContext' arch bin -> CallingContext' arch bin
mkNextContext q cctx = case q of
  Qu.All{} -> dropDivergePoint cctx
  Qu.Single{} -> cctx
 
dropDivergePoint :: Qu.IsExistsOr qbin Qu.AllK => CallingContext' arch qbin -> CallingContext' arch qbin
dropDivergePoint  (CallingContext cctx _) = CallingContext cctx NoDivergePointCtor

mkNodeEntry :: NodeEntry arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry node pPair = NodeEntry (mkNextContext pPair (graphNodeContext node)) pPair

mkNodeEntry' :: GraphNode arch -> PB.BlockPair arch -> NodeEntry arch
mkNodeEntry' (GraphNode ne) pPair = mkNodeEntry ne pPair
mkNodeEntry' (ReturnNode node) pPair = NodeEntry (mkNextContext pPair (returnNodeContext node)) pPair

mkNodeReturn :: NodeEntry arch -> PB.FunPair arch -> NodeReturn arch
mkNodeReturn node fPair = NodeReturn (mkNextContext fPair (graphNodeContext node)) fPair

mkMergedNodeEntry :: 
  GraphNode' arch Qu.AllK -> 
  PB.ConcreteBlock arch PB.Original ->
  PB.ConcreteBlock arch PB.Patched -> 
  NodeEntry' arch Qu.AllK
mkMergedNodeEntry nd blkO blkP = NodeEntry (CallingContext cctx NoDivergePoint) (Qu.All $ \case PB.OriginalRepr -> blkO; PB.PatchedRepr -> blkP)
  where
    CallingContext cctx _ = nodeContext nd

mkMergedNodeReturn :: 
  GraphNode' arch Qu.AllK -> 
  PB.FunctionEntry arch PB.Original ->
  PB.FunctionEntry arch PB.Patched -> 
  NodeReturn' arch Qu.AllK
mkMergedNodeReturn nd fnO fnP = NodeReturn (CallingContext cctx NoDivergePoint) (Qu.All $ \case PB.OriginalRepr -> fnO; PB.PatchedRepr -> fnP)
  where
    CallingContext cctx _ = nodeContext nd

-- | Project the given 'NodeEntry' into a singleton node for the given binary
toSingleNode:: forall m arch bin qbin. PPa.PatchPairM m => PB.WhichBinaryRepr bin -> NodeEntry' arch qbin -> m (NodeEntry arch)
toSingleNode bin divergedAt = toSingleGraphNode bin (GraphNode divergedAt) >>= \case
  GraphNode nd -> return nd
  _ -> PPa.throwPairErr

toSingleGraphNode :: forall m arch bin qbin. PPa.PatchPairM m => PB.WhichBinaryRepr bin -> GraphNode' arch qbin -> m (GraphNode arch)
toSingleGraphNode bin node = withKnownBin node $ withRepr bin $ case Qu.convertQuant node of
  Just (nd :: GraphNode' arch Qu.AllK) | (sgn :: SingleGraphNode arch bin) <- Qu.coerceQuant nd -> return $ Qu.coerceToExists sgn
  Nothing -> case Qu.convertQuant node of
    Just (nd :: SingleGraphNode arch bin) -> return $ Qu.coerceToExists nd
    Nothing -> PPa.throwPairErr


  
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
  | (ctxAncestors ctx1 == ctxAncestors ctx2)
  , blks1 == blks2
  = True
eqUptoDivergePoint (ReturnNode (NodeReturn ctx1 blks1)) (ReturnNode (NodeReturn ctx2 blks2))
  | (ctxAncestors ctx1 == ctxAncestors ctx2)
  , blks1 == blks2
  = True
eqUptoDivergePoint _ _ = False


toTwoSidedNode :: PPa.PatchPairM m => GraphNode' arch qbin -> m (GraphNode' arch Qu.AllK)
toTwoSidedNode nd = withKnownBin nd $ case Qu.convertQuant nd of
  Just (nd' :: GraphNode' arch Qu.AllK) -> return nd'
  Nothing -> PPa.throwPairErr

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
  PA.ValidArch arch => GraphNode' arch qbin -> String -> Doc a
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

pattern SingleNodeEntry :: CallingContext' arch (Qu.OneK bin) -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
pattern SingleNodeEntry cctx blk <- ((\l -> case l of NodeEntry cctx (Qu.Single _ blk) -> (cctx,blk)) -> (cctx,blk))
  where
    SingleNodeEntry cctx blk = NodeEntry cctx (withRepr (PB.blockBinRepr blk) $ Qu.Single (PB.blockBinRepr blk) blk)

{-# COMPLETE SingleNodeEntry #-}

singleEntryBin :: SingleNodeEntry arch bin -> PB.WhichBinaryRepr bin
singleEntryBin (nodeEntryRepr -> Qu.QuantOneRepr repr) = repr

singleNodeAddr :: SingleNodeEntry arch bin -> PPa.WithBin (PAd.ConcreteAddress arch) bin
singleNodeAddr se = PPa.WithBin (singleEntryBin se) (PB.concreteAddress (singleNodeBlock se))

mkSingleNodeEntry :: SingleNodeEntry arch bin -> PB.ConcreteBlock arch bin -> SingleNodeEntry arch bin
mkSingleNodeEntry node blk = SingleNodeEntry (graphNodeContext node) blk


singleNodeDivergePoint :: SingleGraphNode arch bin -> GraphNode' arch Qu.AllK
singleNodeDivergePoint sgn = case divergePoint' (nodeContext sgn) of
  DivergePoint nd -> nd

singleNodeDivergence :: SingleNodeEntry arch bin -> GraphNode' arch Qu.AllK
singleNodeDivergence sne = singleNodeDivergePoint (GraphNode sne)


asSingleNodeEntry :: PPa.PatchPairM m => NodeEntry' arch qbin -> m (Some (Qu.AsSingle (NodeEntry' arch)))
asSingleNodeEntry nd = asSingleNode (GraphNode nd) >>= \case
  Some (Qu.AsSingle (GraphNode nd')) -> return $ Some (Qu.AsSingle nd')
  _ -> PPa.throwPairErr

asSingleNode:: PPa.PatchPairM m => GraphNode' arch qbin -> m (Some (Qu.AsSingle (GraphNode' arch)))
asSingleNode nd = case graphNodeBlocks nd of
  Qu.All{} -> PPa.throwPairErr
  Qu.Single (repr :: PB.WhichBinaryRepr bin) _ -> withRepr repr $ case Qu.convertQuant nd of
    Just (nd' :: GraphNode' arch (Qu.OneK bin)) -> return $ Some (Qu.AsSingle nd')
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
  NodeEntry' arch qbin -> 
  m (SingleNodeEntry arch bin)
toSingleNodeEntry bin ne = do
  case toSingleNode bin ne of
    Just ne' -> do
      Some (Qu.AsSingle sne) <- asSingleNodeEntry ne'
      case testEquality (nodeEntryRepr sne) (Qu.QuantOneRepr bin) of
        Just Refl -> return sne
        Nothing -> PPa.throwPairErr
    _ -> PPa.throwPairErr

singleToNodeEntry :: SingleNodeEntry arch bin -> NodeEntry arch
singleToNodeEntry sne = case singleToGraphNode (GraphNode sne) of
  GraphNode sne' -> sne'
  ReturnNode _ -> error "singleToNodeEntry: unexpected node kind swap" 

singleToGraphNode :: SingleGraphNode arch bin -> GraphNode arch
singleToGraphNode sgn = withRepr (singleNodeRepr sgn) $ Qu.coerceQuant sgn

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
combineSingleEntries node1 node2 = do
  let ndPair = PPa.mkPair (singleEntryBin node1) (Qu.AsSingle node1) (Qu.AsSingle node2)
  Qu.AsSingle nodeO <- PPa.get PB.OriginalRepr ndPair
  Qu.AsSingle nodeP <- PPa.get PB.PatchedRepr ndPair
  -- it only makes sense to combine nodes that share a divergence point
  let divergeO = singleNodeDivergence nodeO
  let divergeP = singleNodeDivergence nodeP
  guard $ divergeO == divergeP
  let ne = mkMergedNodeEntry divergeO (singleNodeBlock nodeO) (singleNodeBlock nodeP)
  GraphNode ne' <- return $ Qu.coerceToExists (GraphNode ne)
  return ne'

type SingleNodeReturn arch bin = NodeReturn' arch (Qu.OneK bin)

pattern SingleNodeReturn :: CallingContext' arch (Qu.OneK bin) -> PB.FunctionEntry arch bin -> SingleNodeReturn arch bin
pattern SingleNodeReturn cctx fn <- ((\l -> case l of NodeReturn cctx (Qu.Single _ fn) -> (cctx,fn)) -> (cctx,fn))
  where
    SingleNodeReturn cctx fn = NodeReturn cctx (withRepr (PB.functionBinRepr fn) $ Qu.Single (PB.functionBinRepr fn) fn)

type SingleGraphNode arch bin = GraphNode' arch (Qu.OneK bin)

singleNodeRepr :: SingleGraphNode arch bin -> PB.WhichBinaryRepr bin
singleNodeRepr sgn = case nodeRepr sgn of Qu.QuantOneRepr repr -> repr