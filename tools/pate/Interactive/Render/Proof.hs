{-# LANGUAGE GADTs #-}
module Interactive.Render.Proof (
  renderProof
  ) where

import qualified Data.Aeson as JSON
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HMS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import qualified Data.Vector as DV
import           Graphics.UI.Threepenny ( (#) )
import qualified Graphics.UI.Threepenny as TP
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPT

import qualified Pate.Event as PE
import qualified Pate.Proof as PPr
import qualified Pate.Types as PT

import qualified Interactive.State as IS

pp :: PP.Doc ann -> T.Text
pp = PPT.renderStrict . PP.layoutCompact

ppApp :: PPr.ProofApp prf node tp -> PP.Doc ann
ppApp app =
  case app of
    PPr.ProofBlockSlice {} -> PP.pretty "ProofBlockSlice"
    PPr.ProofFunctionCall {} -> PP.pretty "ProofFunctionCall"
    PPr.ProofTriple {} -> PP.pretty "ProofTriple"
    PPr.ProofStatus {} -> PP.pretty "ProofStatus"
    PPr.ProofDomain {} -> PP.pretty "ProofDomain"

nodeLabel
  :: PE.BlocksPair arch
  -> PPr.ProofApp prf (PPr.ProofNonceExpr prf) tp
  -> T.Text
nodeLabel (PT.PatchPair (PE.Blocks ob _) (PE.Blocks pb _)) app =
  pp (mconcat [ ppApp app
              , PP.parens (mconcat [ PP.viaShow (PT.concreteAddress ob)
                                   , PP.pretty "/"
                                   , PP.viaShow (PT.concreteAddress pb)
                                   ])
              ])

nodeId :: PPr.ProofNonce prf tp -> T.Text
nodeId = T.pack . show . PPr.proofNonceValue

-- | Render a proof node as a JSON object that can be used to construct the graph
--
-- The label should be minimal, but FIXME we need to include some extra data
-- that can be used for a detailed view of the node
blockNode
  :: Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
  -> Some (IS.ProofTreeNode arch prf)
  -> Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
blockNode m (Some (IS.ProofTreeNode blockPair (PPr.ProofNonceExpr thisNonce _parentNonce app) _tm)) =
  Map.insert (Some thisNonce) (JSON.Object node) m
  where
    node = HMS.fromList [ (T.pack "data", JSON.Object content) ]
    content = HMS.fromList [ (T.pack "id", JSON.String (nodeId thisNonce))
                           , (T.pack "text", JSON.String (nodeLabel blockPair app))
                           ]

blockEdges
  :: [JSON.Value]
  -> Some (IS.ProofTreeNode arch prf)
  -> [JSON.Value]
blockEdges edges (Some (IS.ProofTreeNode _ (PPr.ProofNonceExpr thisNonce (Some parentNonce) _) _tm)) =
  JSON.Object (HMS.fromList [(T.pack "data", JSON.Object content)]) : edges
  where
    srcLabel = nodeId parentNonce
    tgtLabel = nodeId thisNonce
    edgeLabel = pp (PP.pretty srcLabel <> PP.pretty "/" <> PP.pretty tgtLabel)
    content = HMS.fromList [ (T.pack "id", JSON.String edgeLabel)
                           , (T.pack "source", JSON.String srcLabel)
                           , (T.pack "target", JSON.String tgtLabel)
                           ]

-- | If there is an edge with a source that is not in the list of nodes,
-- generate a synthetic root node for it
--
-- We could in principle emit an extra event from the verifier to record the
-- nonce of the root node directly, but the quantification of the scope variable
-- in the nonce (and the proof type) make that a bit complicated.
generateRoot
  :: MapF.MapF (PPr.ProofNonce prf) (IS.ProofTreeNode arch prf)
  -> Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
  -> Some (IS.ProofTreeNode arch prf)
  -> Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
generateRoot proofTree newRoots (Some (IS.ProofTreeNode _ (PPr.ProofNonceExpr _ (Some src) _) _))
  | Just _ <- MapF.lookup src proofTree = newRoots
  | otherwise = Map.insert (Some src) (JSON.Object node) newRoots
  where
    node = HMS.fromList [ (T.pack "data", JSON.Object content) ]
    content = HMS.fromList [ (T.pack "id", JSON.String (nodeId src))
                           , (T.pack "text", JSON.String (T.pack "Proof Root"))
                           ]

initializeGraph :: String -> JSON.Value -> TP.JSFunction ()
initializeGraph divId graphData = TP.ffi "initializeGraphIn(%1, %2)" divId graphData

renderProof
  :: String
  -> IS.ProofTree arch
  -> (TP.UI TP.Element, TP.UI ())
renderProof divId (IS.ProofTree _sym proofTreeNodes) =
  (TP.div # TP.set TP.id_ divId, TP.runFunction (initializeGraph divId (JSON.Object graph)))
  where
    nodes = F.foldl' blockNode Map.empty (MapF.elems proofTreeNodes)
    edges = F.foldl' blockEdges [] (MapF.elems proofTreeNodes)
    roots = F.foldl' (generateRoot proofTreeNodes) Map.empty (MapF.elems proofTreeNodes)
    graph = HMS.fromList [ (T.pack "nodes", JSON.Array (DV.fromList (Map.elems (nodes <> roots))))
                         , (T.pack "edges", JSON.Array (DV.fromList edges))
                         ]
