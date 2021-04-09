{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Interactive.Render.Proof (
    renderProof
  , renderProofApp
  ) where

import qualified Data.Aeson as JSON
import qualified Data.Foldable as F
import qualified Data.Functor.Const as C
import qualified Data.HashMap.Strict as HMS
import qualified Data.Macaw.CFG as MC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy (Proxy(..))
import qualified Data.Text as T
import qualified Data.Vector as DV
import qualified Foreign.JavaScript as FJ
import           Graphics.UI.Threepenny ( (#), (#+) )
import qualified Graphics.UI.Threepenny as TP
import qualified Lang.Crucible.LLVM.MemModel as CLM
import           Numeric.Natural ( Natural )
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPT
import qualified What4.Interface as WI

import qualified Pate.Event as PE
import qualified Pate.MemCell as PMC
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT

import qualified Interactive.State as IS

pp :: PP.Doc ann -> T.Text
pp = PPT.renderStrict . PP.layoutCompact

ppStatus :: PPr.VerificationStatus a -> PP.Doc ann
ppStatus st =
  case st of
    PPr.Unverified -> PP.pretty "Unverified"
    PPr.VerificationSkipped -> PP.pretty "Skipped"
    PPr.VerificationSuccess -> PP.pretty "Success"
    PPr.VerificationFail {} -> PP.pretty "Fail"

ppAppTag :: PPr.ProofApp prf node tp -> PP.Doc ann
ppAppTag app =
  case app of
    PPr.ProofBlockSlice {} -> PP.pretty "Slice"
    PPr.ProofFunctionCall {} -> PP.pretty "Call"
    PPr.ProofTriple {} -> PP.pretty "Triple"
    PPr.ProofStatus st -> PP.pretty "Status" <> PP.parens (ppStatus st)
    PPr.ProofDomain {} -> PP.pretty "Domain"

nodeLabel
  :: PE.BlocksPair arch
  -> PPr.ProofApp prf (PPr.ProofNonceExpr prf) tp
  -> T.Text
nodeLabel (PT.PatchPair (PE.Blocks ob _) (PE.Blocks pb _)) app =
  pp (mconcat [ ppAppTag app
              , PP.line
              , mconcat [ PP.pretty (PT.concreteAddress ob)
                        , PP.pretty "/"
                        , PP.pretty (PT.concreteAddress pb)
                        ]
              ])

nodeId :: PPr.ProofNonce prf tp -> Natural
nodeId = PPr.proofNonceValue

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
    content = HMS.fromList [ (T.pack "id", JSON.Number (fromIntegral (nodeId thisNonce)))
                           , (T.pack "text", JSON.String (pp (PP.pretty (nodeLabel blockPair app))))
                           , (T.pack "nodeType", JSON.String (pp (ppAppTag app)))
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
                           , (T.pack "source", JSON.String (pp (PP.pretty srcLabel)))
                           , (T.pack "target", JSON.String (pp (PP.pretty tgtLabel)))
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
    content = HMS.fromList [ (T.pack "id", JSON.Number (fromIntegral (nodeId src)))
                           , (T.pack "text", JSON.String (T.pack "Proof Root"))
                           ]

initializeGraph :: FJ.JSObject -> String -> JSON.Value -> TP.JSFunction ()
initializeGraph clickCallback divId graphData =
  TP.ffi "initializeGraphIn(%1, %2, proofGraphConfig(), %3)" clickCallback divId graphData

renderProof
  :: FJ.JSObject
  -> String
  -> IS.ProofTree arch
  -> (TP.UI TP.Element, TP.UI ())
renderProof clickCallback divId (IS.ProofTree _sym proofTreeNodes _) =
  (TP.div # TP.set TP.id_ divId, TP.runFunction (initializeGraph clickCallback divId (JSON.Object graph)))
  where
    nodes = F.foldl' blockNode Map.empty (MapF.elems proofTreeNodes)
    edges = F.foldl' blockEdges [] (MapF.elems proofTreeNodes)
    roots = F.foldl' (generateRoot proofTreeNodes) Map.empty (MapF.elems proofTreeNodes)
    graph = HMS.fromList [ (T.pack "nodes", JSON.Array (DV.fromList (Map.elems (nodes <> roots))))
                         , (T.pack "edges", JSON.Array (DV.fromList edges))
                         ]

-- | Render a row in the register domain table if necessary
--
-- If the predicate is syntactically false, the register is not in the domain
-- and we do not need to render an entry. Otherwise, render the register and an
-- (expandable) view of the formula.
--
-- If the predicate is syntactically true, the register is always in the domain
-- and no additional information about the formula is displayed for simplicity.
renderProofRegisterDomain
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => proxy prf
  -> MapF.Pair (PPr.ProofRegister prf) (C.Const (PPr.ProofPredicate prf))
  -> Maybe (TP.UI TP.Element)
renderProofRegisterDomain _ (MapF.Pair reg (C.Const predicate))
  | Just False <- WI.asConstantPred predicate = Nothing
  | Just True <- WI.asConstantPred predicate = Just (TP.string (PC.showF reg))
  | otherwise = Just $ TP.row [ TP.string (PC.showF reg)
                              , TP.string (T.unpack (pp (WI.printSymExpr predicate)))
                              ]

renderProofMemoryDomain
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     )
  => PPr.ProofPredicate prf
  -> MapF.Pair (PPr.ProofMemCell prf) (C.Const (PPr.ProofPredicate prf))
  -> Maybe (TP.UI TP.Element)
renderProofMemoryDomain polarity (MapF.Pair memCell (C.Const predicate))
  | WI.asConstantPred polarity /= WI.asConstantPred predicate =
    Just $ TP.row [ TP.string (show (PN.natValue (PMC.cellWidth memCell)) ++ " bytes at ")
                  , TP.pre # TP.set TP.text (T.unpack (pp (CLM.ppPtr (PMC.cellPtr memCell))))
                  ]
  | otherwise = Nothing

renderDomainExpr
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => PPr.ProofNonceExpr prf PPr.ProofDomainType
  -> TP.UI TP.Element
renderDomainExpr (PPr.ProofNonceExpr _ _ app) = renderDomainApp app

ppPolarityDescription :: WI.IsExpr e => e WI.BaseBoolType -> PP.Doc ann
ppPolarityDescription predicate
  | Just False <- WI.asConstantPred predicate =
      PP.pretty "These locations are in the domain of this slice"
  | Just True <- WI.asConstantPred predicate =
      PP.pretty "All locations other than these are in the domain of this slice"
  | otherwise = PP.pretty "Symbolic polarity"

renderDomainApp
  :: forall prf node sym arch
   . ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => PPr.ProofApp prf node PPr.ProofDomainType
  -> TP.UI TP.Element
renderDomainApp (PPr.ProofDomain regs stack mem _context) =
  TP.column [ TP.h4 #+ [TP.string "Registers"]
            , TP.column (mapMaybe (renderProofRegisterDomain (Proxy @prf)) (MapF.toList (MC.regStateMap regs)))
            , TP.h4 #+ [TP.string "Stack Memory"]
            , TP.string (T.unpack (pp (ppPolarityDescription (PPr.prfMemoryDomainPolarity stack))))
            , TP.column (mapMaybe (renderProofMemoryDomain (PPr.prfMemoryDomainPolarity stack)) (MapF.toList (PPr.prfMemoryDomain stack)))
            , TP.h4 #+ [TP.string "Other Memory"]
            , TP.string (T.unpack (pp (ppPolarityDescription (PPr.prfMemoryDomainPolarity mem))))
            , TP.column (mapMaybe (renderProofMemoryDomain (PPr.prfMemoryDomainPolarity mem)) (MapF.toList (PPr.prfMemoryDomain mem)))
            ]

renderProofApp
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => PPr.ProofApp prf (PPr.ProofNonceExpr prf) tp
  -> TP.UI TP.Element
renderProofApp app =
  case app of
    PPr.ProofBlockSlice domain callees mret munknown transition ->
      TP.div #+ [ TP.string "Proof that the post-domain of this slice of the program is satisfied when this slice returns, assuming its precondition"
                ]
    PPr.ProofFunctionCall pre body cont ->
      TP.div #+ [ TP.string "Proof that a function call is valid given its preconditions"
                ]
    PPr.ProofTriple blocks pre post (PPr.ProofNonceExpr _ _ (PPr.ProofStatus status)) ->
      TP.column [ TP.string "A proof that block slices are equivalent (i.e., satisfy their postconditions) under their preconditions"
                , TP.h3 #+ [TP.string "Pre-domain"]
                , TP.string "These values are assumed to be equal in both the original and patched program at the start of this program slice"
                , renderDomainExpr pre
                , TP.h3 #+ [TP.string "Post-domain"]
                , TP.string "These values are asserted to be equal in both the original and patched program at the end of this program slice"
                , renderDomainExpr post
                , TP.h3 #+ [TP.string "Status"]
                , TP.string (T.unpack (pp (ppStatus status)))
                ]
    PPr.ProofStatus st ->
      TP.div #+ [ TP.string (T.unpack (pp (PP.pretty "Proof Status: " <> ppStatus st)))
                ]
    PPr.ProofDomain {} ->
      TP.column [ TP.string "The domain of an individual equivalence proof"
                , renderDomainApp app
                ]
