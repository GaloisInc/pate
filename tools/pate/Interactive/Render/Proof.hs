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

import qualified Pate.Arch as PA
import qualified Pate.Event as PE
import qualified Pate.MemCell as PMC
import qualified Pate.Panic as Panic
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT

import qualified Interactive.State as IS

pp :: PP.Doc ann -> T.Text
pp = PPT.renderStrict . PP.layoutCompact

ppStatus :: ( prf ~ PFI.ProofSym sym arch
            , WI.IsSymExprBuilder sym
            )
         => proxy prf
         -> PPr.VerificationStatus (PPr.ProofCounterExample prf, PPr.ProofPredicate prf)
         -> PP.Doc ann
ppStatus _ st =
  case st of
    PPr.Unverified -> PP.pretty "Unverified"
    PPr.VerificationSkipped -> PP.pretty "Skipped"
    PPr.VerificationSuccess -> PP.pretty "Success"
    PPr.VerificationFail (_cex, diffSummary)
      | Just False <- WI.asConstantPred diffSummary -> PP.pretty "Inequivalent"
      | otherwise -> PP.pretty "Conditional"

ppAppTag
  :: forall prf tp arch ann sym
   . ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce prf) (IS.ProofTreeNode arch prf)
  -> PPr.ProofNonceExpr prf tp
  -> PP.Doc ann
ppAppTag proofTreeNodes (PPr.ProofNonceExpr thisNonce (Some parentNonce) app) =
  case app of
    PPr.ProofBlockSlice {} -> PP.pretty "Slice"
    PPr.ProofFunctionCall {} -> PP.pretty "Call"
    PPr.ProofTriple {}
      | Just (IS.ProofTreeNode _blocks parentExpr _) <- MapF.lookup parentNonce proofTreeNodes ->
        case PPr.prfNonceBody parentExpr of
          PPr.ProofBlockSlice summaryTriple callNodes mRetTriple mUnknownTriple transition
            | Just PC.Refl <- PC.testEquality (PPr.prfNonce summaryTriple) thisNonce -> PP.pretty "Triple(SliceSummary)"
            | Just sliceReturnTriple <- mRetTriple
            , Just PC.Refl <- PC.testEquality (PPr.prfNonce sliceReturnTriple) thisNonce -> PP.pretty "Triple"
            | Just unknownTriple <- mUnknownTriple
            , Just PC.Refl <- PC.testEquality (PPr.prfNonce unknownTriple) thisNonce -> PP.pretty "Triple(Unknown)"
            | otherwise -> Panic.panic Panic.Visualizer "ppAppTag" ["Invalid parent connection to a ProofBlockSlice for a ProofTriple: " ++ show thisNonce]
          PPr.ProofFunctionCall funcPre _callBody _continuation
            | Just PC.Refl <- PC.testEquality (PPr.prfNonce funcPre) thisNonce -> PP.pretty "Triple(FunctionPredomain)"
            | otherwise -> Panic.panic Panic.Visualizer "ppAppTag" ["Unexpected parent for a ProofTriple: " ++ show (thisNonce, parentNonce)]
          PPr.ProofTriple {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofTriple is not a possible parent component for a ProofTriple"]
          PPr.ProofStatus {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofStatus is not a possible parent component for a ProofTriple"]
          PPr.ProofDomain {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofDomain is not a possible parent component for a ProofTriple"]
      | otherwise -> error ("Missing parent for node " ++ show thisNonce ++ "(" ++ show parentNonce ++ ")")
    PPr.ProofStatus st -> PP.pretty "Status" <> PP.parens (ppStatus (Proxy @prf) st)
    PPr.ProofDomain {} -> PP.pretty "Domain"

nodeLabel
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce prf) (IS.ProofTreeNode arch prf)
  -> PE.BlocksPair arch
  -> PPr.ProofNonceExpr prf tp
  -> T.Text
nodeLabel proofTreeNodes (PT.PatchPair (PE.Blocks ob _) (PE.Blocks pb _)) expr =
  pp (mconcat [ ppAppTag proofTreeNodes expr
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
-- The label should be minimal so that we don't overwhelm the display. In the
-- 'Interactive' module, we set up some callbacks to allow users to ask for more
-- information on individual nodes.
blockNode
  :: ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce prf) (IS.ProofTreeNode arch prf)
  -> Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
  -> Some (IS.ProofTreeNode arch prf)
  -> Map.Map (Some (PPr.ProofNonce prf)) JSON.Value
blockNode proofTreeNodes m (Some (IS.ProofTreeNode blockPair expr@(PPr.ProofNonceExpr thisNonce _parentNonce app) _tm)) =
  Map.insert (Some thisNonce) (JSON.Object node) m
  where
    node = HMS.fromList [ (T.pack "data", JSON.Object content) ]
    content = HMS.fromList [ (T.pack "id", JSON.Number (fromIntegral (nodeId thisNonce)))
                           , (T.pack "text", JSON.String (pp (PP.pretty (nodeLabel proofTreeNodes blockPair expr))))
                           , (T.pack "nodeType", JSON.String (pp (ppAppTag proofTreeNodes expr)))
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

-- | This is a foreign function call to the Javascript that initializes the graph rendering in the provided div
initializeGraph :: FJ.JSObject -> String -> JSON.Value -> TP.JSFunction ()
initializeGraph clickCallback divId graphData =
  TP.ffi "initializeGraphIn(%1, %2, proofGraphConfig(), %3)" clickCallback divId graphData

-- | This returns two things: the UI element into which the proof display will
-- be rendered and a JS function call that needs to be invoked to start
-- rendering on the client side
renderProof
  :: FJ.JSObject
  -> String
  -> IS.ProofTree arch
  -> (TP.UI TP.Element, TP.UI ())
renderProof clickCallback divId (IS.ProofTree _sym proofTreeNodes _) =
  (TP.div # TP.set TP.id_ divId, TP.runFunction (initializeGraph clickCallback divId (JSON.Object graph)))
  where
    nodes = F.foldl' (blockNode proofTreeNodes) Map.empty (MapF.elems proofTreeNodes)
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

renderCounterexample
  :: ( prf ~ PFI.ProofSym sym arch
     , PA.ValidArch arch
     )
  => PPr.ProofCounterExample prf
  -> TP.UI TP.Element
renderCounterexample ineqRes =
  TP.pre # TP.set TP.text (T.unpack (pp (PP.pretty ineqRes)))

renderProofApp
  :: forall prf sym arch tp
   . ( prf ~ PFI.ProofSym sym arch
     , WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     , PA.ValidArch arch
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
                , TP.string (T.unpack (pp (ppStatus (Proxy @prf) status)))
                ]
    PPr.ProofStatus st ->
      case st of
        PPr.VerificationFail (cex, diffSummary)
          | Just False <- WI.asConstantPred diffSummary ->
            TP.column [ TP.string (T.unpack (pp (PP.pretty "Proof Status: " <> ppStatus (Proxy @prf) st)))
                      , TP.string "The patched program always exhibits different behavior if this program location is reached"
                      , TP.string "Counterexample:"
                      , renderCounterexample cex
                      ]
          | otherwise ->
            TP.column [ TP.string (T.unpack (pp (PP.pretty "Proof Status: " <> ppStatus (Proxy @prf) st)))
                      , TP.string "The patched program exhibits identical behavior to the original under the following conditions:"
                      , TP.string (T.unpack (pp (WI.printSymExpr diffSummary)))
                      , TP.string "Counterexample:"
                      , renderCounterexample cex
                      ]
        _ -> TP.div #+ [ TP.string (T.unpack (pp (PP.pretty "Proof Status: " <> ppStatus (Proxy @prf) st)))
                       ]
    PPr.ProofDomain {} ->
      TP.column [ TP.string "The domain of an individual equivalence proof"
                , renderDomainApp app
                ]
