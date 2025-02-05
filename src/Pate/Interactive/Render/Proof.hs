{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Pate.Interactive.Render.Proof (
    renderProof
  , renderProofApp
  ) where

import           Control.Lens ((^.))
import           Control.Monad ( guard )
import qualified Data.Aeson as JSON
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import           Data.Functor.Const
import qualified Compat.Aeson as HMS

import qualified Data.IntervalMap.Interval as DII
import qualified Data.List as DL
import qualified Data.Macaw.CFG as MC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes, mapMaybe )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as TFC
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

import qualified Pate.Arch as PAr
import qualified Pate.Block as PB
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Event as PE
import qualified Pate.Ground as PG
import qualified Pate.MemCell as PMC
import qualified Pate.Panic as Panic
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Verification.MemoryLog as PVM

import qualified Pate.Interactive.State as IS

pp :: PP.Doc ann -> T.Text
pp = PPT.renderStrict . PP.layoutCompact

ppStatus :: ( WI.IsSymExprBuilder sym
            )
         => PPr.VerificationStatus sym arch
         -> PP.Doc ann
ppStatus st =
  case st of
    PPr.Unverified -> PP.pretty "Unverified"
    PPr.VerificationSkipped -> PP.pretty "Skipped"
    PPr.VerificationSuccess -> PP.pretty "Success"
    PPr.VerificationFail _cex diffSummary
      | Just False <- WI.asConstantPred (PPr.condEqPred diffSummary) -> PP.pretty "Inequivalent"
      | otherwise -> PP.pretty "Conditional"

ppAppTag
  :: forall tp arch ann sym
   . ( WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce sym) (IS.ProofTreeNode sym arch)
  -> PPr.ProofNonceExpr sym arch tp
  -> PP.Doc ann
ppAppTag proofTreeNodes (PPr.ProofNonceExpr thisNonce (Some parentNonce) app) =
  case app of
    PPr.ProofBlockSlice {} -> PP.pretty "Slice"
    PPr.ProofFunctionCall {} -> PP.pretty "Call"
    PPr.ProofTriple {}
      | Just (IS.ProofTreeNode _blocks parentExpr _) <- MapF.lookup parentNonce proofTreeNodes ->
        case PPr.prfNonceBody parentExpr of
          PPr.ProofBlockSlice summaryTriple _callNodes mRetTriple mUnknownTriple _transition
            | Just PC.Refl <- PC.testEquality (PPr.prfNonce summaryTriple) thisNonce -> PP.pretty "Triple(SliceSummary)"
            | Just sliceReturnTriple <- mRetTriple
            , Just PC.Refl <- PC.testEquality (PPr.prfNonce sliceReturnTriple) thisNonce -> PP.pretty "Triple"
            | Just unknownTriple <- mUnknownTriple
            , Just PC.Refl <- PC.testEquality (PPr.prfNonce unknownTriple) thisNonce -> PP.pretty "Triple(Unknown)"
            | otherwise -> Panic.panic Panic.Visualizer "ppAppTag" ["Invalid parent connection to a ProofBlockSlice for a ProofTriple: " ++ show thisNonce]
          PPr.ProofFunctionCall funcPre _callBody _continuation _md
            | Just PC.Refl <- PC.testEquality (PPr.prfNonce funcPre) thisNonce ->
              PP.pretty "Triple" <> PP.parens (PP.pretty "FunctionPredomain")
            | otherwise -> Panic.panic Panic.Visualizer "ppAppTag" ["Unexpected parent for a ProofTriple: " ++ show (thisNonce, parentNonce)]
          PPr.ProofTriple {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofTriple is not a possible parent component for a ProofTriple"]
          PPr.ProofInlinedCall {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofInlinedCall is not a possible parent component for a ProofTriple"]
          PPr.ProofDomain {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofDomain is not a possible parent component for a ProofTriple"]
          PPr.ProofStatus {} -> Panic.panic Panic.Visualizer "ppAppTag" ["ProofStatus is not a possible parent component for a ProofTriple"]
      | otherwise ->
        -- See Note [Pending Nodes]
        PP.pretty "<Pending>"
    PPr.ProofStatus st -> PP.pretty "Status" <> PP.parens (ppStatus st)
    PPr.ProofDomain {} -> PP.pretty "Domain"
    PPr.ProofInlinedCall {} -> PP.pretty "Inlined Call"

nodeLabel
  :: ( WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce sym) (IS.ProofTreeNode sym arch)
  -> PE.BlocksPair arch
  -> PPr.ProofNonceExpr sym arch tp
  -> T.Text
nodeLabel _ (PPa.PatchPairSingle{}) _ = PPa.handleSingletonStub
nodeLabel proofTreeNodes (PPa.PatchPair (PE.Blocks _ ob _) (PE.Blocks _ pb _)) expr =
  pp (mconcat [ ppAppTag proofTreeNodes expr
              , PP.line
              , mconcat [ PP.pretty (PB.concreteAddress ob)
                        , PP.pretty "/"
                        , PP.pretty (PB.concreteAddress pb)
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
  :: ( WI.IsSymExprBuilder sym
     )
  => MapF.MapF (PPr.ProofNonce sym) (IS.ProofTreeNode sym arch)
  -> Map.Map (Some (PPr.ProofNonce sym)) JSON.Value
  -> Some (IS.ProofTreeNode sym arch)
  -> Map.Map (Some (PPr.ProofNonce sym)) JSON.Value
blockNode proofTreeNodes m (Some (IS.ProofTreeNode blockPair expr@(PPr.ProofNonceExpr thisNonce _parentNonce _app) _tm)) =
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
  :: MapF.MapF (PPr.ProofNonce sym) (IS.ProofTreeNode sym arch)
  -> Map.Map (Some (PPr.ProofNonce sym)) JSON.Value
  -> Some (IS.ProofTreeNode sym arch)
  -> Map.Map (Some (PPr.ProofNonce sym)) JSON.Value
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
  :: ( WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => Proxy sym
  -> (Some (MC.ArchReg arch), WI.Pred sym)
  -> Maybe (TP.UI TP.Element)
renderProofRegisterDomain _ (Some reg, predicate)
  | Just False <- WI.asConstantPred predicate = Nothing
  | Just True <- WI.asConstantPred predicate = Just (TP.string (PC.showF reg))
  | otherwise = Just $ TP.row [ TP.string (PC.showF reg)
                              , text (WI.printSymExpr predicate)
                              ]

renderProofMemoryDomain
  :: ( WI.IsSymExprBuilder sym
     )
  => (Some (PMC.MemCell sym arch), (WI.Pred sym))
  -> TP.UI TP.Element
renderProofMemoryDomain (Some memCell, _predicate) =
  TP.row [ TP.string (show (PN.natValue (PMC.cellWidth memCell)) ++ " bytes at ")
         , TP.pre # TP.set TP.text (T.unpack (pp (CLM.ppPtr (PMC.cellPtr memCell))))
         ]

renderDomainExpr
  :: ( WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => PPr.ProofNonceExpr sym arch PPr.ProofDomainType
  -> TP.UI TP.Element
renderDomainExpr (PPr.ProofNonceExpr _ _ (PPr.ProofDomain dom)) = renderDomain dom

text :: PP.Doc ann -> TP.UI TP.Element
text = TP.string . T.unpack . pp

renderDomain
  :: forall sym arch
   . ( WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     )
  => PED.EquivalenceDomain sym arch
  -> TP.UI TP.Element
renderDomain (PED.EquivalenceDomain regs stack mem _) =
  TP.column [ TP.h4 #+ [TP.string "Registers"]
            , TP.column (mapMaybe (renderProofRegisterDomain (Proxy @sym)) (PER.toList regs))
            , TP.h4 #+ [TP.string "Stack Memory"]
            , TP.column (map renderProofMemoryDomain (PEM.toList stack))
            , TP.h4 #+ [TP.string "Other Memory"]
            , TP.column (map renderProofMemoryDomain (PEM.toList mem))
            ]

-- | Render the pretty version of a register pair in a ground state
--
-- If both registers are zero, return Nothing so that they can be elided.
renderRegVal
  :: ( PAr.ValidArch arch
     , PG.IsGroundSym grnd
     )
  => PED.EquivalenceDomain grnd arch
  -> MC.ArchReg arch tp
  -> PPr.BlockSliceRegOp grnd tp
  -> Maybe (PAr.RegisterDisplay (PP.Doc ()))
renderRegVal domain reg regOp =
  case PPr.slRegOpRepr regOp of
    CLM.LLVMPointerRepr _ ->
      case vals of
        PPa.PatchPairC (PFI.GroundMacawValue obv) (PFI.GroundMacawValue pbv)
          | PFI.isGroundBVZero obv && PFI.isGroundBVZero pbv -> Nothing
          | otherwise -> Just prettySlotVal
        PPa.PatchPairSingle{} -> Just prettySlotVal
    _ -> Just prettySlotVal
  where
    vals = TFC.fmapFC (\(Const x) -> Const $ PFI.groundMacawValue x) $ PPr.slRegOpValues regOp

    ppDom =
      case PFI.regInGroundDomain (PED.eqDomainRegisters domain) reg of
        True -> PP.emptyDoc
        False -> PP.pretty "| Excluded"

    ppVals =
      case PG.groundValue $ PPr.slRegOpEquiv regOp of
        True -> PP.pretty (PPa.someC vals)
        False -> PPa.ppPatchPairC PP.pretty vals

    -- Use 'PAr.displayRegister' to find the display name of the register, while
    -- transforming that name with extra data inside of the resulting classifier
    -- container (to preserve sort order)
    prettySlotVal :: PAr.RegisterDisplay (PP.Doc ())
    prettySlotVal = (\rd -> PP.pretty rd <> PP.pretty ": " <> ppVals PP.<+> ppDom) <$> PAr.displayRegister reg

-- | Render a concrete (ground) register state for display in a counterexample
--
-- Note that this suppresses any excluded all-zero registers for cleanliness,
-- but it does report how many such registers were hidden.
renderRegisterState
  :: ( PAr.ValidArch arch
     , PG.IsGroundSym grnd
     )
  => PED.EquivalenceDomain grnd arch
  -> MC.RegState (MC.ArchReg arch) (PPr.BlockSliceRegOp grnd)
  -> TP.UI TP.Element
renderRegisterState domain regs =
  TP.column (TP.h3 #+ [TP.string "Registers"] : map TP.string shownRegs ++ [text hidden])
  where
    renderedRegs = map (\(MapF.Pair reg op) -> renderRegVal domain reg op) (MapF.toList (MC.regStateMap regs))
    shownRegs = reverse (DL.sort (fmap show (catMaybes (map PAr.fromRegisterDisplay (catMaybes renderedRegs)))))
    numHidden = length renderedRegs - length shownRegs

    hidden = PP.pretty "Eliding " <> PP.pretty numHidden <> PP.pretty " zero-valued registers"

renderMemCellVal
  :: ( PAr.ValidArch arch
     , PG.IsGroundSym grnd
     )
  => PED.EquivalenceDomain grnd arch
  -> PMC.MemCell grnd arch n
  -> PPr.BlockSliceMemOp grnd tp
  -> Maybe (PP.Doc a)
renderMemCellVal domain cell memOp = do
  guard (PG.groundValue $ PPr.slMemOpCond memOp)
  let vals = PPa.map (\(Const x) -> Const $ PFI.groundBV x) $ PPr.slMemOpValues memOp
  let ppDom = case PFI.cellInGroundDomain domain cell of
        True -> PP.emptyDoc
        False -> PP.pretty "| Excluded"
  let ppVals = case PG.groundValue $ PPr.slMemOpEquiv memOp of
        True -> PP.viaShow (PPa.someC vals)
        False -> PPa.ppPatchPairC PP.viaShow vals
  return (PFI.ppGroundCell cell <> PP.pretty ": " <> ppVals PP.<+> ppDom)

renderMemoryState
  :: ( PAr.ValidArch arch
     , PG.IsGroundSym grnd
     )
  => PED.EquivalenceDomain grnd arch
  -> MapF.MapF (PMC.MemCell grnd arch) (PPr.BlockSliceMemOp grnd)
  -> TP.UI TP.Element
renderMemoryState domain cells =
  TP.column (TP.h3 #+ [TP.string "Memory"] : map text entries)
  where
    entries = mapMaybe (\(MapF.Pair cell v) -> renderMemCellVal domain cell v) (MapF.toList cells)

renderIPs
  :: ( MC.RegisterInfo (MC.ArchReg arch)
     , PG.IsGroundSym grnd
     )
  => PPr.BlockSliceState grnd arch
  -> PP.Doc ann
renderIPs st
  | (PG.groundValue $ PPr.slRegOpEquiv pcRegs) = PP.pretty (PPa.someC vals)
  | otherwise = PPa.ppPatchPairC PP.pretty vals
  where
    vals = PPa.map (\(Const x) -> Const $ PFI.groundMacawValue x) (PPr.slRegOpValues pcRegs)
    pcRegs = PPr.slRegState st ^. MC.curIP

renderReturn
  :: PPa.PatchPairC (Maybe (PFI.GroundLLVMPointer w))
  -> Maybe (TP.UI TP.Element)
renderReturn ret =
  case ret of
    PPa.PatchPairC (Just c1) (Just c2) ->
      Just (text (PP.pretty "Continues execution at: " <> PPa.ppPatchPairCEq (PP.pretty . PFI.ppLLVMPointer) (PPa.PatchPairC c1 c2)))
    _ -> Nothing

renderCounterexample
  :: forall arch
   . ( PAr.ValidArch arch )
  => PPr.InequivalenceResult arch
  -> TP.UI TP.Element
renderCounterexample ineqRes' = PPr.withIneqResult ineqRes' $ \ineqRes ->
  let
    groundEnd = PPa.map (\(Const x) -> Const $ (PFI.groundBlockEnd (Proxy @arch)) x) $ PPr.slBlockExitCase (PPr.ineqSlice ineqRes)
    renderInequalityReason rsn =
      case rsn of
        PEE.InequivalentRegisters ->
          TP.string "The post-states of the original and patched programs contain inequivalent registers"
        PEE.InequivalentMemory ->
          TP.string "The post-states of the original and patched programs contain inequivalent memory locations"
        PEE.InvalidCallPair ->
          TP.string "The original and patched programs contain incomparable call pairs"
        PEE.InvalidPostState ->
          TP.string "The original and patched programs have generated invalid post states"

    renderedContinuation = TP.column (catMaybes [ Just (text (PP.pretty "Next IP: " <> renderIPs (PPr.slBlockPostState (PPr.ineqSlice ineqRes))))
                                                , renderReturn (PPa.map (\(Const x) -> Const $ PFI.grndBlockReturn x) groundEnd)
                                                ])
    in
    TP.grid [ [ renderInequalityReason (PPr.ineqReason ineqRes) ]
          , [ text (PPa.ppPatchPairCEq (PP.pretty . PFI.ppExitCase) (PPa.map (\(Const x) -> Const $ PFI.grndBlockCase x) groundEnd)) ]
          , [ TP.h2 #+ [TP.string "Initial states"] ]
          , [ renderRegisterState (PPr.ineqPre ineqRes) (PPr.slRegState (PPr.slBlockPreState (PPr.ineqSlice ineqRes)))
            , renderMemoryState (PPr.ineqPre ineqRes) (PPr.slMemState (PPr.slBlockPreState (PPr.ineqSlice ineqRes)))
            ]
          , [ TP.h2 #+ [TP.string "Final states"] ]
          , [ renderRegisterState (PPr.ineqPost ineqRes) (PPr.slRegState (PPr.slBlockPostState (PPr.ineqSlice ineqRes)))
            , renderMemoryState (PPr.ineqPre ineqRes) (PPr.slMemState (PPr.slBlockPostState (PPr.ineqSlice ineqRes)))
            ]
          , [ TP.h2 #+ [TP.string "Continuation"] ]
          , [ renderedContinuation ]
          ]
  where


renderProofTripleLabel
  :: (MapF.OrdF k)
  => MapF.MapF k (IS.ProofTreeNode arch prf)
  -> k tp
  -> TP.UI TP.Element
renderProofTripleLabel nodeMap parentNonce
  | Just (IS.ProofTreeNode _blocks parentExpr _) <- MapF.lookup parentNonce nodeMap =
      case PPr.prfNonceBody parentExpr of
        PPr.ProofBlockSlice {} ->
          TP.string "A proof that block slices are equivalent (i.e., satisfy their postconditions) under their preconditions"
        PPr.ProofFunctionCall _funcPre _callBody _cont targetAddr ->
          TP.string ("A proof that a call to the function at " ++ show targetAddr ++ " is safe")
        PPr.ProofTriple {} ->
          TP.string "Impossible proof structure with a triple as the parent of another triple"
        PPr.ProofStatus {} ->
          TP.string "Impossible proof structure with a status as the parent of a triple"
        PPr.ProofDomain {} ->
          TP.string "Impossible proof structure with a domain as the parent of a triple"
        PPr.ProofInlinedCall {} ->
          TP.string "A proof that two equated callees have equivalent behavior"
  | otherwise = TP.string "Unknown proof triple"

-- | Render the results from inlining a call
renderInlinedCall
  :: PPa.PatchPair (PB.ConcreteBlock arch)
  -> Either String (PVM.WriteSummary sym (MC.ArchAddrWidth arch))
  -> TP.UI TP.Element
renderInlinedCall (PPa.PatchPairSingle{}) _ = PPa.handleSingletonStub
renderInlinedCall (PPa.PatchPair ob pb) results =
  case results of
    Left err -> TP.column [ TP.string (T.unpack renderBlocks)
                          , TP.string err
                          ]
    Right (PVM.WriteSummary ranges _ _ _ w) ->
      let ppHex bv = PP.pretty (BVS.ppHex w bv)
          ppRange l h = text (ppHex l <> PP.pretty "-" <> ppHex h)
      in TP.column [ TP.string "The following global memory ranges differ between the original and patched programs"
                   , TP.ul #+ [ TP.li #+ [ppRange l h]
                              | DII.ClosedInterval l h <- PVM.indexWriteAddresses w ranges
                              ]
                   ]
  where
    renderBlocks =
      pp (mconcat [ PP.pretty (PB.concreteAddress ob)
                  , PP.pretty "/"
                  , PP.pretty (PB.concreteAddress pb)
                  ]
         )

renderStatus
  :: forall sym arch
   . ( WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     , PAr.ValidArch arch
     )  
  => PPr.VerificationStatus sym arch
  -> TP.UI TP.Element
renderStatus st = case st of
  PPr.VerificationFail cex diffSummary
    | Just False <- WI.asConstantPred (PPr.condEqPred diffSummary) ->
      TP.column [ text (PP.pretty "Proof Status: " <> ppStatus st)
                , TP.string "The patched program always exhibits different behavior if this program location is reached"
                , TP.string "Counterexample:"
                , renderCounterexample cex
                ]
    | otherwise ->
      TP.column [ text (PP.pretty "Proof Status: " <> ppStatus st)
                , TP.string "The patched program exhibits identical behavior to the original under the following conditions:"
                , TP.pre # TP.set TP.text (T.unpack (pp (WI.printSymExpr (PPr.condEqPred diffSummary))))
                , TP.string "Counterexample:"
                , renderCounterexample cex
                ]
  _ -> TP.div #+ [ text (PP.pretty "Proof Status: " <> ppStatus st)
                 ]

renderProofApp
  :: forall sym arch tp
   . ( WI.IsSymExprBuilder sym
     , MC.ArchConstraints arch
     , PAr.ValidArch arch
     )
  => MapF.MapF (PPr.ProofNonce sym) (IS.ProofTreeNode sym arch)
  -> Some (PPr.ProofNonce sym)
  -> PPr.ProofApp sym arch (PPr.ProofNonceExpr sym arch) tp
  -> TP.UI TP.Element
renderProofApp nodeMap (Some parentNonce) app =
  case app of
    PPr.ProofBlockSlice _domain _callees _mret _munknown _transition ->
      TP.div #+ [ TP.string "Proof that the post-domain of this slice of the program is satisfied when this slice returns, assuming its precondition"
                ]
    PPr.ProofFunctionCall _pre _body _cont targetAddr ->
      TP.div #+ [ TP.string ("Proof that a function call at " ++ show targetAddr ++ " is valid given its preconditions")
                ]
    PPr.ProofTriple _blocks pre post (PPr.ProofNonceExpr _ _ (PPr.ProofStatus status)) ->
      let preElts = TP.column [ TP.h3 #+ [TP.string "Pre-domain"]
                              , TP.string "These values are assumed to be equal in both the original and patched program at the start of this program slice"
                              , renderDomainExpr pre
                              ]
          postElts = TP.column [ TP.h3 #+ [TP.string "Post-domain"]
                               , TP.string "These values are asserted to be equal in both the original and patched program at the end of this program slice"
                               , renderDomainExpr post
                               ]
          statusElts = TP.column [ TP.h3 #+ [TP.string "Status"]
                                 , text (ppStatus status)
                                 ]
      in TP.grid [ [renderProofTripleLabel nodeMap parentNonce]
                 , [preElts # TP.set TP.class_ "domain", postElts # TP.set TP.class_ "domain"]
                 , [statusElts]
                 ]
    PPr.ProofInlinedCall blks results ->
      TP.column [ TP.string "The results of inlining equated call sites"
                , renderInlinedCall blks results
                ]
    PPr.ProofStatus st -> renderStatus st
    PPr.ProofDomain dom ->
      TP.column [ TP.string "The domain of an individual equivalence proof"
                , renderDomain dom
                ]

-- 
{- Note [Pending Nodes]

We verify proof nodes in parallel and mostly irrespective of dependency
order. If we try to render a snapshot of the proof at an arbitrary time, there
is a good chance that we will have verified a node without a parent in the
graph.  If we throw an error in that case, the exception is caught uncleanly and
seems to break the UI.

Instead, we render a marker denoting that the part of the proof tree is still
pending.

-}
