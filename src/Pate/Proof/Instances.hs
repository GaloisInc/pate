{-|
Module           : Pate.ProofInstances
Copyright        : (c) Galois, Inc 2021
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Instantiations for the leaves of the proof types
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}

module Pate.Proof.Instances
  ( SomeProofSym(..)
  , GroundBV(..)
  , groundBV
  , mkGroundBV
  , groundBVAsPointer
  , ConcreteValue
  , GroundLLVMPointer(..)
  , GroundBlockExit(..)
  , groundBlockEnd
  , GroundMacawValue(..)
  , groundMacawValue
  , cellInDomain
  , regInDomain
  , ppLLVMPointer
  , ppInequivalencePreRegs
  , ppExitCase
  , ppGroundCell
  , isGroundBVZero
  )
  
  where

import           Control.Lens hiding ( op, pre )
import qualified Data.IntervalMap.Interval as DII
import qualified Data.Kind as DK
import           Data.Maybe
import           Data.Proxy
import           GHC.Natural
import           Numeric

import qualified Data.Set as Set
import qualified Data.BitVector.Sized as BVS
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map ( Pair(..) )

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator.RegValue as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.ExprMappable as PEM
import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Proof as PF
import qualified Pate.Ground as PG
import qualified Pate.PatchPair as PPa
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.MemCell as PMC
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Verification.MemoryLog as PVM

import qualified What4.Interface as W4
import qualified What4.ExprHelpers as WEH
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Partial as W4P

data SomeProofSym (arch :: DK.Type) tp where
  SomeProofSym :: PA.ValidArch arch =>
    PSo.Sym sym -> PF.ProofNonceExpr sym arch tp -> SomeProofSym arch tp

instance Show (SomeProofSym arch tp) where
  show (SomeProofSym (PSo.Sym{}) e) = show (PP.pretty (PF.unNonceProof e))

ppInequivalencePreRegs ::
  PF.InequivalenceResult arch -> String
ppInequivalencePreRegs gineq = PF.withIneqResult gineq $ \ineq ->
  show $ ppRegs (PF.ineqPre ineq) (PF.slRegState $ PF.slBlockPreState (PF.ineqSlice ineq))

-- | Specializing 'ProofExpr' and a 'BlockSliceTransition' to symbolic values.
-- data ProofSym sym arch

-- type instance PF.ProofBlock (ProofSym sym arch) = PB.ConcreteBlock arch
-- type instance PF.ProofRegister (ProofSym sym arch) = MM.ArchReg arch
-- type instance PF.ProofMemCell (ProofSym sym arch) = PMC.MemCell sym arch
-- type instance PF.ProofBV (ProofSym sym arch) = SymBV sym
-- type instance PF.ProofPredicate (ProofSym sym arch) = W4.Pred sym
-- type instance PF.ProofCounterExample (ProofSym sym arch) = InequivalenceResult arch
-- type instance PF.ProofCondition (ProofSym sym arch) = CondEquivalenceResult sym arch
-- type instance PF.ProofMacawValue (ProofSym sym arch) = PSR.MacawRegEntry sym
-- type instance PF.ProofBlockExit (ProofSym sym arch) = CS.RegValue sym (MS.MacawBlockEndType arch)
-- type instance PF.ProofContext (ProofSym sym arch) = PPa.PatchPair (PS.SimState sym arch)
-- type instance PF.ProofScope (ProofSym (W4B.ExprBuilder t st fs) arch) = t
-- type instance PF.ProofInlinedResult (ProofSym sym arch) = PVM.SomeWriteSummary (MM.ArchAddrWidth arch)
-- 
-- type SymDomain sym arch = PF.ProofExpr (ProofSym sym arch) PF.ProofDomainType

-- Needed because LLVMPtr is defined as an alias

-- instance (PA.ValidArch arch, PSo.ValidSym sym) => PEM.ExprMappable sym (PF.ProofExpr sym arch tp) where
--   mapExpr sym f (PF.ProofExpr app) = PF.ProofExpr <$> PEM.mapExpr sym f app
-- 
-- instance (PA.ValidArch arch, PSo.ValidSym sym) => PEM.ExprMappable sym (PF.ProofNonceExpr sym arch tp) where
--   mapExpr sym f (PF.ProofNonceExpr nonce parent app) = do
--     app' <- PEM.mapExpr sym f app
--     return $ PF.ProofNonceExpr nonce parent app'
--

ppCell :: (PA.ValidArch arch, PSo.ValidSym sym) => PMC.MemCell sym arch w -> PP.Doc a
ppCell cell =
  let CLM.LLVMPointer reg off = PMC.cellPtr cell
  in W4.printSymNat reg <> "+" <> PP.pretty (showF off)

ppMaybe :: Maybe f -> (f ->  PP.Doc a) -> PP.Doc a
ppMaybe (Just f) pp = pp f
ppMaybe Nothing _ = PP.emptyDoc

instance forall sym arch tp. (PA.ValidArch arch, PSo.ValidSym sym) => PP.Pretty (PF.ProofExpr sym arch tp) where
 pretty (PF.ProofExpr prf@PF.ProofFunctionCall { PF.prfFunctionCallBody = PF.ProofExpr (PF.ProofInlinedCall {}) }) =
   PP.vsep $
     [ "Function pre-domain is satisfied before call:"
     -- , PP.indent 4 $ ppBlockPairTarget (PF.prfTripleBlocks $ PF.unApp $ PF.prfFunctionCallPre prf) (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple slice)
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallPre prf
     , "Function satisfies post-domain upon return:"
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallBody prf
     ] ++ case PF.prfFunctionCallContinue prf of
       Just cont@(PF.ProofExpr (contSlice@PF.ProofBlockSlice {})) ->
         [ "Continuing after function return satisfies post-domain for caller."
         , PP.indent 4 $ ppBlockPairReturn (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple contSlice)
         , PP.indent 4 $ PP.pretty $ cont
         ]
       Just cont@(PF.ProofExpr (PF.ProofInlinedCall {})) ->
         [ "Continuing after inlined function return"
         , PP.indent 4 $ PP.pretty cont
         ]
       Nothing -> []
   where
     ppBlockPairReturn :: PPa.BlockPair arch -> PP.Doc a
     ppBlockPairReturn pPair = PPa.ppPatchPairEq PB.equivBlocks go pPair
       where
         go :: PB.ConcreteBlock arch bin -> PP.Doc a
         go blk = PP.parens (PP.pretty (PB.ppBlock blk) <+> "-> return")

 pretty (PF.ProofExpr prf@PF.ProofFunctionCall { PF.prfFunctionCallBody = PF.ProofExpr (slice@PF.ProofBlockSlice {}) }) =
   PP.vsep $
     [ "Function pre-domain is satisfied before call:"
     , PP.indent 4 $ ppBlockPairTarget (PF.prfTripleBlocks $ PF.unApp $ PF.prfFunctionCallPre prf) (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple slice)
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallPre prf
     , "Function satisfies post-domain upon return:"
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallBody prf
     ] ++ case PF.prfFunctionCallContinue prf of
       Just cont@(PF.ProofExpr (contSlice@PF.ProofBlockSlice {})) ->
         [ "Continuing after function return satisfies post-domain for caller."
         , PP.indent 4 $ ppBlockPairReturn (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple contSlice)
         , PP.indent 4 $ PP.pretty $ cont
         ]
       Just cont@(PF.ProofExpr (PF.ProofInlinedCall {})) ->
         [ "Continuing after inlined function return"
         , PP.indent 4 $ PP.pretty cont
         ]
       Nothing -> []
   where
     ppBlockPairReturn :: PPa.BlockPair arch -> PP.Doc a
     ppBlockPairReturn pPair = PPa.ppPatchPairEq PB.equivBlocks go pPair
       where
         go :: PB.ConcreteBlock arch bin -> PP.Doc a
         go blk = PP.parens (PP.pretty (PB.ppBlock blk) <+> "-> return")

     ppBlockPairTarget :: PPa.BlockPair arch -> PPa.BlockPair arch -> PP.Doc a
     ppBlockPairTarget (PPa.PatchPair srcO srcP) (PPa.PatchPair tgtO tgtP) =
       if PPa.ppEq srcO srcP && PPa.ppEq tgtO tgtP then
         go (srcO, tgtO)
       else
         go (srcO, tgtO) <+> "(original) vs." <+> go (srcP, tgtP) <+> "(patched)"
       where
         go :: (PB.ConcreteBlock arch bin, PB.ConcreteBlock arch bin) -> PP.Doc a
         go (src, tgt) = PP.parens (PP.pretty (PB.ppBlock src)) <+> "->" <+> (PP.pretty (PB.ppBlock tgt))
 pretty (PF.ProofExpr prf@PF.ProofBlockSlice{}) =
    PP.vsep
      [ PP.pretty (PF.prfBlockSliceTriple prf)
      , "Proof:"
      , PP.indent 4 $ 
          (case PF.prfBlockSliceCalls prf of
            [] -> PP.emptyDoc
            funCalls -> "Function Calls: "
                 <> PP.line
                 <> PP.indent 4 (PP.vsep (map (PP.pretty . snd) funCalls))
                 <> PP.line
          )
          <> (ppMaybe (PF.prfBlockSliceReturn prf) $ \trip ->
            PP.vsep
              [ "Function Return: "
              , PP.indent 4 $ PP.pretty trip
              ])
          <> (ppMaybe (PF.prfBlockSliceUnknownExit prf) $ \trip ->
            PP.vsep
              [ "Unknown function exit: "
              , PP.indent 4 $ PP.pretty trip
              ])
      ]
 pretty (PF.ProofExpr prf@PF.ProofTriple{}) =
   PP.vsep
     [ "Block Transition:"
     , PP.indent 4 $ PPa.ppPatchPairEq PB.equivBlocks (PP.pretty . PB.ppBlock) (PF.prfTripleBlocks prf)
     , "Pre-domain:"
     , PP.indent 4 $ PP.pretty (PF.prfTriplePreDomain prf)
     , "Post-domain:"
     , PP.indent 4 $ PP.pretty (PF.prfTriplePostDomain prf)
     , "Verification Status:"
     , PP.indent 4 $ PP.pretty (PF.prfTripleStatus prf)
     ]
 pretty (PF.ProofExpr (PF.ProofInlinedCall blks res)) = case res of
    Left err ->
      PP.vsep [ "Inlined callees: " <> PP.pretty blks
              , "  Error: " <> PP.pretty err
              ]
    Right writeSummary ->
      let ptrW = writeSummary ^. PVM.pointerWidth
          locRanges = PVM.indexWriteAddresses ptrW (writeSummary ^. PVM.differingGlobalMemoryLocations)
          ppRange r = "[" <> PP.pretty (BVS.ppHex ptrW (DII.lowerBound r)) <> "-" <> PP.pretty (BVS.ppHex ptrW (DII.upperBound r)) <> "]"
      in PP.vsep [ "Inlined callees: " <> PP.pretty blks
                 , "Global addresses with different contents: "
                 , PP.indent 2 $ PP.vsep (map ppRange locRanges)
                 ]
 pretty (PF.ProofExpr (PF.ProofDomain dom)) = PP.pretty dom
 pretty (PF.ProofExpr (PF.ProofStatus st)) = PP.pretty st

instance forall sym arch.
  (PA.ValidArch arch, PSo.ValidSym sym) =>
  PP.Pretty (PF.EquivalenceDomain sym arch) where
  pretty prf = PP.vsep
    [ "Registers:"
    , PP.indent 4 $ prettyRegs
    , "Stack Memory:" <+> ppPolarity (PF.memoryDomainPolarity $ PF.eqDomainStackMemory prf)
    , PP.indent 4 $ prettyMem (PF.eqDomainStackMemory prf)
    , "Global Memory:" <+> ppPolarity (PF.memoryDomainPolarity $ PF.eqDomainGlobalMemory prf)
    , PP.indent 4 $ prettyMem (PF.eqDomainGlobalMemory prf)
    ]
    where
      prettyRegs = PP.vsep (map ppReg (collapseRegState (Proxy @sym) (PF.eqDomainRegisters prf)))

      ppReg :: (Some (MM.ArchReg arch), W4.Pred sym) -> PP.Doc a
      ppReg (Some reg, p) = case W4.asConstantPred p of
        Just True -> PP.pretty (showF reg)
        _ -> PP.pretty (showF reg) <> PP.line <> "Conditional"

      prettyMem m = PP.vsep (map ppMem (collapseProofMemoryDomain m))

      ppMem :: (Some (PMC.MemCell sym arch), W4.Pred sym) -> PP.Doc a
      ppMem (Some cell, p) = case W4.asConstantPred p of
        Just True -> ppCell cell
        _ -> ppCell cell <> PP.line <> "Conditional"

      ppPolarity :: W4.Pred sym -> PP.Doc a
      ppPolarity p = case W4.asConstantPred p of
        Just True -> PP.parens "inclusive"
        Just False -> PP.parens "exclusive"
        _ -> PP.parens "symbolic polarity"


instance forall sym arch.
  (PA.ValidArch arch, PSo.ValidSym sym) =>
  PP.Pretty (PF.VerificationStatus sym arch) where
  pretty st = case st of
    PF.Unverified -> "Not verified"
    PF.VerificationSkipped -> "Skipped (assumed)"
    PF.VerificationSuccess -> "Succeeded"
    PF.VerificationFail result cond -> PP.vsep [ "Failed:", PP.pretty result, PP.pretty cond ]




instance PSo.ValidSym sym => PP.Pretty (PF.CondEquivalenceResult sym arch) where
  pretty (PF.CondEquivalenceResult pExample pPred pAbortValid) =
    PP.vsep $
     [ "Equivalence Condition:"
     , PP.pretty (showF pPred)
     , "Condition is abort-valid: " <> (PP.pretty pAbortValid)
     , "Bindings in Counter-example:"
     ] ++ map prettyBind (MapF.toList pExample)
     where
       prettyGV :: W4.BaseTypeRepr tp -> W4G.GroundValue tp -> PP.Doc a
       prettyGV W4.BaseBoolRepr b = PP.pretty $ show b
       prettyGV (W4.BaseBVRepr w) bv = PP.pretty $ show (GroundBV mempty w bv)
       prettyGV (W4.BaseStructRepr Ctx.Empty) _ = "()"
       prettyGV _ _ = "Unsupported Type"

       prettyBind :: Pair (W4.SymExpr sym) (W4G.GroundValueWrapper) -> PP.Doc a
       prettyBind (Pair e (W4G.GVW gv)) =
         W4.printSymExpr e <+> "-->" <+> prettyGV (W4.exprType e) gv


collapseRegState ::
  forall sym arch.
  PSo.ValidSym sym =>
  PA.ValidArch arch =>
  Proxy sym ->
  MM.RegState (MM.ArchReg arch) (Const (W4.Pred sym)) ->
  [(Some (MM.ArchReg arch), W4.Pred sym)]
collapseRegState _ regState =
  mapMaybe go $ MapF.toList $ MM.regStateMap regState
  where
    go :: Pair (MM.ArchReg arch) (Const (W4.Pred sym)) ->
       Maybe (Some (MM.ArchReg arch), W4.Pred sym)
    go (Pair reg (Const p)) = case W4.asConstantPred p of
      Just False -> Nothing
      _ -> Just (Some reg, p)

collapseProofMemoryDomain ::
  forall sym arch.
  PSo.ValidSym sym =>
  PA.ValidArch arch =>
  PF.MemoryDomain sym arch ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
collapseProofMemoryDomain memdom = mapMaybe go $ MapF.toList (PF.memoryDomain memdom)
  where
    go :: MapF.Pair (PMC.MemCell sym arch)
                    (Const (W4.Pred sym))
          -> Maybe (Some (PMC.MemCell sym arch), W4.Pred sym)
    go (MapF.Pair cell (Const p)) =
        case W4.asConstantPred p of
          Just False -> Nothing
          _ -> Just (Some cell, p)

-- | Specializing 'ProofExpr' and 'BlockSliceTransition' to concrete values.

-- data ProofGround arch

-- type instance PF.ProofBlock (ProofGround arch) = PB.ConcreteBlock arch
-- type instance PF.ProofRegister (ProofGround arch) = MM.ArchReg arch
-- type instance PF.ProofMemCell (ProofGround arch) = GroundMemCell arch
-- type instance PF.ProofBV (ProofGround arch) = GroundBV
-- type instance PF.ProofCounterExample (ProofGround arch) = InequivalenceResult arch
-- type instance PF.ProofCondition (ProofGround arch) = ()
-- type instance PF.ProofPredicate (ProofGround arch) = Bool
-- type instance PF.ProofMacawValue (ProofGround arch) = GroundMacawValue
-- type instance PF.ProofBlockExit (ProofGround arch) = GroundBlockExit arch
-- -- no additional context needed for ground values
-- type instance PF.ProofContext (ProofGround arch) = ()
-- type instance PF.ProofInlinedResult (ProofGround arch) = PVM.SomeWriteSummary (MM.ArchAddrWidth arch)
-- 
-- instance PA.ValidArch arch => PF.IsProof (ProofGround arch)



data GroundBV n where
  GroundBV :: MT.UndefPtrOpTags -> W4.NatRepr n -> BVS.BV n -> GroundBV n
  GroundLLVMPointer :: GroundLLVMPointer n -> GroundBV n
  deriving Eq

instance Show (GroundBV n) where
  show = ppGroundBV

ppGroundBV :: GroundBV w -> String
ppGroundBV gbv = case gbv of
  GroundBV tag w bv -> BVS.ppHex w bv ++ ppUndefPtrTag tag
  GroundLLVMPointer ptr -> ppLLVMPointer ptr 

ppUndefPtrTag :: MT.UndefPtrOpTags -> String
ppUndefPtrTag tags = case Set.toList tags of
  [] -> ""
  tagsList -> show tagsList

groundBVWidth :: GroundBV n -> W4.NatRepr n
groundBVWidth gbv = case gbv of
  GroundBV _ nr _ -> nr
  GroundLLVMPointer ptr -> ptrWidth ptr

instance TestEquality GroundBV where
  testEquality bv bv' = case testEquality (groundBVWidth bv) (groundBVWidth bv') of
    Just Refl | bv == bv' -> Just Refl
    _ -> Nothing

instance OrdF GroundBV where
  compareF (GroundBV tag w bv) (GroundBV tag' w' bv') =
    lexCompareF w w' $ fromOrdering $ compare bv bv' <> compare tag tag'
  compareF (GroundLLVMPointer ptr) (GroundLLVMPointer ptr') = compareF ptr ptr'
  compareF (GroundBV _ _ _) _ = LTF
  compareF (GroundLLVMPointer _) _ = GTF

instance Ord (GroundBV n) where
  compare bv bv' = toOrdering (compareF bv bv')

data GroundLLVMPointer n where
  GroundLLVMPointerC ::
      { ptrWidth :: W4.NatRepr n
      , ptrRegion :: Natural
      , _ptrOffset :: BVS.BV n
      , _ptrUndefTag :: MT.UndefPtrOpTags
      } -> GroundLLVMPointer n
  deriving Eq

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

ppLLVMPointer :: GroundLLVMPointer w -> String
ppLLVMPointer (GroundLLVMPointerC bitWidthRepr reg offBV tag) = concat
  [ pad 3 (show reg)
  , "+0x"
  , padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")
  , ppUndefPtrTag tag
  ]
  where
    off = BVS.asUnsigned offBV
    bitWidth = W4.natValue bitWidthRepr

instance TestEquality GroundLLVMPointer where
  testEquality ptr ptr'
    | Just Refl <- testEquality (ptrWidth ptr) (ptrWidth ptr')
    , ptr == ptr'
    = Just Refl
  testEquality _ _ = Nothing

instance Ord (GroundLLVMPointer n) where
  compare (GroundLLVMPointerC _ reg off tag) (GroundLLVMPointerC _ reg' off' tag') =
    compare reg reg' <> compare off off' <> compare tag tag'

instance OrdF GroundLLVMPointer where
  compareF ptr ptr' =
    lexCompareF (ptrWidth ptr) (ptrWidth ptr') $ fromOrdering $ compare ptr ptr'

instance Show (GroundLLVMPointer n) where
  show ptr = ppLLVMPointer ptr

mkGroundBV :: forall n.
  W4.NatRepr n ->
  MT.UndefPtrOpTags ->
  Natural ->
  BVS.BV n ->
  GroundBV n
mkGroundBV nr tag reg bv = case reg > 0 of
 True -> GroundLLVMPointer $ GroundLLVMPointerC nr reg bv tag
 False -> GroundBV tag nr bv

groundBVAsPointer :: GroundBV n -> GroundLLVMPointer n
groundBVAsPointer gbv = case gbv of
  GroundLLVMPointer ptr -> ptr
  GroundBV tag w bv -> GroundLLVMPointerC w 0 bv tag

type family ConcreteValue (tp :: CT.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundBV w
type instance ConcreteValue (CT.MaybeType (CLM.LLVMPointerType w)) = Maybe (GroundBV w)
type instance ConcreteValue CT.BoolType = Bool
type instance ConcreteValue (CT.StructType CT.EmptyCtx) = ()

type ValidMacawType tp = (Eq (ConcreteValue (MS.ToCrucibleType tp)), Show (ConcreteValue (MS.ToCrucibleType tp)))

data GroundMacawValue tp where
  GroundMacawValue :: ValidMacawType tp =>
    { grndMacawValue :: ConcreteValue (MS.ToCrucibleType tp)
    } -> GroundMacawValue tp

instance PP.Pretty (GroundMacawValue tp) where
  pretty (GroundMacawValue v) = PP.pretty (show v)


data GroundBlockExit arch where
  GroundBlockExit ::
    { grndBlockCase :: MS.MacawBlockEndCase
    , grndBlockReturn :: Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch))
    } -> GroundBlockExit arch
  deriving Eq

instance PA.ValidArch arch => PP.Pretty (PF.InequivalenceResult arch) where
  pretty gineq = PF.withIneqResult gineq $ \ineq ->
    PP.vsep [ "Reason:" <+> PP.pretty (show (PF.ineqReason ineq))
            , ppBlockSliceTransition (PF.ineqPre ineq) (PF.ineqPost ineq) (PF.ineqSlice ineq)
            ]

ppBlockSliceTransition ::
  forall grnd arch a.
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  -- | pre-domain
  PF.EquivalenceDomain grnd arch ->
  -- | post-domain
  PF.EquivalenceDomain grnd arch ->
  PF.BlockSliceTransition grnd arch ->
  PP.Doc a
ppBlockSliceTransition pre post bs = PP.vsep $
  [ "Block Exit Condition:" <+> PPa.ppPatchPairCEq (PP.pretty . ppExitCase) (fmap grndBlockCase groundEnd)
  ,  "Initial register state:"
  , ppRegs pre (PF.slRegState $ PF.slBlockPreState bs)
  , "Initial memory state:"
  , ppMemCellMap pre (PF.slMemState $ PF.slBlockPreState bs)
  , "Final register state:"
  , ppRegs post (PF.slRegState $ PF.slBlockPostState bs)
  , "Final memory state:"
  , ppMemCellMap post (PF.slMemState $ PF.slBlockPostState bs)
  , "Final IP:" <+> ppIPs (PF.slBlockPostState bs)
  , case fmap grndBlockReturn groundEnd of
      PPa.PatchPairC (Just cont1) (Just cont2) ->
        "Function Continue Address:" <+> PPa.ppPatchPairCEq (PP.pretty . ppLLVMPointer) (PPa.PatchPairC cont1 cont2)
      _ -> PP.emptyDoc
  ]
  where
    groundEnd = fmap (groundBlockEnd (Proxy @arch)) $ PF.slBlockExitCase bs

ppIPs ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.BlockSliceState grnd arch ->
  PP.Doc a
ppIPs st  =
  let
    pcRegs = (PF.slRegState st) ^. MM.curIP
    vals = fmap groundMacawValue (PF.slRegOpValues pcRegs)
  in case PG.groundValue $ PF.slRegOpEquiv pcRegs of
    True -> PP.pretty $ PPa.pcOriginal vals
    False -> PPa.ppPatchPairC PP.pretty vals

ppMemCellMap ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.EquivalenceDomain grnd arch ->
  MapF.MapF (PMC.MemCell grnd arch) (PF.BlockSliceMemOp grnd) ->
  PP.Doc a
ppMemCellMap dom cells = let
  ppCells = mapMaybe (\(Pair cell v) -> ppCellVal dom cell v) $ MapF.toList cells
  in PP.vsep ppCells

ppRegs ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  -- | domain that this register set was checked for equivalence under
  PF.EquivalenceDomain grnd arch ->
  MM.RegState (MM.ArchReg arch) (PF.BlockSliceRegOp grnd) ->
  PP.Doc a
ppRegs dom regs = let
  rm = MapF.toList $ MM.regStateMap regs
  docs' = map (\(Pair reg op) -> ppRegVal dom reg op) rm
  docs = catMaybes docs'
  diff = length docs' - length docs
  in (PP.vsep docs) <> PP.line <> (".. and" <+> PP.pretty diff <+> "zero-valued registers")
  

isGroundBVZero :: GroundBV w -> Bool
isGroundBVZero (GroundBV _ _ ptr) = BVS.asUnsigned ptr == 0
isGroundBVZero _ = False


groundLLVMPointer :: forall sym w.
  PG.IsGroundSym sym =>
  CLM.LLVMPtr sym w ->
  GroundLLVMPointer w
groundLLVMPointer ptr = groundBVAsPointer $ groundBV ptr

isStackCell :: forall grnd arch w.
  PG.IsGroundSym grnd =>
  PMC.MemCell grnd arch w ->
  Bool
isStackCell cell =
  let CLM.LLVMPointer reg _ = PMC.cellPtr cell
  in PG.isStackRegion reg

groundBV ::
  PG.IsGroundSym grnd =>
  CLM.LLVMPtr grnd w ->
  GroundBV w
groundBV (CLM.LLVMPointer reg off)
  | W4.BaseBVRepr w <- W4.exprType off =
  let
    regInfo = PG.groundInfoNat reg
    offInfo = PG.groundInfo off
    tags = PG.groundPtrTag regInfo <> (PG.groundPtrTag offInfo)
    integerToNat :: Integer -> Natural
    integerToNat i
      | i >= 0 = fromIntegral i
      | otherwise = 0
  in mkGroundBV w tags (integerToNat (PG.groundVal regInfo)) (PG.groundVal offInfo)

groundMacawValue ::
  PG.IsGroundSym grnd =>
  PSR.MacawRegEntry grnd tp ->
  GroundMacawValue tp
groundMacawValue e
  | CLM.LLVMPointerRepr _ <- PSR.macawRegRepr e
  , ptr <- PSR.macawRegValue e = do
    GroundMacawValue $ groundBV ptr
  | CT.BoolRepr <- PSR.macawRegRepr e
  , val <- PSR.macawRegValue e = GroundMacawValue $ PG.groundValue val
  | CT.StructRepr Ctx.Empty <- PSR.macawRegRepr e = GroundMacawValue ()
  | otherwise = error $ "groundMacawValue: unexpected register type:" ++ show (PSR.macawRegRepr e)


groundBlockEnd ::
  forall grnd arch.
  PG.IsGroundSym grnd =>
  Proxy arch ->
  CS.RegValue grnd (MS.MacawBlockEndType arch) ->
  GroundBlockExit arch
groundBlockEnd arch blkend =
  GroundBlockExit
    (PG.groundMacawEndCase arch blkend)
    (fmap groundLLVMPointer $ PG.groundPartial (MS.blockEndReturn arch blkend))

  
ppRegVal ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.EquivalenceDomain grnd arch ->
  MM.ArchReg arch tp ->
  PF.BlockSliceRegOp grnd tp ->
  Maybe (PP.Doc a)
ppRegVal dom reg regOp = case PF.slRegOpRepr regOp of
  CLM.LLVMPointerRepr _ ->
    let
      PPa.PatchPairC (GroundMacawValue obv) (GroundMacawValue pbv) = vals
    in case isGroundBVZero obv && isGroundBVZero pbv of
         True -> Nothing
         False -> Just $ ppSlotVal
  _ -> Just $ ppSlotVal
  where
    vals = fmap groundMacawValue $ PF.slRegOpValues regOp
    ppSlotVal = PP.pretty (showF reg) <> ":" <+> ppVals <+> ppDom

    ppDom = case regInDomain dom reg of
      True -> PP.emptyDoc
      False -> "| Excluded"
    
    ppVals = case PG.groundValue $ PF.slRegOpEquiv regOp of
      True -> PP.pretty $ PPa.pcOriginal vals
      False -> PPa.ppPatchPairC PP.pretty vals

regInDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.EquivalenceDomain grnd arch ->
  MM.ArchReg arch tp ->
  Bool
regInDomain dom r = PG.groundValue $ getConst $ PF.eqDomainRegisters dom ^. MM.boundValue r 


ppCellVal ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.EquivalenceDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  PF.BlockSliceMemOp grnd tp ->
  Maybe (PP.Doc a)
ppCellVal dom cell memOp = case PG.groundValue $ PF.slMemOpCond memOp of
    True -> Just $ ppSlotVal
    False -> Nothing
  where
    vals = fmap groundBV $ PF.slMemOpValues memOp
    ppSlotVal = ppGroundCell cell <> ":" <+> ppVals <+> ppDom

    ppDom = case cellInDomain dom cell of
      True -> PP.emptyDoc
      False -> "| Excluded"
 
    ppVals = case PG.groundValue $ PF.slMemOpEquiv memOp of
      True -> PP.pretty $ show (PPa.pcOriginal vals)
      False -> PPa.ppPatchPairC (PP.pretty . show) vals

ppGroundCell ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PMC.MemCell grnd arch n ->
  PP.Doc a
ppGroundCell cell = PP.pretty $ (show $ groundLLVMPointer (PMC.cellPtr cell))

-- TODO: we can't rely on MapF.lookup being consistent here because it's relying on
-- term equality for annotated terms.
-- The easiest solution is to just traverse the domain and use equality on ground terms,
-- but we could also consider generalizing this container type to support lookups
-- based on abstract domains (see CachedArray from crucible symio).
cellInMemDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.MemoryDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  Bool
cellInMemDomain dom cell  = case MapF.lookup cell (PF.memoryDomain dom) of
    Just (Const p) -> PG.groundValue p == (PG.groundValue $ PF.memoryDomainPolarity dom)
    Nothing -> not $ (PG.groundValue $ PF.memoryDomainPolarity dom)


cellInDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.EquivalenceDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  Bool
cellInDomain dom cell = case isStackCell cell of
  True -> cellInMemDomain (PF.eqDomainStackMemory dom) cell
  False -> cellInMemDomain (PF.eqDomainGlobalMemory dom) cell

ppExitCase :: MS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MS.MacawBlockEndJump -> "arbitrary jump"
  MS.MacawBlockEndCall -> "function call"
  MS.MacawBlockEndReturn -> "function return"
  MS.MacawBlockEndBranch -> "branch"
  MS.MacawBlockEndArch -> "syscall"
  MS.MacawBlockEndFail -> "analysis failure"
