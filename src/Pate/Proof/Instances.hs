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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Proof.Instances
  ( SomeProofNonceExpr(..)
  , ppExitCase
  )
  
  where

import           Control.Lens hiding ( op, pre )
import           Data.List ( nubBy )
import qualified Data.IntervalMap.Interval as DII
import qualified Data.Kind as DK
import           Data.Maybe ( mapMaybe, catMaybes )
import           Data.Proxy ( Proxy(..) )
import           Numeric ( showHex )
import           Numeric.Natural ( Natural )

import qualified Data.Set as Set
import qualified Data.BitVector.Sized as BVS
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map ( Pair(..) )

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator.RegValue as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.Symbolic as MS

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Proof as PF
import qualified Pate.Ground as PG
import qualified Pate.PatchPair as PPa
import qualified Pate.MemCell as PMC
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Verification.MemoryLog as PVM

import qualified What4.Interface as W4
import qualified What4.Expr.GroundEval as W4G

data SomeProofNonceExpr (arch :: DK.Type) tp where
  SomeProofNonceExpr :: PA.ValidArch arch =>
    PSo.Sym sym -> PF.ProofNonceExpr sym arch tp -> SomeProofNonceExpr arch tp

instance Show (SomeProofNonceExpr arch tp) where
  show (SomeProofNonceExpr (PSo.Sym{}) e) = show (PP.pretty (PF.unNonceProof e))

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
     ppBlockPairReturn :: PB.BlockPair arch -> PP.Doc a
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
     ppBlockPairReturn :: PB.BlockPair arch -> PP.Doc a
     ppBlockPairReturn pPair = PPa.ppPatchPairEq PB.equivBlocks go pPair
       where
         go :: PB.ConcreteBlock arch bin -> PP.Doc a
         go blk = PP.parens (PP.pretty (PB.ppBlock blk) <+> "-> return")

     ppBlockPairTarget :: PB.BlockPair arch -> PB.BlockPair arch -> PP.Doc a
     ppBlockPairTarget (PPa.PatchPair srcO srcP) (PPa.PatchPair tgtO tgtP) =
       if PPa.ppEq srcO srcP && PPa.ppEq tgtO tgtP then
         go (srcO, tgtO)
       else
         go (srcO, tgtO) <+> "(original) vs." <+> go (srcP, tgtP) <+> "(patched)"
       where
         go :: (PB.ConcreteBlock arch bin, PB.ConcreteBlock arch bin) -> PP.Doc a
         go (src, tgt) = PP.parens (PP.pretty (PB.ppBlock src)) <+> "->" <+> (PP.pretty (PB.ppBlock tgt))
     ppBlockPairTarget _ _ = PPa.handleSingletonStub
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
  PP.Pretty (PED.EquivalenceDomain sym arch) where
  pretty prf = PP.vsep
    [ "Registers:"
    , PP.indent 4 $ PER.ppRegisterDomain (\_ -> "Conditional") (\r -> Just $ PP.pretty (showF r)) (PED.eqDomainRegisters prf)
    , "Stack Memory:"
    , PP.indent 4 $ PEM.ppMemoryDomainEntries (\_ -> "Conditional") (PED.eqDomainStackMemory prf)
    , "Global Memory:"
    , PP.indent 4 $ PEM.ppMemoryDomainEntries (\_ -> "Conditional") (PED.eqDomainGlobalMemory prf)
    ]


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
    { grndBlockCase :: MCS.MacawBlockEndCase
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
  PED.EquivalenceDomain grnd arch ->
  -- | post-domain
  PED.EquivalenceDomain grnd arch ->
  PF.BlockSliceTransition grnd arch ->
  PP.Doc a
ppBlockSliceTransition pre post bs = PP.vsep $
  [ "Block Exit Condition:" <+> PPa.ppPatchPairCEq (PP.pretty . ppExitCase) (PPa.map (\(Const x) -> Const $ grndBlockCase x) groundEnd)
  ,  "Initial register state:"
  , ppRegs pre (PF.slRegState $ PF.slBlockPreState bs)
  , "Initial memory state:"
  , ppMemCellMap pre (PF.slMemState $ PF.slBlockPreState bs)
  , "Final register state:"
  , ppRegs post (PF.slRegState $ PF.slBlockPostState bs)
  , "Final memory state:"
  , ppMemCellMap post (PF.slMemState $ PF.slBlockPostState bs)
  , "Final IP:" <+> ppIPs (PF.slBlockPostState bs)
  , case PPa.map (\(Const x) -> Const $ grndBlockReturn x) groundEnd of
      PPa.PatchPairC (Just cont1) (Just cont2) ->
        "Function Continue Address:" <+> PPa.ppPatchPairCEq (PP.pretty . ppLLVMPointer) (PPa.PatchPairC cont1 cont2)
      _ -> PP.emptyDoc
  ]
  where
    groundEnd = PPa.map (\(Const x) -> Const $ groundBlockEnd (Proxy @arch) x) $ PF.slBlockExitCase bs

ppIPs ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PF.BlockSliceState grnd arch ->
  PP.Doc a
ppIPs st  =
  let
    pcRegs = (PF.slRegState st) ^. MM.curIP
    vals = PPa.map (\(Const x) -> Const $ groundMacawValue x) (PF.slRegOpValues pcRegs)
  in case PG.groundValue $ PF.slRegOpEquiv pcRegs of
    True -> PP.pretty $ PPa.someC vals
    False -> PPa.ppPatchPairC PP.pretty vals

ppMemCellMap ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  MapF.MapF (PMC.MemCell grnd arch) (PF.BlockSliceMemOp grnd) ->
  PP.Doc a
ppMemCellMap dom cells = let
  eqEntries (Pair cell1 _) (Pair cell2 _) = eqGroundCells cell1 cell2
  ppCells = mapMaybe (\(Pair cell v) -> ppCellVal dom cell v) $ nubBy eqEntries $ MapF.toList cells
  in PP.vsep ppCells

-- | True if the two cells represent the same value when grounded
eqGroundCells ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PMC.MemCell grnd arch tp1 ->
  PMC.MemCell grnd arch tp2 ->
  Bool
eqGroundCells cell1 cell2 = case testEquality (PMC.cellWidth cell1) (PMC.cellWidth cell2) of
  Just Refl | PMC.cellEndian cell1 == PMC.cellEndian cell2 ->
    groundBV (PMC.cellPtr cell1) == groundBV (PMC.cellPtr cell2)
  _ -> False

ppRegs ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  -- | domain that this register set was checked for equivalence under
  PED.EquivalenceDomain grnd arch ->
  MM.RegState (MM.ArchReg arch) (PF.BlockSliceRegOp grnd) ->
  PP.Doc a
ppRegs dom regs = let
  rm = MapF.toList $ MM.regStateMap regs
  docs' = map (\(Pair reg op) -> ppRegVal (PED.eqDomainRegisters dom) reg op) rm
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
    (regTags, groundReg) = PG.groundInfoNat reg
    offInfo = PG.groundInfo off
    tags = regTags <> (PG.groundPtrTag offInfo)
  in mkGroundBV w tags groundReg (PG.groundVal offInfo)

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
  CS.RegValue grnd (MCS.MacawBlockEndType arch) ->
  GroundBlockExit arch
groundBlockEnd arch blkend =
  GroundBlockExit
    (PG.groundMacawEndCase arch blkend)
    (fmap groundLLVMPointer $ PG.groundPartial (MCS.blockEndReturn arch blkend))

  
ppRegVal ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PER.RegisterDomain grnd arch ->
  MM.ArchReg arch tp ->
  PF.BlockSliceRegOp grnd tp ->
  Maybe (PP.Doc a)
ppRegVal dom reg regOp = case PF.slRegOpRepr regOp of
  CLM.LLVMPointerRepr _ | PPa.PatchPairC (GroundMacawValue obv) (GroundMacawValue pbv) <- vals ->
    case isGroundBVZero obv && isGroundBVZero pbv of
         True -> Nothing
         False -> Just $ ppSlotVal
  _ -> Just $ ppSlotVal
  where
    vals = PPa.map (\(Const x) -> Const $ groundMacawValue x) $ PF.slRegOpValues regOp
    ppSlotVal = PP.pretty (showF reg) <> ":" <+> ppVals <+> ppDom

    ppDom = case regInGroundDomain dom reg of
      True -> PP.emptyDoc
      False -> "| Excluded"
    
    ppVals = case PG.groundValue $ PF.slRegOpEquiv regOp of
      True -> PP.pretty $ PPa.someC vals
      False -> PPa.ppPatchPairC PP.pretty vals

regInGroundDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PER.RegisterDomain grnd arch ->
  MM.ArchReg arch tp ->
  Bool
regInGroundDomain dom r = case PER.registerInDomain' r dom of
  Just p -> PG.groundValue p
  Nothing -> False


ppCellVal ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  PF.BlockSliceMemOp grnd tp ->
  Maybe (PP.Doc a)
ppCellVal dom cell memOp = case PG.groundValue $ PF.slMemOpCond memOp of
    True -> Just $ ppSlotVal
    False -> Nothing
  where
    vals = PPa.map (\(Const x) -> Const $ groundBV x) $ PF.slMemOpValues memOp
    ppSlotVal = ppGroundCell cell <> ":" <+> ppVals <+> ppDom

    ppDom = case cellInGroundDomain dom cell of
      True -> PP.emptyDoc
      False -> "| Excluded"
 
    ppVals = case PG.groundValue $ PF.slMemOpEquiv memOp of
      True -> PP.pretty $ show (PPa.someC vals)
      False -> PPa.ppPatchPairC (PP.pretty . show) vals

ppGroundCell ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PMC.MemCell grnd arch n ->
  PP.Doc a
ppGroundCell cell = PP.pretty $ (show $ groundLLVMPointer (PMC.cellPtr cell))

eqGroundMemCells ::
  PG.IsGroundSym grnd =>
  PMC.MemCell grnd arch n1 ->
  PMC.MemCell grnd arch n2 ->
  Bool  
eqGroundMemCells cell1 cell2 =
  case testEquality (PMC.cellWidth cell1) (PMC.cellWidth cell2) of
    Just Refl ->
      let
        CLM.LLVMPointer reg1 off1 = PMC.cellPtr cell1
        CLM.LLVMPointer reg2 off2 = PMC.cellPtr cell2
      in PG.groundNat reg1 == PG.groundNat reg2 && PG.groundValue off1 == PG.groundValue off2
    Nothing -> False


cellInMemDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PEM.MemoryDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  Bool
cellInMemDomain dom cell = foldr (\(Some cell', p) p' -> p' && (not (eqGroundMemCells cell cell') || not (PG.groundValue p))) True (PEM.toList dom)


cellInGroundDomain ::
  PA.ValidArch arch =>
  PG.IsGroundSym grnd =>
  PED.EquivalenceDomain grnd arch ->
  PMC.MemCell grnd arch n ->
  Bool
cellInGroundDomain dom cell = case isStackCell cell of
  True -> cellInMemDomain (PED.eqDomainStackMemory dom) cell
  False -> cellInMemDomain (PED.eqDomainGlobalMemory dom) cell

ppExitCase :: MCS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MCS.MacawBlockEndJump -> "arbitrary jump"
  MCS.MacawBlockEndCall -> "function call"
  MCS.MacawBlockEndReturn -> "function return"
  MCS.MacawBlockEndBranch -> "branch"
  MCS.MacawBlockEndArch -> "arch-specific"
  MCS.MacawBlockEndFail -> "analysis failure"

