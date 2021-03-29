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
  ( ProofSym
  , ProofGround
  , InequivalenceResult(..)
  , SymBV(..)
  , ProofSymExpr
  , ProofSymNonceExpr
  , ProofSymNonceApp
  , ProofSymApp
  , SomeProofSym(..)
  , GroundBV(..)
  , mkGroundBV
  , groundBVAsPointer
  , ConcreteValue
  , GroundLLVMPointer(..)
  , GroundBlockExit(..)
  , GroundDomain
  , GroundMemCell(..)
  , GroundMacawValue(..)
  , cellInDomain
  , regInDomain
  , ppInequivalencePreRegs
  )
  
  where

import           Numeric
import           GHC.Natural
import           Data.Functor.Const
import qualified Data.Kind as DK
import           Control.Lens hiding ( op, pre )
import           Data.Maybe
import           Data.Proxy

import qualified Data.BitVector.Sized as BVS
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
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
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.MemCell as PMC
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified What4.Interface as W4
import qualified What4.ExprHelpers as WEH
import qualified What4.Expr.Builder as W4B


data SomeProofSym (arch :: DK.Type) tp where
  SomeProofSym :: PA.ValidArch arch =>
    PT.Sym sym -> ProofSymNonceExpr sym arch tp -> SomeProofSym arch tp

instance Show (SomeProofSym arch tp) where
  show (SomeProofSym (PT.Sym{}) e) = show (PP.pretty (PF.unNonceProof e))

data InequivalenceResult arch where
  InequivalenceResult :: PA.ValidArch arch =>
    { ineqSlice :: PF.BlockSliceTransition (ProofGround arch)
    , ineqPre :: GroundDomain arch
    , ineqPost :: GroundDomain arch
    , ineqReason :: PT.InequivalenceReason
    } -> InequivalenceResult arch


ppInequivalencePreRegs ::
  InequivalenceResult arch -> String
ppInequivalencePreRegs (ineq@InequivalenceResult{}) =
  show $ ppRegs (ineqPre ineq) (PF.slRegState $ PF.slBlockPreState (ineqSlice ineq))

-- | Specializing 'ProofExpr' and a 'BlockSliceTransition' to symbolic values.
data ProofSym sym arch

type instance PF.ProofBlock (ProofSym sym arch) = PT.ConcreteBlock arch
type instance PF.ProofRegister (ProofSym sym arch) = MM.ArchReg arch
type instance PF.ProofMemCell (ProofSym sym arch) = PMC.MemCell sym arch
type instance PF.ProofBV (ProofSym sym arch) = SymBV sym
type instance PF.ProofPredicate (ProofSym sym arch) = W4.Pred sym
type instance PF.ProofCounterExample (ProofSym sym arch) = InequivalenceResult arch
type instance PF.ProofMacawValue (ProofSym sym arch) = PSR.MacawRegEntry sym
type instance PF.ProofBlockExit (ProofSym sym arch) = CS.RegValue sym (MS.MacawBlockEndType arch)
type instance PF.ProofContext (ProofSym sym arch) = PT.PatchPair (PS.SimState sym arch)
type instance PF.ProofScope (ProofSym (W4B.ExprBuilder t st fs) arch) = t

-- Needed because LLVMPtr is defined as an alias
newtype SymBV sym w = SymBV (CLM.LLVMPtr sym w)

instance PEM.ExprMappable sym (SymBV sym w) where
  mapExpr sym f (SymBV bv) = SymBV <$> WEH.mapExprPtr sym f bv

instance (PA.ValidArch arch, PT.ValidSym sym) => PEM.ExprMappable sym (PF.ProofExpr (ProofSym sym arch) tp) where
  mapExpr sym f (PF.ProofExpr app) = PF.ProofExpr <$> PEM.mapExpr sym f app

instance (PA.ValidArch arch, PT.ValidSym sym) => PEM.ExprMappable sym (PF.ProofNonceExpr (ProofSym sym arch) tp) where
  mapExpr sym f (PF.ProofNonceExpr nonce parent app) = do
    app' <- PEM.mapExpr sym f app
    return $ PF.ProofNonceExpr nonce parent app'

instance
  ( PA.ValidArch arch
  , PT.ValidSym sym,
    forall ntp. PEM.ExprMappable sym (app ntp)) =>
  PEM.ExprMappable sym (PF.ProofApp (ProofSym sym arch) app tp) where
  mapExpr sym f app =
    PF.traverseProofApp (PEM.mapExpr sym f) =<< PF.transformProofApp (mapExprTrans sym f) app
    
mapExprTrans ::
  PA.ValidArch arch =>
  PT.ValidSym sym =>
  sym ->
  (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
  PF.ProofTransformer IO (ProofSym sym arch) (ProofSym sym arch)
mapExprTrans sym f = PF.ProofTransformer
  { PF.prfPredTrans = f
  , PF.prfMemCellTrans = PEM.mapExpr sym f
  , PF.prfBVTrans = PEM.mapExpr sym f
  , PF.prfExitTrans = PEM.mapExpr sym f
  , PF.prfValueTrans = PEM.mapExpr sym f
  , PF.prfContextTrans = PEM.mapExpr sym f
  , PF.prfConstraint = \a -> a
  }

instance (PA.ValidArch arch, PT.ValidSym sym) => PF.IsProof (ProofSym sym arch)

type ProofSymNonceExpr sym arch = PF.ProofNonceExpr (ProofSym sym arch)
type ProofSymNonceApp sym arch = PF.ProofApp (ProofSym sym arch) (ProofSymNonceExpr sym arch)

type ProofSymExpr sym arch = PF.ProofExpr (ProofSym sym arch)
type ProofSymApp sym arch = PF.ProofApp (ProofSym sym arch) (ProofSymExpr sym arch)

ppCell :: (PA.ValidArch arch, PT.ValidSym sym) => PMC.MemCell sym arch w -> PP.Doc a
ppCell cell =
  let CLM.LLVMPointer reg off = PMC.cellPtr cell
  in PP.pretty (showF reg) <> "+" <> PP.pretty (showF off)

ppMaybe :: Maybe f -> (f ->  PP.Doc a) -> PP.Doc a
ppMaybe (Just f) pp = pp f
ppMaybe Nothing _ = PP.emptyDoc

instance forall sym arch tp. (PA.ValidArch arch, PT.ValidSym sym) => PP.Pretty (PF.ProofExpr (ProofSym sym arch) tp) where
 pretty (PF.ProofExpr prf@PF.ProofFunctionCall{}) =
   PP.vsep $ 
     [ "Function pre-domain is satisfied before call:"
     , PP.indent 4 $ ppBlockPairTarget (PF.prfTripleBlocks $ PF.unApp $ PF.prfFunctionCallPre prf) (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple $ PF.unApp $ PF.prfFunctionCallBody prf)
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallPre prf
     , "Function satisfies post-domain upon return:"
     , PP.indent 4 $ PP.pretty $ PF.prfFunctionCallBody prf
     ] ++ case PF.prfFunctionCallContinue prf of
       Just cont ->
         [ "Continuing after function return satisfies post-domain for caller."
         , PP.indent 4 $ ppBlockPairReturn (PF.prfTripleBlocks $ PF.unApp $ PF.prfBlockSliceTriple $ PF.unApp cont)
         , PP.indent 4 $ PP.pretty $ cont
         ]
       Nothing -> []
   where
     ppBlockPairReturn :: PT.BlockPair arch -> PP.Doc a
     ppBlockPairReturn pPair = PT.ppPatchPairEq PT.equivBlocks go pPair
       where
         go :: PT.ConcreteBlock arch bin -> PP.Doc a
         go blk = PP.parens (PP.pretty (PT.ppBlock blk) <+> "-> return")

     ppBlockPairTarget :: PT.BlockPair arch -> PT.BlockPair arch -> PP.Doc a
     ppBlockPairTarget (PT.PatchPair srcO srcP) (PT.PatchPair tgtO tgtP) =
       if PT.ppEq srcO srcP && PT.ppEq tgtO tgtP then
         go (srcO, tgtO)
       else
         go (srcO, tgtO) <+> "(original) vs." <+> go (srcP, tgtP) <+> "(patched)"
       where
         go :: (PT.ConcreteBlock arch bin, PT.ConcreteBlock arch bin) -> PP.Doc a
         go (src, tgt) = PP.parens (PP.pretty (PT.ppBlock src)) <+> "->" <+> (PP.pretty (PT.ppBlock tgt))
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
     , PP.indent 4 $ PT.ppPatchPairEq PT.equivBlocks (PP.pretty . PT.ppBlock) (PF.prfTripleBlocks prf)
     , "Pre-domain:"
     , PP.indent 4 $ PP.pretty (PF.prfTriplePreDomain prf)
     , "Post-domain:"
     , PP.indent 4 $ PP.pretty (PF.prfTriplePostDomain prf)
     , "Verification Status:"
     , PP.indent 4 $ PP.pretty (PF.prfTripleStatus prf)
     ]
 pretty (PF.ProofExpr prf@PF.ProofDomain{}) = PP.vsep
   [ "Registers:"
   , PP.indent 4 $ prettyRegs
   , "Stack Memory:" <+> ppPolarity (PF.prfMemoryDomainPolarity $ PF.prfDomainStackMemory prf)
   , PP.indent 4 $ prettyMem (PF.prfDomainStackMemory prf)
   , "Global Memory:" <+> ppPolarity (PF.prfMemoryDomainPolarity $ PF.prfDomainGlobalMemory prf)
   , PP.indent 4 $ prettyMem (PF.prfDomainGlobalMemory prf)
   ]
   where
     prettyRegs = PP.vsep (map ppReg (collapseRegState (Proxy @sym) (PF.prfDomainRegisters prf)))

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

 pretty (PF.ProofExpr prf@PF.ProofStatus{}) = case PF.prfStatus prf of
   PF.Unverified -> "Not verified"
   PF.VerificationSkipped -> "Skipped (assumed)"
   PF.VerificationSuccess -> "Succeeded"
   PF.VerificationFail result -> PP.vsep [ "Failed:", PP.pretty result ]



collapseRegState ::
  forall sym arch.
  PT.ValidSym sym =>
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
  PT.ValidSym sym =>
  PA.ValidArch arch =>
  PF.ProofMemoryDomain (ProofSym sym arch) ->
  [(Some (PMC.MemCell sym arch), W4.Pred sym)]
collapseProofMemoryDomain memdom = mapMaybe go $ MapF.toList (PF.prfMemoryDomain memdom)
  where
    go :: MapF.Pair (PMC.MemCell sym arch)
                    (Const (W4.Pred sym))
          -> Maybe (Some (PMC.MemCell sym arch), W4.Pred sym)
    go (MapF.Pair cell (Const p)) =
        case W4.asConstantPred p of
          Just False -> Nothing
          _ -> Just (Some cell, p)

-- | Specializing 'ProofExpr' and 'BlockSliceTransition' to concrete values.
data ProofGround arch

type instance PF.ProofBlock (ProofGround arch) = PT.ConcreteBlock arch
type instance PF.ProofRegister (ProofGround arch) = MM.ArchReg arch
type instance PF.ProofMemCell (ProofGround arch) = GroundMemCell arch
type instance PF.ProofBV (ProofGround arch) = GroundBV
type instance PF.ProofCounterExample (ProofGround arch) = InequivalenceResult arch
type instance PF.ProofPredicate (ProofGround arch) = Bool
type instance PF.ProofMacawValue (ProofGround arch) = GroundMacawValue
type instance PF.ProofBlockExit (ProofGround arch) = GroundBlockExit arch
-- no additional context needed for ground values
type instance PF.ProofContext (ProofGround arch) = ()

instance PA.ValidArch arch => PF.IsProof (ProofGround arch)



data GroundBV n where
  GroundBV :: W4.NatRepr n -> BVS.BV n -> GroundBV n
  GroundLLVMPointer :: GroundLLVMPointer n -> GroundBV n
  deriving Eq

instance Show (GroundBV n) where
  show = ppGroundBV

ppGroundBV :: GroundBV w -> String
ppGroundBV gbv = case gbv of
  GroundBV w bv -> BVS.ppHex w bv
  GroundLLVMPointer ptr -> ppLLVMPointer ptr

groundBVWidth :: GroundBV n -> W4.NatRepr n
groundBVWidth gbv = case gbv of
  GroundBV nr _ -> nr
  GroundLLVMPointer ptr -> ptrWidth ptr

instance TestEquality GroundBV where
  testEquality bv bv' = case testEquality (groundBVWidth bv) (groundBVWidth bv') of
    Just Refl | bv == bv' -> Just Refl
    _ -> Nothing

instance OrdF GroundBV where
  compareF (GroundBV w bv) (GroundBV w' bv') =
    lexCompareF w w' $ fromOrdering $ compare bv bv'
  compareF (GroundLLVMPointer ptr) (GroundLLVMPointer ptr') = compareF ptr ptr'
  compareF (GroundBV _ _) _ = LTF
  compareF (GroundLLVMPointer _) _ = GTF

instance Ord (GroundBV n) where
  compare bv bv' = toOrdering (compareF bv bv')

data GroundLLVMPointer n where
  GroundLLVMPointerC ::
      { ptrWidth :: W4.NatRepr n
      , _ptrRegion :: Natural
      , _ptrOffset :: BVS.BV n
      } -> GroundLLVMPointer n
  deriving Eq

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

ppLLVMPointer :: GroundLLVMPointer w -> String
ppLLVMPointer (GroundLLVMPointerC bitWidthRepr reg offBV) = concat
  [ pad 3 (show reg)
  , "+0x"
  , padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")
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
  compare (GroundLLVMPointerC _ reg off) (GroundLLVMPointerC _ reg' off') =
    compare reg reg' <> compare off off'

instance OrdF GroundLLVMPointer where
  compareF ptr ptr' =
    lexCompareF (ptrWidth ptr) (ptrWidth ptr') $ fromOrdering $ compare ptr ptr'

instance Show (GroundLLVMPointer n) where
  show ptr = ppLLVMPointer ptr

mkGroundBV :: forall n.
  W4.NatRepr n ->
  Natural ->
  BVS.BV n ->
  GroundBV n
mkGroundBV nr reg bv = case reg > 0 of
 True -> GroundLLVMPointer $ GroundLLVMPointerC nr reg bv
 False -> GroundBV nr bv

groundBVAsPointer :: GroundBV n -> GroundLLVMPointer n
groundBVAsPointer gbv = case gbv of
  GroundLLVMPointer ptr -> ptr
  GroundBV w bv -> GroundLLVMPointerC w 0 bv

type family ConcreteValue (tp :: CT.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundBV w
type instance ConcreteValue (CT.MaybeType (CLM.LLVMPointerType w)) = Maybe (GroundBV w)
type instance ConcreteValue CT.BoolType = Bool
type instance ConcreteValue (CT.StructType CT.EmptyCtx) = ()

type ValidMacawType tp = (Eq (ConcreteValue (MS.ToCrucibleType tp)), Show (ConcreteValue (MS.ToCrucibleType tp)))


data GroundMemCell arch w where
  GroundMemCell ::
    { grndCellPtr :: GroundLLVMPointer (MM.ArchAddrWidth arch)
    -- | width of this cell in bytes
    , grndCellWidth :: W4.NatRepr w
    -- | true if this cell is a stack pointer
    , grndCellStack :: Bool
    } -> GroundMemCell arch w

instance TestEquality (GroundMemCell arch) where
  testEquality (GroundMemCell ptr1 w1 s1) (GroundMemCell ptr2 w2 s2)
    | Just Refl <- testEquality w1 w2
    , Just Refl <- testEquality ptr1 ptr2
    , s1 == s2
    = Just Refl
  testEquality _ _ = Nothing

instance OrdF (GroundMemCell arch) where
  compareF (GroundMemCell ptr1 w1 s1) (GroundMemCell ptr2 w2 s2) =
    lexCompareF w1 w2 $ fromOrdering $ compare ptr1 ptr2 <> compare s1 s2

instance PP.Pretty (GroundMemCell arch w) where
  pretty (GroundMemCell ptr _ _) = PP.pretty $ ppLLVMPointer ptr

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

instance PA.ValidArch arch => PP.Pretty (InequivalenceResult arch) where
  pretty ineq = PP.vsep [ "Reason:" <+> PP.pretty (show (ineqReason ineq)), ppBlockSliceTransition (ineqPre ineq) (ineqPost ineq) (ineqSlice ineq) ]

type GroundDomain arch = PF.ProofExpr (ProofGround arch) PF.ProofDomainType
type GroundRegOp arch = PF.BlockSliceRegOp (ProofGround arch)
type GroundMemOp arch = PF.BlockSliceMemOp (ProofGround arch)
  

ppBlockSliceTransition ::
  PA.ValidArch arch =>
  -- | pre-domain
  GroundDomain arch ->
  -- | post-domain
  GroundDomain arch ->
  PF.BlockSliceTransition (ProofGround arch) ->
  PP.Doc a
ppBlockSliceTransition pre post bs = PP.vsep $
  [ "Block Exit Condition:" <+> PT.ppPatchPairCEq (PP.pretty . ppExitCase) (fmap grndBlockCase $ PF.slBlockExitCase bs)
  ,  "Initial register state:"
  , ppRegs pre (PF.slRegState $ PF.slBlockPreState bs)
  , "Initial memory state:"
  , ppMemCellMap pre (PF.slMemState $ PF.slBlockPreState bs)
  , "Final register state:"
  , ppRegs post (PF.slRegState $ PF.slBlockPostState bs)
  , "Final memory state:"
  , ppMemCellMap post (PF.slMemState $ PF.slBlockPostState bs)
  , "Block Return Address:" <+> PT.ppPatchPairCEq (\v -> ppMaybe v (PP.pretty . ppLLVMPointer)) (fmap grndBlockReturn $ PF.slBlockExitCase bs)
  ]

ppMemCellMap ::
  PA.ValidArch arch =>
  GroundDomain arch ->
  MapF.MapF (GroundMemCell arch) (GroundMemOp arch) ->
  PP.Doc a
ppMemCellMap dom cells = let
  ppCells = mapMaybe (\(Pair cell v) -> ppCellVal dom cell v) $ MapF.toList cells
  in PP.vsep ppCells

ppRegs ::
  PA.ValidArch arch =>
  -- | domain that this register set was checked for equivalence under
  GroundDomain arch ->
  MM.RegState (MM.ArchReg arch) (GroundRegOp arch) ->
  PP.Doc a
ppRegs dom regs = let
  rm = MapF.toList $ MM.regStateMap regs
  docs' = map (\(Pair reg op) -> ppRegVal dom reg op) rm
  docs = catMaybes docs'
  diff = length docs' - length docs
  in (PP.vsep docs) <> PP.line <> (".. and" <+> PP.pretty diff <+> "zero-valued registers")
  

isGroundBVZero :: GroundBV w -> Bool
isGroundBVZero (GroundBV _ ptr) = BVS.asUnsigned ptr == 0
isGroundBVZero _ = False


ppRegVal ::
  PA.ValidArch arch =>
  GroundDomain arch ->
  MM.ArchReg arch tp ->
  GroundRegOp arch tp ->
  Maybe (PP.Doc a)
ppRegVal dom reg regOp = case PF.slRegOpRepr regOp of
  CLM.LLVMPointerRepr _ ->
    let
      PT.PatchPairC (GroundMacawValue obv) (GroundMacawValue pbv) = vals
    in case isGroundBVZero obv && isGroundBVZero pbv of
         True -> Nothing
         False -> Just $ ppSlotVal
  _ -> Just $ ppSlotVal
  where
    vals = PF.slRegOpValues regOp
    ppSlotVal = PP.pretty (showF reg) <> ":" <+> ppVals <+> ppDom

    ppDom = case regInDomain dom reg of
      True -> PP.emptyDoc
      False -> "| Excluded"
    
    ppVals = case PF.slRegOpEquiv regOp of
      True -> PP.pretty $ PT.pcOriginal vals
      False -> PT.ppPatchPairC PP.pretty vals

regInDomain ::
  PA.ValidArch arch =>
  GroundDomain arch ->
  MM.ArchReg arch tp ->
  Bool
regInDomain dom r = getConst $ PF.prfDomainRegisters (PF.unApp dom) ^. MM.boundValue r 


ppCellVal ::
  PA.ValidArch arch =>
  GroundDomain arch ->
  GroundMemCell arch n ->
  GroundMemOp arch tp ->
  Maybe (PP.Doc a)
ppCellVal dom cell memOp = case PF.slMemOpCond memOp of
    True -> Just $ ppSlotVal
    False -> Nothing
  where
    vals = PF.slMemOpValues memOp
    ppSlotVal = PP.pretty cell <> ":" <+> ppVals <+> ppDom

    ppDom = case cellInDomain dom cell of
      True -> PP.emptyDoc
      False -> "| Excluded"
    
    ppVals = case PF.slMemOpEquiv memOp of
      True -> PP.pretty $ show (PT.pcOriginal vals)
      False -> PT.ppPatchPairC (PP.pretty . show) vals

cellInMemDomain ::
  PA.ValidArch arch =>
  PF.ProofMemoryDomain (ProofGround arch) ->
  GroundMemCell arch n ->
  Bool
cellInMemDomain dom cell  = case MapF.lookup cell (PF.prfMemoryDomain dom) of
    Just (Const p) -> p == PF.prfMemoryDomainPolarity dom
    Nothing -> not $ PF.prfMemoryDomainPolarity dom


cellInDomain ::
  PA.ValidArch arch =>
  GroundDomain arch ->
  GroundMemCell arch n ->
  Bool
cellInDomain dom cell = case grndCellStack cell of
  True -> cellInMemDomain (PF.prfDomainStackMemory (PF.unApp dom)) cell
  False -> cellInMemDomain (PF.prfDomainGlobalMemory (PF.unApp dom)) cell

ppExitCase :: MS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MS.MacawBlockEndJump -> "arbitrary jump"
  MS.MacawBlockEndCall -> "function call"
  MS.MacawBlockEndReturn -> "function return"
  MS.MacawBlockEndBranch -> "branch"
  MS.MacawBlockEndArch -> "syscall"
  MS.MacawBlockEndFail -> "analysis failure"
