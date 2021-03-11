{-|
Module           : Pate.ProofInstances
Copyright        : (c) Galois, Inc 2021
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Instantiations for the leaves of the proof types
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pate.ProofInstances
  ( BSExprLeaf(..)
  , BSGroundExprLeaf(..)
  , BlockSliceRegister(..)
  , BlockSliceMemOp(..)
  , PatchPairC(..)
  , ExprBlockSlice
  , GroundBlockSlice
  , InequivalenceResult(..)
  , ProofExpr
  , BlockSliceState(..)
  )
  
  where

import qualified Data.Parameterized.TraversableF as TF
import           Data.Functor.Identity
import qualified Data.Macaw.CFG as MM

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.ExprMappable as PEM
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.MemCell as PMC
import qualified Pate.SimState as PS
import qualified Pate.Parallel as Par

import qualified What4.Interface as W4

data VerificationStatus arch =
    Unverified
  | VerificationSkipped
  | VerificationSuccess
  | VerificationFail (InequivalenceResult arch)

data InequivalenceResult arch =
  InequivalenceResult
    { ineqSlice :: GroundBlockSlice arch
    , ineqReason :: PT.InequivalenceReason
    }


data ProofExprLeafs sym arch future tp where
  ProofExprBlock :: PT.ConcreteBlock arch bin -> ProofExprLeafs sym arch future PF.ProofBlockType
  ProofExprRegister :: MM.ArchReg arch tp -> ProofExprLeafs sym arch future PF.ProofRegisterType
  ProofExprMemCell :: PMC.MemCell sym arch w -> ProofExprLeafs sym arch future PF.ProofMemoryCellType
  ProofExprStatus :: future (VerificationStatus arch) -> ProofExprLeafs sym arch future PF.ProofStatusType
  ProofExprPred :: W4.Pred sym -> ProofExprLeafs sym arch future PF.ProofPredicateType
  ProofExprPolarity :: W4.Pred sym -> ProofExprLeafs sym arch future PF.ProofMemoryPolarityType
  ProofExprContext :: PT.PatchPair (PS.SimState sym arch) -> ProofExprLeafs sym arch future PF.ProofContextType

joinProofExpr ::
  ProofExprLeafs sym arch Par.Future tp ->
  IO (ProofExprLeafs sym arch Identity tp)
joinProofExpr = \case
  ProofExprStatus status -> ProofExprStatus <$> (Identity <$> Par.joinFuture status)
  ProofExprBlock blk -> return $ ProofExprBlock blk
  ProofExprRegister reg -> return $ ProofExprRegister reg
  ProofExprMemCell cell -> return $ ProofExprMemCell cell
  ProofExprPred p -> return $ ProofExprPred p
  ProofExprPolarity p -> return $ ProofExprPolarity p
  ProofExprContext st -> return $ ProofExprContext st

instance (PT.ValidArch arch, PT.ValidSym sym) => PP.Pretty (ProofExprLeafs sym arch Identity tp) where
  pretty = \case
    ProofExprBlock blk -> PP.pretty $ PT.ppBlock blk
    ProofExprRegister reg -> PP.pretty $ showF reg
    ProofExprMemCell cell ->
      let CLM.LLVMPointer reg off = PMC.cellPtr cell
      in PP.pretty (showF reg) <> "+" <> PP.pretty (showF off)
    ProofExprStatus st -> case runIdentity st of
      Unverified -> "Not verified"
      VerificationSkipped -> "Skipped (assumed)"
      VerificationSuccess -> "Succeeded"
      VerificationFail result -> PP.vsep [ "Failed:", PP.pretty result ]
    ProofExprPred p | Just True <- W4.asConstantPred p -> PP.emptyDoc
    ProofExprPred _ -> "Conditional"
    ProofExprContext _ -> "Proof Context"
    ProofExprPolarity p | Just True <- W4.asConstantPred p -> "Inclusive"
    ProofExprPolarity p | Just True <- W4.asConstantPred p -> "Exclusive"
    ProofExprPolarity _ -> "Symbolic Polarity"

instance PEM.ExprMappable sym (ProofExprLeafs sym arch future tp) where
  mapExpr sym f leaf = case leaf of
    ProofExprMemCell cell -> ProofExprMemCell <$> PEM.mapExpr sym f cell
    ProofExprPred p -> ProofExprPred <$> f p
    ProofExprContext st -> ProofExprContext <$> PEM.mapExpr sym f st 
    _ -> return leaf



type ProofExprFuture sym arch = ProofBlockSlice (ProofExprLeafs sym arch Par.Future)
type ProofExpr sym arch = ProofBlockSlice (ProofExprLeafs sym arch Identity)

data SomeProof (arch :: *) where
  SomeProof :: PT.Sym sym -> ProofExpr sym arch -> SomeProof arch

data SomeProofTriple (arch :: *) where
  SomeProofTriple :: PT.Sym sym -> ProofTriple (ProofExprLeafs sym arch Identity) -> SomeProofTriple arch


finalizeProof :: ProofExprFuture sym arch -> IO (ProofExpr sym arch)
finalizeProof = TF.traverseF joinProofExpr




data BlockSliceElemType =
    BSMemCellType
  | BSBVType
  | BSMacawValueType MT.Type
  | BSBoolType
  | BSBlockExitType
  | BSRegisterType MT.Type

class (IsBoolLike (e 'BSBoolType),
       (forall tp. Eq (e tp)),
       (forall tp. PP.Pretty (e tp))) => PrettySliceElem e


data BlockSliceState (e :: BlockSliceElemType -> *) =
  BlockSliceState
    {
      bsMemState :: [BlockSliceMemOp e]
    , bsRegState :: [BlockSliceRegister e]
    }

instance TF.FunctorF BlockSliceState where
  fmapF = TF.fmapFDefault

instance TF.FoldableF BlockSliceState where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF BlockSliceState where
  traverseF f (BlockSliceState a1 a2) =
    BlockSliceState
      <$> traverse (TF.traverseF f) a1
      <*> traverse (TF.traverseF f) a2

-- | A block slice represents the semantics of executing a sequence of blocks,
-- from some initial memory and register state to a final memory and register state
data BlockSlice (e :: BlockSliceElemType -> *) =
  BlockSlice
    { 
      bsPreState :: BlockSliceState e
    , bsPostState :: BlockSliceState e
    , bsExitCase :: PatchPairC (e 'BSBlockExitType)
    }


instance TF.FunctorF BlockSlice where
  fmapF = TF.fmapFDefault

instance TF.FoldableF BlockSlice where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF BlockSlice where
  traverseF f (BlockSlice a1 a2 a3) =
    BlockSlice
      <$> TF.traverseF f a1
      <*> TF.traverseF f a2
      <*> traverse f a3


data BlockSliceMemOp (e :: BlockSliceElemType -> *) =
  BlockSliceMemOp
    {
      bsMemOpCell :: e 'BSMemCellType
    , bsMemOpValues :: PatchPairC (e 'BSBVType)
    -- | true if the values of the memory operation are considered equivalent
    , bsMemOpEquiv :: e 'BSBoolType
    -- | true if the cell of the memory operation is within the domain that this
    -- block slice is checked in
    , bsMemOpInDomain :: e 'BSBoolType
    }

instance TF.FunctorF BlockSliceMemOp where
  fmapF = TF.fmapFDefault

instance TF.FoldableF BlockSliceMemOp where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF BlockSliceMemOp where
  traverseF f (BlockSliceMemOp a1 a2 a3 a4) =
    BlockSliceMemOp
      <$> f a1
      <*> traverse f a2
      <*> f a3
      <*> f a4


instance PrettySliceElem e => PP.Pretty (BlockSliceMemOp e) where
  pretty mop = PP.pretty (bsMemOpCell mop) <> ":" <+> ppPatchPairEq PP.pretty (bsMemOpValues mop)
    <+> prettyEquiv (bsMemOpEquiv mop) (bsMemOpInDomain mop)

prettyEquiv :: PrettySliceElem e => e 'BSBoolType -> e 'BSBoolType -> PP.Doc a
prettyEquiv isEq isInDomain = case (asBool isEq, asBool isInDomain) of
  (Just True, _) -> PP.emptyDoc
  (Just False, Just False) -> "Excluded"
  _ -> "Unequal"

data BlockSliceRegister (e :: BlockSliceElemType -> *) where
  BlockSliceRegister ::
    {
      bsRegister :: e ('BSRegisterType tp)
    , bsRegisterValues :: PatchPairC (e ('BSMacawValueType tp))
    , bsRegisterEquiv :: e 'BSBoolType
    , bsRegisterInDomain :: e 'BSBoolType
    } -> BlockSliceRegister e

instance TF.FunctorF BlockSliceRegister where
  fmapF = TF.fmapFDefault

instance TF.FoldableF BlockSliceRegister where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF BlockSliceRegister where
  traverseF f (BlockSliceRegister a1 a2 a3 a4) =
    BlockSliceRegister
      <$> f a1
      <*> traverse f a2
      <*> f a3
      <*> f a4

instance PrettySliceElem e => PP.Pretty (BlockSliceRegister e) where
  pretty bsr@(BlockSliceRegister reg vals _ _) = PP.pretty reg <> ":" <+> ppPatchPairEq PP.pretty vals
    <+> prettyEquiv (bsRegisterEquiv bsr) (bsRegisterInDomain bsr)

instance PrettySliceElem e => PP.Pretty (BlockSlice e) where
  pretty bs = PP.vsep $
    [ "Block Exit Condition:" <+> ppPatchPairEq PP.pretty (bsExitCase bs)
    ,  "Initial register state:"
    , PP.vsep $ map PP.pretty (bsRegState $ bsPreState bs)
    , "Initial memory state:"
    , PP.vsep $ map PP.pretty (bsMemState $ bsPreState bs)
    , "Final memory state:"
    , PP.vsep $ map PP.pretty (bsRegState $ bsPostState bs) 
    , "Final register state:"
    , PP.vsep $ map PP.pretty (bsRegState $ bsPostState bs)
    ]

data BSGroundExprLeaf arch tp where
  BSGroundMemCell :: PT.GroundLLVMPointer (MM.ArchAddrWidth arch) -> Natural -> BSGroundExprLeaf arch 'BSMemCellType
  BSGroundBV :: PT.GroundBV w -> BSGroundExprLeaf arch 'BSBVType
  BSGroundMacawValue :: PSR.ValidMacawType tp => CT.TypeRepr (MS.ToCrucibleType tp) -> PT.ConcreteValue (MS.ToCrucibleType tp) -> BSGroundExprLeaf arch ('BSMacawValueType tp)
  BSGroundBool :: Bool -> BSGroundExprLeaf arch 'BSBoolType
  BSGroundBlockExit :: MS.MacawBlockEndCase -> Maybe (PT.GroundLLVMPointer (MM.ArchAddrWidth arch)) -> BSGroundExprLeaf arch 'BSBlockExitType
  BSGroundRegister :: MM.ArchReg arch tp -> BSGroundExprLeaf arch ('BSRegisterType tp)

instance PT.ValidArch arch => Eq (BSGroundExprLeaf arch tp) where
  a == b = case (a, b) of
    (BSGroundMemCell a1 a2, BSGroundMemCell b1 b2) | a1 == b1, a2 == b2 -> True
    (BSGroundBV a1, BSGroundBV b1) | Just Refl <- testEquality a1 b1 -> True
    (BSGroundMacawValue a1 a2, BSGroundMacawValue b1 b2)
      | Just Refl <- testEquality a1 b1
      , a2 == b2
      -> True
    (BSGroundBool a1, BSGroundBool b1) | a1 == b1 -> True
    (BSGroundBlockExit a1 a2, BSGroundBlockExit b1 b2) | a1 == b1, a2 == b2 -> True
    (BSGroundRegister a1, BSGroundRegister b1) | Just Refl <- testEquality a1 b1 -> True
    _ -> False


instance PT.ValidArch arch => PP.Pretty (BSGroundExprLeaf arch tp) where
  pretty = \case
    BSGroundMemCell ptr _ -> PP.pretty $ PT.ppLLVMPointer ptr
    BSGroundBV bv -> PP.pretty $ show bv
    BSGroundMacawValue repr cv -> case repr of
      CLM.LLVMPointerRepr _ -> PP.pretty $ show cv
      _ -> "Unsupported Value"
    BSGroundBool b -> PP.pretty $ show b
    BSGroundBlockExit ec Nothing -> PP.pretty $ ppExitCase ec
    BSGroundBlockExit ec (Just ptr) ->
      PP.pretty (ppExitCase ec) <+> "returning to" <+> PP.pretty (PT.ppLLVMPointer ptr)
    BSGroundRegister r -> PP.pretty $ showF r

instance PF.IsBoolLike (BSGroundExprLeaf arch 'BSBoolType) where
  asBool (BSGroundBool b) = Just b

instance PT.ValidArch arch => PrettySliceElem (BSGroundExprLeaf arch)

data BSExprLeaf sym arch tp where
  BSExprMemCell :: PMC.MemCell sym arch w -> BSExprLeaf sym arch 'BSMemCellType
  BSExprBV :: CLM.LLVMPtr sym w -> BSExprLeaf sym arch 'BSBVType
  BSExprMacawValue :: PSR.MacawRegEntry sym tp -> BSExprLeaf sym arch ('BSMacawValueType tp)
  BSExprBool :: W4.Pred sym -> BSExprLeaf sym arch 'BSBoolType
  BSExprBlockExit :: CS.RegValue sym (MS.MacawBlockEndType arch) -> BSExprLeaf sym arch 'BSBlockExitType
  BSExprRegister :: MM.ArchReg arch tp -> BSExprLeaf sym arch ('BSRegisterType tp)
 

type GroundBlockSlice arch = BlockSlice (BSGroundExprLeaf arch)
type ExprBlockSlice sym arch = BlockSlice (BSExprLeaf sym arch)



