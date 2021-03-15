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

module Pate.ProofInstances
  ( ProofSymLeafs(..)
  , ProofGroundLeafs(..)
  , InequivalenceResult(..)
  , ProofSymExpr
  , CounterExample
  , SomeProof(..)
  , SomeProofTriple(..)
  )
  
  where

import           GHC.Natural

import           Data.Parameterized.Classes

import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator.RegValue as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.ExprMappable as PEM
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.MemCell as PMC
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR

import qualified What4.Interface as W4
import qualified What4.ExprHelpers as WEH


data InequivalenceResult arch =
  InequivalenceResult
    { ineqSlice :: CounterExample arch
    , ineqReason :: PT.InequivalenceReason
    }


instance PT.ValidArch arch => PP.Pretty (InequivalenceResult arch) where
  pretty ineq = PP.vsep [ "Reason:" <+> PP.pretty (show (ineqReason ineq)), PP.pretty (ineqSlice ineq) ]

data ProofSymLeafs sym arch tp where
  ProofSymBlock :: PT.ConcreteBlock arch bin -> ProofSymLeafs sym arch PF.ProofBlockType
  ProofSymRegister :: MM.ArchReg arch tp -> ProofSymLeafs sym arch  PF.ProofRegisterType
  ProofSymMemCell :: PMC.MemCell sym arch w -> ProofSymLeafs sym arch PF.ProofMemCellType
  ProofSymCounterExample :: InequivalenceResult arch -> ProofSymLeafs sym arch PF.ProofCounterExampleType
  ProofSymPredicate :: W4.Pred sym -> ProofSymLeafs sym arch PF.ProofPredicateType
  ProofSymPolarity :: W4.Pred sym -> ProofSymLeafs sym arch PF.ProofPolarityType
  ProofSymContext :: PT.PatchPair (PS.SimState sym arch) -> ProofSymLeafs sym arch PF.ProofContextType
  ProofSymBlockExit :: CS.RegValue sym (MS.MacawBlockEndType arch) -> ProofSymLeafs sym arch PF.ProofBlockExitType
  ProofSymBV :: CLM.LLVMPtr sym w -> ProofSymLeafs sym arch (PF.ProofBVType w)
  ProofSymMacawValue :: PSR.MacawRegEntry sym tp -> ProofSymLeafs sym arch (PF.ProofMacawValueType tp)

instance (PT.ValidArch arch, PT.ValidSym sym) => PP.Pretty (ProofSymLeafs sym arch tp) where
  pretty = \case
    ProofSymBlock blk -> PP.pretty $ PT.ppBlock blk
    ProofSymRegister reg -> PP.pretty $ showF reg
    ProofSymMemCell cell ->
      let CLM.LLVMPointer reg off = PMC.cellPtr cell
      in PP.pretty (showF reg) <> "+" <> PP.pretty (showF off)
    ProofSymCounterExample ce -> PP.pretty ce
    ProofSymPredicate p | Just True <- W4.asConstantPred p -> PP.emptyDoc
    ProofSymPredicate _ -> "Conditional"
    ProofSymContext _ -> "Proof Context"
    ProofSymPolarity p | Just True <- W4.asConstantPred p -> "Inclusive"
    ProofSymPolarity p | Just True <- W4.asConstantPred p -> "Exclusive"
    ProofSymPolarity _ -> "Symbolic Polarity"
    ProofSymBlockExit _ -> "Symbolic Block Exit"
    ProofSymBV e -> ppPtr e
    ProofSymMacawValue me -> PP.pretty $ show me



ppPtr :: PT.ValidSym sym => CLM.LLVMPtr sym w -> PP.Doc a
ppPtr ( CLM.LLVMPointer reg off) = PP.pretty (showF reg) <> "+" <> PP.pretty (showF off)

instance W4.IsSymExprBuilder sym => PF.IsBoolLike (ProofSymLeafs sym arch PF.ProofPredicateType) where
  asBool (ProofSymPredicate p) = W4.asConstantPred p

instance Eq (ProofSymLeafs sym arch PF.ProofBlockType) where
  (ProofSymBlock blk) == (ProofSymBlock blk') =
       PT.concreteAddress blk == PT.concreteAddress blk'
    && PT.concreteBlockEntry blk == PT.concreteBlockEntry blk'

instance PT.ValidSym sym => Eq (ProofSymLeafs sym arch PF.ProofBlockExitType) where
  -- unused for symbolic values at the moment, and it's annoying to define 
  _ == _ = False

instance W4.IsSymExprBuilder sym => Eq (ProofSymLeafs sym arch (PF.ProofMacawValueType tp)) where
  (ProofSymMacawValue mv) == (ProofSymMacawValue mv') = mv == mv'
    
instance W4.IsSymExprBuilder sym => Eq (ProofSymLeafs sym arch (PF.ProofBVType n)) where
  (ProofSymBV bv) == (ProofSymBV bv') | Just Refl <- PT.ptrEquality bv bv' = True
  _ == _ = False

instance PT.ValidArch arch => Eq (ProofSymLeafs sym arch PF.ProofRegisterType) where
  (ProofSymRegister r1) == (ProofSymRegister r2) | Just Refl <- testEquality r1 r2 = True
  _ == _ = False

instance PT.ValidArch arch => Ord (ProofSymLeafs sym arch PF.ProofRegisterType) where
  compare (ProofSymRegister r1) (ProofSymRegister r2) = toOrdering $ compareF r1 r2

instance W4.IsSymExprBuilder sym => Eq (ProofSymLeafs sym arch PF.ProofMemCellType) where
  (ProofSymMemCell m1) == (ProofSymMemCell m2) | Just Refl <- testEquality m1 m2 = True
  _ == _ = False

instance W4.IsSymExprBuilder sym => Ord (ProofSymLeafs sym arch PF.ProofMemCellType) where
  compare (ProofSymMemCell m1) (ProofSymMemCell m2) = toOrdering $ compareF m1 m2

instance (PT.ValidArch arch, PT.ValidSym sym) => PF.PrettyProofLeafs (ProofSymLeafs sym arch)


data ProofGroundLeafs arch tp where
  -- unchanged from symbolic
  ProofGroundBlock :: PT.ConcreteBlock arch bin -> ProofGroundLeafs arch PF.ProofBlockType
  -- unchanged from symbolic
  ProofGroundRegister :: MM.ArchReg arch tp -> ProofGroundLeafs arch PF.ProofRegisterType
  ProofGroundPredicate :: Bool -> ProofGroundLeafs arch PF.ProofPredicateType
  ProofGroundMemCell :: PT.GroundLLVMPointer (MM.ArchAddrWidth arch) -> Natural -> ProofGroundLeafs arch PF.ProofMemCellType
  ProofGroundPolarity :: Bool -> ProofGroundLeafs arch PF.ProofPolarityType
  -- unchanged from symbolic
  ProofGroundCounterExample :: InequivalenceResult arch -> ProofGroundLeafs arch PF.ProofCounterExampleType
  -- unsupported
  ProofGroundContext :: ProofGroundLeafs arch PF.ProofContextType
  ProofGroundBV :: PT.GroundBV w -> ProofGroundLeafs arch (PF.ProofBVType w)
  ProofGroundBlockExit :: MS.MacawBlockEndCase -> Maybe (PT.GroundLLVMPointer (MM.ArchAddrWidth arch)) -> ProofGroundLeafs arch PF.ProofBlockExitType
  ProofGroundMacawValue :: PSR.ValidMacawType tp =>
    CT.TypeRepr (MS.ToCrucibleType tp) -> PT.ConcreteValue (MS.ToCrucibleType tp) -> ProofGroundLeafs arch (PF.ProofMacawValueType tp)


instance PT.ValidArch arch => PP.Pretty (ProofGroundLeafs arch tp) where
  pretty = \case
    ProofGroundBlock blk -> PP.pretty $ PT.ppBlock blk
    ProofGroundRegister reg -> PP.pretty $ showF reg
    ProofGroundPredicate p -> PP.pretty $ show p
    ProofGroundMemCell ptr _ -> PP.pretty $ PT.ppLLVMPointer ptr
    ProofGroundPolarity p -> PP.pretty $ show p
    ProofGroundCounterExample ce -> PP.pretty ce
    ProofGroundContext -> PP.emptyDoc
    ProofGroundBV bv -> PP.pretty $ show bv
    ProofGroundBlockExit ec Nothing -> PP.pretty $ ppExitCase ec
    ProofGroundBlockExit ec (Just ptr) ->
      PP.pretty (ppExitCase ec) <+> "returning to" <+> PP.pretty (PT.ppLLVMPointer ptr)    
    ProofGroundMacawValue repr cv -> case repr of
      CLM.LLVMPointerRepr _ -> PP.pretty $ show cv
      _ -> "Unsupported Value"

instance PF.IsBoolLike (ProofGroundLeafs arch PF.ProofPredicateType) where
  asBool (ProofGroundPredicate p) = Just p

instance Eq (ProofGroundLeafs arch PF.ProofBlockType) where
  (ProofGroundBlock blk) == (ProofGroundBlock blk') =
    PT.concreteAddress blk == PT.concreteAddress blk'
    && PT.concreteBlockEntry blk == PT.concreteBlockEntry blk'

instance Eq (ProofGroundLeafs arch PF.ProofBlockExitType) where
  (ProofGroundBlockExit ecase1 eret1) == (ProofGroundBlockExit ecase2 eret2) = ecase1 == ecase2 && eret1 == eret2

instance Eq (ProofGroundLeafs arch (PF.ProofMacawValueType tp)) where
  (ProofGroundMacawValue _ v1) == (ProofGroundMacawValue _ v2) = v1 == v2

instance Eq (ProofGroundLeafs arch (PF.ProofBVType n)) where
  (ProofGroundBV bv) == (ProofGroundBV bv') = bv == bv'

instance PT.ValidArch arch => Eq (ProofGroundLeafs arch PF.ProofRegisterType) where
  (ProofGroundRegister r1) == (ProofGroundRegister r2) | Just Refl <- testEquality r1 r2 = True
  _ == _ = False

instance PT.ValidArch arch => Ord (ProofGroundLeafs arch PF.ProofRegisterType) where
  compare (ProofGroundRegister r1) (ProofGroundRegister r2) = toOrdering $ compareF r1 r2

instance Eq (ProofGroundLeafs arch PF.ProofMemCellType) where
  (ProofGroundMemCell m1 n1) == (ProofGroundMemCell m2 n2) = m1 == m2 && n1 == n2

instance Ord (ProofGroundLeafs arch PF.ProofMemCellType) where
  compare (ProofGroundMemCell m1 n1) (ProofGroundMemCell m2 n2) = compare n1 n2 <> (toOrdering $ compareF m1 m2)

instance PT.ValidArch arch => PF.PrettyProofLeafs (ProofGroundLeafs arch)

instance PEM.ExprMappable sym (ProofSymLeafs sym arch tp) where
  mapExpr sym f leaf = case leaf of
    ProofSymMemCell cell -> ProofSymMemCell <$> PEM.mapExpr sym f cell
    ProofSymPredicate p -> ProofSymPredicate <$> f p
    ProofSymPolarity p -> ProofSymPolarity <$> f p
    ProofSymBV bv -> ProofSymBV <$> WEH.mapExprPtr sym f bv
    ProofSymMacawValue mv -> ProofSymMacawValue <$> PEM.mapExpr sym f mv
    ProofSymContext st -> ProofSymContext <$> PEM.mapExpr sym f st
    _ -> return leaf

instance (forall tp. PEM.ExprMappable sym (leaf tp)
         ,forall tp. PEM.ExprMappable sym (node tp)
         , PF.ValidLeaf leaf) =>
         PEM.ExprMappable sym (PF.ProofApp leaf node tp) where
  mapExpr sym f = PF.traverseProofApp (PEM.mapExpr sym f) (PEM.mapExpr sym f)


type ProofSymExpr sym arch = PF.ProofExpr (ProofSymLeafs sym arch) PF.ProofBlockSliceType
type CounterExample arch = PF.BlockSliceTransition (ProofGroundLeafs arch)

data SomeProof (arch :: *) where
  SomeProof :: PT.Sym sym -> ProofSymExpr sym arch -> SomeProof arch

data SomeProofTriple (arch :: *) where
  SomeProofTriple :: PT.Sym sym -> PF.ProofExpr (ProofSymLeafs sym arch) PF.ProofTripleType -> SomeProofTriple arch




ppExitCase :: MS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MS.MacawBlockEndJump -> "arbitrary jump"
  MS.MacawBlockEndCall -> "function call"
  MS.MacawBlockEndReturn -> "function return"
  MS.MacawBlockEndBranch -> "branch"
  MS.MacawBlockEndArch -> "syscall"
  MS.MacawBlockEndFail -> "analysis failure"
