{-|
Module           : Pate.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Presenting counter-examples to failed equivalence checks
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}

module Pate.CounterExample 
  ( throwInequivalenceResult
  , getInequivalenceResult
  --, ppEquivalenceError
  --, ppAbortedResult
  --, ppPreRegs
  --, showModelForPtr
  --, ppMemDiff
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.Reader as CMR
import           Control.Applicative

import qualified Data.BitVector.Sized as BVS
import qualified Data.Set as S
import           Data.Maybe (catMaybes)
import           Data.Monoid ( Sum(..) )
import           Data.Proxy ( Proxy(..) )

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )


import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.MuxTree as C

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Partial as W4P

import           Pate.Equivalence
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import           Pate.Types
import qualified Pate.Proof as PF

throwInequivalenceResult ::
  Maybe (InequivalenceResult arch) ->
  EquivM sym arch ()
throwInequivalenceResult Nothing = return ()
throwInequivalenceResult (Just ir) = throwHere $ InequivalentError ir

-- | Convert the result of symbolic execution into a structured slice
-- representation
simBundleToSlice ::
  -- | symbolic representation of the block slice semantics
  PS.SimBundle sym arch ->
  -- | pre-domain
  PE.StatePred sym arch ->
  -- | post-domain
  PE.StatePred sym arch ->
  EquivM sym arch (ExprBlockSlice sym arch)
simBundleToSlice bundle precond postcond = withSym $ \sym -> do
  let
    ecaseO = simOutBlockEnd $ simOutO $ bundle
    ecaseP = simOutBlockEnd $ simOutP $ bundle
  footprints <- getFootprints bundle
  reads <- memPredToList <$> liftIO $ footPrintsToPred sym footprints (W4.truePred sym)
  writes <- memPredToList <$> liftIO $ footPrintsToPred sym footprints (W4.falsePred sym)

  preMem <- mapM (memCellToOp precond init) reads
  postMem <- mapM (memCellToOp postcond fin) writes

  preRegs <- PT.zipRegStates (simInRegs $ simInO bundle) (simInRegs $ simInP bundle) (getReg precond)
  postRegs <- PT.zipRegStates (simOutRegs $ simOutO bundle) (simOutRegs $ simOutP bundle) (getReg postcond)
  
  let
    preState = PF.BlockSliceState preMem preRegs
    postState = PF.BlockSliceState postMem postRegs
  return $ PF.BlockSlice preState postState
  where
    init = fmapFC PT.simInState (simIn bundle)
    fin = fmapFC PT.simOutState (simOut bundle)

    getReg ::
      PE.StatePred sym arch ->
      MM.ArchReg arch tp ->
      PSR.MacawRegEntry sym tp ->
      PSR.MacawRegEntry sym tp ->
      EquivM sym arch (BlockSliceRegister (PF.BSExprLeaf sym arch))
    getReg stPred reg valO valP = withSym $ \sym -> do
      eqRel <- CMR.asks envBaseEquiv
      inDomain <- liftIO @ regPredAt sym reg
      isEquiv <- liftIO $ applyRegEquivRelation (eqRelRegs eqRel) reg valO valP
      return $ PF.BlockSliceRegister
        (PF.BSExprRegister reg)
        (PF.PatchPairC (PF.BFMacawValue valO) (PF.BFMacawValue valP))
        (PF.BSBoolType isEquiv)
        (PF.BSBoolType inDomain)
    
    memCellToOp ::
      PE.StatePred sym arch ->
      PT.PatchPair (SimState sym arch) -> 
      (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      EquivM sym arch (Maybe (PF.BlockSliceMemOp (PF.BSExprLeaf sym arch)))
    memCellToOp stPred ppair@(PT.PatchPair stO stP) (Some cell, cond) = withSym $ \sym -> do
      valO <- PMC.readMemCell sym (simMem stO) cell
      valP <- PMC.readMemCell sym (simMem stP) cell
      eqRel <- CMR.asks envBaseEquiv
      
      isValidStack <- liftIO $ applyMemEquivRelation (eqRelStack eqRel) cell valO valP
      isValidGlobalMem <- liftIO $ applyMemEquivRelation (eqRelMem eqRel) cell valO valP
      
      inStackDomain <- liftIO $ memPredAt sym (predStack stPred) cell
      inGlobalMemDomain <- liftIO $ memPredAt sym (predMem stPred) cell

      isEqStack <- liftIO $ W4.andPred sym isValidStack inStackDomain
      isEqDomain <- liftIO $ W4.andPred sym isValidGlobalMem inGlobalMemDomain
      isEquiv <- liftIO $ W4.orPred sym isEqStack isEqDomain
  
      inDomain <- liftIO $ W4.orPred sym inStackDomain inGlobalMemDomain

      case W4.asConstantPred inDomain of
        Just False -> return Nothing
        _ -> return $ Just $ PF.BlockSliceMemOp
          (PF.BSExprMemCell cell)
          (PF.PatchPairC (PF.BSExprBV valO) (PF.BSExprBV valP))
          (PF.BSBoolType isEquiv)
          (PF.BSBoolType inDomain)

groundExprLeaf ::
  SymGroundEvalFn sym ->
  PF.BSExprLeaf sym arch tp ->
  EquivM sym arch (PF.BSGroundExprLeaf arch)
groundExprLeaf fn = \case
  PF.BSExprMemCell (PMC.MemCell ptr w _) ->
    PF.BSGroundMemCell <$> groundLLVMPointer fn ptr <*> return (NR.natValue w)
  PF.BSExprBV bv -> PF.BSGroundBV <$> groundBV fn bv
  PF.BSExprMacawValue e@PSR.MacawRegEntry{} -> PF.BSGroundCrucibleValue <$> concreteValue fn e
  PF.BSExprBool p -> PF.BSGroundBool <$> execGroundFn fn p
  PF.BSExprBlockExit exit ->
    PF.BSGroundBlockExit <$> groundBlockEndCase fn exit <*> groundReturnPtr fn exit
  PF.BSExprRegister r -> PF.BSGroundRegister r


groundSlice ::
  SymGroundEvalFn sym ->
  ExprBlockSlice sym arch ->
  EquivM sym arch (GroundBlockSlice arch)
groundSlice slice = TF.traverseF (groundExprLeaf fn)


-- | Takes a model resulting from a failed equivalence check, and evaluates
-- it on the symbolic program state to produce an 'InequivalenceResult', representing
-- a structured description of a counterexample.
getInequivalenceResult ::
  forall sym arch.
  HasCallStack =>
  -- | the default reason to report why equality does not hold, to be used
  -- when memory and registers are otherwise equivalent
  InequivalenceReason ->
  -- | the pre-domain that was assumed initially equivalence before this slice executed
  PE.StatePred sym arch ->
  -- | the post-domain that was attempted to be proven equivalence after this slice executed
  PE.StatePred sym arch ->
  -- | the input and symbolic output states of the block pair that was evaluated
  SimBundle sym arch ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (InequivalenceResult arch)
getInequivalenceResult defaultReason eqRel bundle fn  = do
  slice <- simBundleToSlice bundle >>= groundSlice fn
  let reason = fromMaybe defaultReason (getInequivalenceReason slice)
  return $ InequivalenceResult slice reason

isMemOpValid :: PF.BlockSliceMemOp (PF.BSGroundExprLeaf arch) -> Bool
isMemOpValid mop = let
  PF.BSGroundBool isEquiv = PF.bsMemOpEquiv bop
  PF.BSGroundBool isInDomain = PF.bsMemOpInDomain bop
  in (not isInDomain) || isEquiv

isRegValid :: PF.BlockSliceRegister (PF.BSGroundExprLeaf arch) -> Bool
isRegValid mop = let
  PF.BSGroundBool isEquiv = PF.bsRegisterEquiv bop
  PF.BSGroundBool isInDomain = PF.bsRegisterInDomain bop
  in (not isInDomain) || isEquiv

getInequivalenceReason ::
  PF.BlockSliceState (PF.BSGroundExprLeaf arch) ->
  Maybe InequivalenceReason
getInequivalenceReason st =
  if | not $ all isMemOpValid (PF.bsMemState st) -> Just InequivalentMemory
     | not $ all isRegValid (PF.bsRegState st) -> Just InequivalentRegisters
     | _ -> Nothing


groundMuxTree ::
  SymGroundEvalFn sym ->
  C.MuxTree sym a ->
  EquivM sym arch a
groundMuxTree fn mt =
  withSym $ \sym ->
  IO.withRunInIO $ \runInIO -> do
    C.collapseMuxTree sym (\p a b -> do
                              p' <- runInIO (execGroundFn fn p)
                              return $ if p' then a else b) mt
groundBlockEndCase ::
  forall sym arch.
  SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch MS.MacawBlockEndCase
groundBlockEndCase fn blkend = withSym $ \sym -> do
  blkend_tree <- liftIO $ MS.blockEndCase (Proxy @arch) sym blkend
  groundMuxTree fn blkend_tree

groundBV ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (GroundBV w)
groundBV fn (CLM.LLVMPointer reg off) = do
  W4.BaseBVRepr w <- return $ W4.exprType off
  greg <- execGroundFn fn reg
  goff <- execGroundFn fn off
  let gbv = mkGroundBV w greg goff
  return gbv

groundLLVMPointer :: forall sym arch.
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (GroundLLVMPointer (MM.ArchAddrWidth arch))
groundLLVMPointer fn ptr = groundBVAsPointer <$> groundBV fn ptr


concreteValue ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (ConcreteValue (MS.ToCrucibleType tp))
concreteValue fn e
  | CLM.LLVMPointerRepr _ <- PSR.macawRegRepr e
  , ptr <- PSR.macawRegValue e = do
    groundBV fn ptr
  | CT.BoolRepr <- PSR.macawRegRepr e
  , val <- PSR.macawRegValue e = execGroundFn fn val
  | CT.StructRepr Ctx.Empty <- PSR.macawRegRepr e = return ()
concreteValue _ e = throwHere (UnsupportedRegisterType (Some (PSR.macawRegRepr e)))

groundReturnPtr ::
  forall sym arch.
  HasCallStack =>
  SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch)))
groundReturnPtr fn blkend = case MS.blockEndReturn (Proxy @arch) blkend of
  W4P.PE p e -> execGroundFn fn p >>= \case
    True -> Just <$> groundLLVMPointer fn e
    False -> return Nothing
  W4P.Unassigned -> return Nothing

-------------------------------------------------
-- Proof leaf types


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

instance IsBoolLike (BSGroundExprLeaf arch 'BSBoolType) where
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



data InequivalenceResult arch =
  InequivalenceResult
    { ineqSlice :: GroundBlockSlice arch
    , ineqReason :: PT.InequivalenceReason
    }
