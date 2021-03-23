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

module Pate.Proof.Ground 
  ( getInequivalenceResult
  , groundMacawValue
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR

import           Data.Maybe (fromMaybe)
import           Data.Proxy ( Proxy(..) )

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.MuxTree as C

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Partial as W4P

import qualified Pate.MemCell as PMC
import           Pate.Monad
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI


getInequivalenceResult ::
  PT.InequivalenceReason ->
  -- | pre-domain
  PF.ProofExpr (PFI.ProofSym sym arch) PF.ProofDomainType ->
  -- | post-domain
  PF.ProofExpr (PFI.ProofSym sym arch) PF.ProofDomainType ->
  -- | the transition that was attempted to be proven equivalent
  -- in the given domains
  PF.BlockSliceTransition (PFI.ProofSym sym arch) ->
  -- | the model representing the counterexample from the solver
  PT.SymGroundEvalFn sym ->
  EquivM sym arch (PFI.InequivalenceResult arch)
getInequivalenceResult defaultReason pre post slice fn = do
  groundPre <- groundProofExpr fn pre
  groundPost <- groundProofExpr fn post
  gslice <- groundSlice fn slice
  let reason = fromMaybe defaultReason (getInequivalenceReason groundPost (PF.slBlockPostState gslice))
  return $ PFI.InequivalenceResult gslice groundPre groundPost reason

groundProofTransformer ::
  PT.ValidArch arch =>
  PT.ValidSym sym =>
  PT.SymGroundEvalFn sym ->
  PF.ProofTransformer (EquivM_ sym arch) (PFI.ProofSym sym arch) (PFI.ProofGround arch)
groundProofTransformer fn = PF.ProofTransformer
  { PF.prfPredTrans = execGroundFn fn
  , PF.prfMemCellTrans = groundMemCell fn
  , PF.prfBVTrans = \(PFI.SymBV bv) -> groundBV fn bv
  , PF.prfExitTrans = \e ->
      PFI.GroundBlockExit <$> (groundBlockEndCase fn e) <*> (groundReturnPtr fn e)
  , PF.prfValueTrans = groundMacawValue fn
  , PF.prfContextTrans = \_ -> return ()
  , PF.prfConstraint = \a -> a
  }

groundSlice ::
  PT.SymGroundEvalFn sym ->
  PF.BlockSliceTransition (PFI.ProofSym sym arch) ->
  EquivM sym arch (PF.BlockSliceTransition (PFI.ProofGround arch))
groundSlice fn = PF.transformBlockSlice (groundProofTransformer fn)


groundProofExpr ::
  PT.SymGroundEvalFn sym ->
  PF.ProofExpr (PFI.ProofSym sym arch) tp ->
  EquivM sym arch (PF.ProofExpr (PFI.ProofGround arch) tp)
groundProofExpr fn = PF.transformProofExpr (groundProofTransformer fn)


isMemOpValid ::
  PT.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (PFI.GroundMemCell arch) (PF.BlockSliceMemOp (PFI.ProofGround arch)) -> Bool
isMemOpValid dom (MapF.Pair cell mop) =
  (not (PFI.cellInDomain dom cell)) || (not (PF.slMemOpCond mop)) || PF.slMemOpEquiv mop

isRegValid ::
  PT.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (MM.ArchReg arch) (PF.BlockSliceRegOp (PFI.ProofGround arch)) -> Bool
isRegValid dom (MapF.Pair r rop) =
  (not (PFI.regInDomain dom r)) || PF.slRegOpEquiv rop

getInequivalenceReason ::
  PT.ValidArch arch =>
  PFI.GroundDomain arch ->
  PF.BlockSliceState (PFI.ProofGround arch) ->
  Maybe PT.InequivalenceReason
getInequivalenceReason dom st =
  if | not $ all (isMemOpValid dom) (MapF.toList $ PF.slMemState st) -> Just PT.InequivalentMemory
     | not $ all (isRegValid dom) (MapF.toList $ MM.regStateMap $ PF.slRegState st) -> Just PT.InequivalentRegisters
     | otherwise -> Nothing


groundMuxTree ::
  PT.SymGroundEvalFn sym ->
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
  PT.SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch MS.MacawBlockEndCase
groundBlockEndCase fn blkend = withSym $ \sym -> do
  blkend_tree <- liftIO $ MS.blockEndCase (Proxy @arch) sym blkend
  groundMuxTree fn blkend_tree

groundBV ::
  HasCallStack =>
  PT.SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (PFI.GroundBV w)
groundBV fn (CLM.LLVMPointer reg off) = do
  W4.BaseBVRepr w <- return $ W4.exprType off
  greg <- execGroundFn fn reg
  goff <- execGroundFn fn off
  let gbv = PFI.mkGroundBV w greg goff
  return gbv

groundLLVMPointer :: forall sym arch.
  HasCallStack =>
  PT.SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (PFI.GroundLLVMPointer (MM.ArchAddrWidth arch))
groundLLVMPointer fn ptr = PFI.groundBVAsPointer <$> groundBV fn ptr


isStackCell ::
  PMC.MemCell sym arch w ->
  EquivM sym arch (W4.Pred sym)
isStackCell cell = withSym $ \sym -> do
  stackRegion <- CMR.asks envStackRegion
  let CLM.LLVMPointer region _ = PMC.cellPtr cell
  liftIO $ W4.isEq sym region stackRegion

groundMemCell :: forall sym arch w.
  PT.SymGroundEvalFn sym ->
  PMC.MemCell sym arch w ->
  EquivM sym arch (PFI.GroundMemCell arch w)
groundMemCell fn cell = do
  gptr <- groundLLVMPointer fn $ PMC.cellPtr cell
  isStack <- isStackCell cell
  gIsStack <- execGroundFn fn isStack
  return $ PFI.GroundMemCell gptr (PMC.cellWidth cell) gIsStack

groundMacawValue ::
  PT.SymGroundEvalFn sym ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (PFI.GroundMacawValue tp)
groundMacawValue fn e
  | CLM.LLVMPointerRepr _ <- PSR.macawRegRepr e
  , ptr <- PSR.macawRegValue e = do
    PFI.GroundMacawValue <$> groundBV fn ptr
  | CT.BoolRepr <- PSR.macawRegRepr e
  , val <- PSR.macawRegValue e = PFI.GroundMacawValue <$>  execGroundFn fn val
  | CT.StructRepr Ctx.Empty <- PSR.macawRegRepr e = PFI.GroundMacawValue <$> return ()
  | otherwise = throwHere $ PT.UnsupportedRegisterType (Some $ PSR.macawRegRepr e)

groundReturnPtr ::
  forall sym arch.
  HasCallStack =>
  PT.SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch (Maybe (PFI.GroundLLVMPointer (MM.ArchAddrWidth arch)))
groundReturnPtr fn blkend = case MS.blockEndReturn (Proxy @arch) blkend of
  W4P.PE p e -> execGroundFn fn p >>= \case
    True -> Just <$> groundLLVMPointer fn e
    False -> return Nothing
  W4P.Unassigned -> return Nothing
