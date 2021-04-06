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

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Proof.Ground 
  ( getInequivalenceResult
  , getUnequalPathCondition
  , groundMacawValue
  , groundProofTransformer
  , groundProofExpr
  ) where

import           GHC.Stack ( HasCallStack )

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR

import           Data.Maybe (fromMaybe)
import           Data.Proxy ( Proxy(..) )
import           Numeric.Natural ( Natural )
import           Data.Functor.Const

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF


import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.MuxTree as C

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Partial as W4P
import qualified What4.Expr.Builder as W4B

import qualified Pate.MemCell as PMC
import           Pate.Monad
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.SimState as PS
import qualified Pate.Arch as PA
import qualified Pate.ExprMappable as PEM
import           What4.ExprHelpers

-- | Generate a structured counterexample for an equivalence
-- check from an SMT model.
-- Takes a symbolic 'PF.BlockSliceTransition' and grounds it according
-- to the model. Additionally, the given pre-domain and post-domains are
-- similarly grounded, so the counter-example contains which concrete locations
-- were assumed equivalent, and any concrete locations that are not equivalent
-- after the block slice transition.
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


getGenPathCondition ::
  forall sym f.
  W4.IsExprBuilder sym =>
  PEM.ExprMappable sym f =>
  sym ->
  PT.SymGroundEvalFn sym ->
  f ->
  IO (W4.Pred sym)
getGenPathCondition sym (PT.SymGroundEvalFn fn) e = do
  cache <- W4B.newIdxCache
  
  
  let
    f :: forall tp'. W4.SymExpr sym tp' -> W4.Pred sym -> IO (W4.Pred sym)
    f e' cond = do
      stripped <- stripAsserts sym cache e'
      cond' <- getPathCondition sym fn stripped
      W4.andPred sym cond cond'
  
  PEM.foldExpr sym f e (W4.truePred sym)

-- | Compute a domain that represents the path condition for
-- values which disagree in the given counter-example
getUnequalPathCondition ::
  forall sym arch.
  PS.SimBundle sym arch ->
  PF.BlockSliceState (PFI.ProofSym sym arch) ->
  PFI.SymDomain sym arch ->
  PT.SymGroundEvalFn sym ->
  EquivM sym arch (PT.PatchPairC (W4.Pred sym))
getUnequalPathCondition bundle slice dom fn = withSym $ \sym -> do
  groundDom <- groundProofExpr fn dom
  let
    getRegPath reg regOp paths = do
      case PFI.regInDomain groundDom reg of
        True -> do
          paths' <- liftIO $ mapM (getGenPathCondition sym fn) (PF.slRegOpValues regOp)
          liftIO $ PT.zipMPatchPairC paths paths' (W4.andPred sym)
        _ -> return paths    

    getMemPath :: forall bin. PS.SimOutput sym arch bin -> EquivM sym arch (Const (W4.Pred sym) bin)
    getMemPath st = do
      let mem = MT.memArr $ PS.simOutMem st
      Const <$> (liftIO $ getGenPathCondition sym fn mem)

  let truePair = PT.PatchPairC (W4.truePred sym) (W4.truePred sym)
  regPath <- PF.foldrMBlockStateLocs getRegPath (\_ _ -> return) truePair slice
  
  memPath <- PT.toPatchPairC <$> TF.traverseF getMemPath (PS.simOut bundle)
  liftIO $ PT.zipMPatchPairC regPath memPath (W4.andPred sym)


groundProofTransformer ::
  PA.ValidArch arch =>
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
  PA.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (PFI.GroundMemCell arch) (PF.BlockSliceMemOp (PFI.ProofGround arch)) -> Bool
isMemOpValid dom (MapF.Pair cell mop) =
  (not (PFI.cellInDomain dom cell)) || (not (PF.slMemOpCond mop)) || PF.slMemOpEquiv mop

isRegValid ::
  PA.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (MM.ArchReg arch) (PF.BlockSliceRegOp (PFI.ProofGround arch)) -> Bool
isRegValid dom (MapF.Pair r rop) =
  (not (PFI.regInDomain dom r)) || PF.slRegOpEquiv rop

getInequivalenceReason ::
  PA.ValidArch arch =>
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
groundBV fn (CLM.LLVMPointer reg off) = withSym $ \sym -> do
  W4.BaseBVRepr w <- return $ W4.exprType off
  iReg <- liftIO $ W4.natToInteger sym reg
  greg <- execGroundFn fn iReg
  goff <- execGroundFn fn off
  let integerToNat :: Integer -> Natural
      integerToNat i
        | i >= 0 = fromIntegral i
        | otherwise = fromIntegral (negate i)
  let gbv = PFI.mkGroundBV w (integerToNat greg) goff
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
  liftIO $ W4.natEq sym region stackRegion

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
