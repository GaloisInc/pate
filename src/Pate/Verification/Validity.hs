{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pate.Verification.Validity (
    validInitState
  , validRegister
  , collectPointerAssertions
  ) where

import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Writer as CMW
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.Trans.Writer (WriterT, runWriterT)

import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Functor.Const
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import           Pate.AssumptionSet
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Discovery as PD
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import qualified Pate.Register.Traversal as PRt
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Memory.MemTrace as MT

import qualified What4.ExprHelpers as WEH

validInitState ::
  Maybe (PB.BlockPair arch) ->
  SimState sym arch v PB.Original ->
  SimState sym arch v PB.Patched ->
  EquivM sym arch (AssumptionSet sym)
validInitState mpPair stO stP = do
  fmap PRt.collapse $ PRt.zipWithRegStatesM (simRegs stO) (simRegs stP) $ \r vO vP -> do
    validO <- validRegister (fmap PPa.pOriginal mpPair) vO r
    validP <- validRegister (fmap PPa.pPatched mpPair) vP r
    return $ Const $ validO <> validP

validRegister ::
  forall bin sym arch tp.
  PB.KnownBinary bin =>
  -- | if this register is an initial state, the corresponding
  -- starting block
  Maybe (PB.ConcreteBlock arch bin) ->
  PSR.MacawRegEntry sym tp ->
  MM.ArchReg arch tp ->
  EquivM sym arch (AssumptionSet sym)
validRegister mblockStart entry r = withSym $ \sym -> do
  PA.SomeValidArch (PA.validArchDedicatedRegisters -> hdr) <- CMR.asks envValidArch
  case PRe.registerCase hdr (PSR.macawRegRepr entry) r of
    PRe.RegIP -> case mblockStart of
      Just blockStart -> do
        ptrO <- PD.concreteToLLVM blockStart
        return $ macawRegBinding sym entry (PSR.ptrToEntry ptrO)
      Nothing -> return $ mempty
    PRe.RegSP -> do
      stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      return $ natBinding region stackRegion
    PRe.RegBV -> liftIO $ do
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      zero <- W4.intLit sym 0
      nzero <- W4.integerToNat sym zero
      return $ natBinding region nzero
    PRe.RegGPtr -> liftIO $ do
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      p <- liftIO $ WEH.assertPositiveNat sym region
      return $ fromPred p
    PRe.RegDedicated dr -> do
      ctx <- CMR.asks envCtx
      let binRepr = W4.knownRepr :: PB.WhichBinaryRepr bin
      liftIO $ PA.dedicatedRegisterValidity hdr sym ctx binRepr entry dr
    _ -> return $ mempty


collectPointerAssertions ::
  forall sym arch tp.
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp, AssumptionSet sym)
collectPointerAssertions outer = withSym $ \sym -> do
  ptrAsserts <- CMR.asks envPtrAssertions
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> WriterT (AssumptionSet sym) (EquivM_ sym arch) (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      WEH.setProgramLoc sym e
      e' <- (liftIO $ (MT.getPtrAssertion sym ptrAsserts e)) >>= \case
        Just (p, e') -> CMW.tell (fromPred p) >> return e'
        Nothing -> return e
      case e' of
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e'
          else (liftIO $ W4B.sbMakeExpr sym a0')
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e'
          else (liftIO $ W4B.sbNonceExpr sym a0')
        _ -> return e'
  runWriterT $ go outer
