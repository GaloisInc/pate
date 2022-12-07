{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines the semantics of exceptional program termination

module Pate.Abort
  ( isAbortedStatePred
  , proveAbortValid
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR

import qualified Data.Macaw.CFG as MC

import qualified What4.Interface as WI

import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.PatchPair as PPa
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.SimState as PSS

-- | Compute a predicate that is true exactly when the output state has resolved to an abort condition
-- NOTE: For the moment, this is defined exactly as a call to a special sentinel function that
-- defines abnormal program exit. In general this can be expanded to other error states (i.e. null-pointer
-- dereference), there necessarily exist abort conditions that this does not cover.
isAbortedStatePred ::
  forall sym arch v bin.
  PB.KnownBinary bin =>
  PSS.SimOutput sym arch v bin ->
  EquivM sym arch (WI.Pred sym)
isAbortedStatePred stOut = (PMC.binAbortFn <$> getBinCtx @bin) >>= \case
  Just abortFn -> withSym $ \sym -> do
    let abortBlk = PB.functionEntryToConcreteBlock abortFn
    abortPtr <- PD.concreteToLLVM abortBlk
    liftIO $ MT.llvmPtrEq sym abortPtr (PSR.macawRegValue ip)
  Nothing -> withSym $ \sym -> return $ WI.falsePred sym
  where
    regs = PSS.simOutRegs stOut
    ip = regs ^. MC.curIP

-- | Prove that the original binary aborts only in cases where the equivalence condition
-- is invalidated
proveAbortValid ::
  forall sym arch v.
  SimBundle sym arch v ->
  -- | conditional equivalence predicate
  WI.Pred sym ->
  EquivM sym arch Bool
proveAbortValid bundle condEq = withSym $ \sym -> do
  outO <- case PSS.simOut bundle of
    PPa.PatchPair outO _ -> return outO
    PPa.PatchPairOriginal outO -> return outO
    _ -> PPa.handleSingletonStub
  oAbort <- isAbortedStatePred outO
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  traceBundle bundle "Checking conditional equivalence validity"
  -- assuming conditional equivalence does not hold (i.e. the programs may diverge)
  -- prove that the original binary necessarily results in an abort branch
  notCondEq <- liftIO $ WI.notPred sym condEq
  withAssumption notCondEq $
    isPredTrue' heuristicTimeout oAbort
