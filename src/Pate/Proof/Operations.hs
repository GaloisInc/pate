{-|
Module           : Pate.Proof.Operations
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Functions for creating and operating with equivalence proofs
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Proof.Operations
  ( simBundleToSlice
  ) where

import qualified Control.Monad.Reader as CMR
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Set as S

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS

import qualified Lang.Crucible.Simulator as CS

import qualified What4.Interface as W4

import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Event as PE
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Binary as PBi

-- | Convert the result of symbolic execution into a structured slice
-- representation
simBundleToSlice ::
  PS.SimScope sym arch v ->
  PS.SimBundle sym arch v ->
  EquivM sym arch (PF.BlockSliceTransition sym arch)
simBundleToSlice scope bundle = withSym $ \sym -> do
  let 
    (ecaseO, ecaseP) = PPa.view PS.simOutBlockEnd (simOut bundle) 
    (inO, inP) = PS.asStatePair scope (PS.simIn bundle) PS.simInState
    (outO, outP) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState

  footprints <- getFootprints bundle
  memReads <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (S.filter (MT.isDir MT.Read) footprints))
  memWrites <- PEM.toList <$> (liftIO $ PEM.fromFootPrints sym (S.filter (MT.isDir MT.Write) footprints))

  preMem <- MapF.fromList <$> mapM (\x -> memCellToOp inO inP x) memReads
  postMem <- MapF.fromList <$> mapM (\x -> memCellToOp outO outP x) memWrites

  preRegs <- PRt.zipWithRegStatesM (PS.simRegs inO) (PS.simRegs inP) (\r vo vp -> getReg r vo vp)
  postRegs <- PRt.zipWithRegStatesM (PS.simRegs outO) (PS.simRegs outP) (\r vo vp -> getReg r vo vp)
  
  let
    preState = PF.BlockSliceState preMem preRegs
    postState = PF.BlockSliceState postMem postRegs
  return $ PF.BlockSliceTransition preState postState (PPa.PatchPairC ecaseO ecaseP)
  where
    getReg ::
      MM.ArchReg arch tp ->
      PSR.MacawRegEntry sym tp ->
      PSR.MacawRegEntry sym tp ->
      EquivM sym arch (PF.BlockSliceRegOp sym tp)
    getReg reg valO valP = withSym $ \sym -> do
      eqCtx <- equivalenceContext
      isEquiv <- liftIO $ PE.registerValuesEqual sym eqCtx reg valO valP
      return $ PF.BlockSliceRegOp
        (PPa.PatchPairC valO valP)
        (PSR.macawRegRepr valO)
        isEquiv
    
    memCellToOp ::
      PS.SimState sym arch v PBi.Original ->
      PS.SimState sym arch v PBi.Patched ->
      (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      EquivM sym arch (MapF.Pair (PMC.MemCell sym arch) (PF.BlockSliceMemOp sym))
    memCellToOp stO stP (Some cell, cond) = withSym $ \sym -> do
      valO <- liftIO $ PMC.readMemCell sym (PS.simMem stO) cell
      valP <- liftIO $ PMC.readMemCell sym (PS.simMem stP) cell
      isEquiv <- liftIO $ MT.llvmPtrEq sym valO valP
      return $ MapF.Pair cell $ PF.BlockSliceMemOp
        { PF.slMemOpValues = PPa.PatchPairC valO valP
        , PF.slMemOpEquiv = isEquiv
        , PF.slMemOpCond = cond
        }
