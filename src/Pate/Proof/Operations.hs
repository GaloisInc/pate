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
simBundleToSlice scope bundle = error "remove this function"