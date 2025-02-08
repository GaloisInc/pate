{-|
Module           : Pate.Proof.CounterExample
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

module Pate.Proof.CounterExample 
  ( getInequivalenceResult
  ) where

import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import           Data.Maybe (fromMaybe)


import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Ground as PG
import           What4.ExprHelpers as WEH

-- | Generate a structured counterexample for an equivalence
-- check from an SMT model.
-- Takes a symbolic 'PF.BlockSliceTransition' and grounds it according
-- to the model. Additionally, the given pre-domain and post-domains are
-- similarly grounded, so the counter-example contains which concrete locations
-- were assumed equivalent, and any concrete locations that are not equivalent
-- after the block slice transition.
getInequivalenceResult ::
  forall sym arch.
  PEE.InequivalenceReason ->
  -- | pre-domain
  PED.EquivalenceDomain sym arch ->
  -- | post-domain
  PED.EquivalenceDomain sym arch ->
  -- | the transition that was attempted to be proven equivalent
  -- in the given domains
  PF.BlockSliceTransition sym arch ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (PF.InequivalenceResult arch)
getInequivalenceResult defaultReason pre post slice fn = error "remove this function"
