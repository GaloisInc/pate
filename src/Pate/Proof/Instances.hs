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
{-# LANGUAGE ViewPatterns   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Proof.Instances
  (
  ppExitCase
  )
  
  where

import qualified Data.Macaw.CFGSlice as MCS

import qualified Prettyprinter as PP

import qualified Pate.Arch as PA
import qualified Pate.Proof as PF
import qualified Pate.Solver as PSo

instance forall sym arch.
  (PA.ValidArch arch, PSo.ValidSym sym) =>
  PP.Pretty (PF.VerificationStatus sym arch) where
  pretty st = error "replace this function"

instance PA.ValidArch arch => PP.Pretty (PF.InequivalenceResult arch) where
  pretty gineq = error "replace this function"


ppExitCase :: MCS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MCS.MacawBlockEndJump -> "arbitrary jump"
  MCS.MacawBlockEndCall -> "function call"
  MCS.MacawBlockEndReturn -> "function return"
  MCS.MacawBlockEndBranch -> "branch"
  MCS.MacawBlockEndArch -> "arch-specific"
  MCS.MacawBlockEndFail -> "analysis failure"