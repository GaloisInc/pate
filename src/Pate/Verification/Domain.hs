{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification.Domain (
    equateInitialStates
  , equateRegisters
  , universalDomain
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import           Data.Functor.Const ( Const(..) )
import           Data.Parameterized.Classes()
import qualified What4.Interface as W4

import qualified Data.Macaw.CFG as MM

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Register as PRe
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimState as PSi
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PS

equateRegisters ::
  PER.RegisterDomain sym arch ->
  SimBundle sym arch v ->
  EquivM sym arch (PSi.AssumptionSet sym v)
equateRegisters regRel bundle = withValid $ withSym $ \sym -> do
  PA.SomeValidArch (PA.validArchDedicatedRegisters -> hdr) <- CMR.asks envValidArch
  fmap PRt.collapse $ PRt.zipWithRegStatesM (PSi.simRegs inStO) (PSi.simRegs inStP) $ \r vO vP -> case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return mempty
    _ -> do
      let cond = PER.registerInDomain sym r regRel
      case W4.asConstantPred cond of
        Just True -> fmap Const $ liftIO $ PSi.macawRegBinding sym vO vP
        _ -> return $ Const mempty
  where
    inStO = PSi.simInState $ PSi.simInO bundle
    inStP = PSi.simInState $ PSi.simInP bundle

equateInitialMemory :: SimBundle sym arch v -> EquivM sym arch (PSi.AssumptionSet sym v)
equateInitialMemory bundle =
  return $ PSi.bindingToFrame $ MT.mkMemoryBinding memStO memStP
  where
    memStO = MT.memState $ PSi.simInMem $ PSi.simInO bundle
    memStP = MT.memState $ PSi.simInMem $ PSi.simInP bundle

equateInitialStates :: SimBundle sym arch v -> EquivM sym arch (PSi.AssumptionSet sym v)
equateInitialStates bundle = withSym $ \sym -> do
  eqRegs <- equateRegisters (PER.universal sym) bundle
  eqMem <- equateInitialMemory bundle
  return $ eqRegs <> eqMem

-- | Domain that includes entire state, except IP and SP registers
universalDomain ::
  forall sym arch.
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  PED.EquivalenceDomain sym arch
universalDomain sym =
  let
    regDomain =
        (PER.update sym (\_ -> W4.falsePred sym)) (MM.ip_reg @(MM.ArchReg arch))
      $ (PER.universal sym)
  in PED.EquivalenceDomain
    {
      PED.eqDomainRegisters = regDomain
    , PED.eqDomainStackMemory = PEM.universal sym
    , PED.eqDomainGlobalMemory = PEM.universal sym
    }

{- Note [Names for Inputs]

Our goal here is to assign meaningful names to function inputs so that they
appear in generated differential summaries.

This code looks up the entry point address of the current slice in the
VerificationHints (extracted from metadata) and attempts to use those names when
allocating the symbolic values for registers.

The location of that original entry point is a bit involved. We use the
'SimBundle', which has a 'SimInput' (at least a pair of them)

> 'simInBlock' :: 'SimInput' sym arch bin -> 'ConcreteBlock' arch bin

Using that address, we can look up the argument names in the metadata. Note
that there is a single set of inputs allocated for both blocks, so plan
accordingly (we only need the input block names)

Note that this currently only handles supplying names to arguments in integer
registers, and will misbehave if there are arguments actually passed on the
stack or in floating point registers. Longer term, this code should use the
abide library to map arguments to registers.

-}
