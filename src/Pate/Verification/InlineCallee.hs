{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Pate.Verification.InlineCallee ( inlineCallee ) where

import           GHC.Stack ( HasCallStack )

import qualified Pate.Abort as PAb
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory as PM
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import           Pate.Proof.Ground as PFG
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Proof.Operations as PFO
import           Pate.SimState
import qualified Pate.Solver as PS
import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Simplify as PVSi
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.Validity as PVV

-- | Symbolically execute the given callees and synthesize a new 'PES.StatePred'
-- for the two equated callees (as directed by the user) that only reports
-- memory effects that are not explicitly ignored.
--
-- Unlike the normal loop of 'provePostcondition', this path effectively inlines
-- callees (rather than breaking them into slices compositionally) to produce
-- monolithic summaries. The main goal of this is to enable us to more
-- accurately capture all of the memory effects of the two functions.  This
-- function uses the standard implementation of symbolic execution of machine
-- code provided by macaw-symbolic, rather than the slice-based decomposition.
--
-- The premise is that the two callees (in the original and patched binaries)
-- are actually quite different, but the user would like to reason about their
-- unintended effects.
inlineCallee
  :: (HasCallStack)
  => StatePredSpec sym arch
  -> PPa.BlockPair arch
  -> EquivM sym arch (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
inlineCallee = undefined
