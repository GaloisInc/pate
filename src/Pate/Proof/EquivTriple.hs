{-# LANGUAGE GADTs #-}
module Pate.Proof.EquivTriple (
  EquivTriple(..)
  ) where

import qualified Pate.Equivalence as PE
import qualified Pate.PatchPair as PPa

-- | An triple representing the equivalence conditions for a block pair.
-- This is analogous to a 'ProofExpr' of type
-- 'ProofTriple', but contains the 'PE.StatePredSpec' type that the verifier uses.
-- This redundancy can potentially be eliminated at some point.
data EquivTriple sym arch where
  EquivTriple ::
    {
      eqPair :: PPa.BlockPair arch
      -- ^ the entry points that yield equivalent states on the post-domain
      -- after execution, assuming initially equivalent states on the pre-domain
    , eqPreDomain :: PE.DomainSpec sym arch
      -- ^ the pre-domain: the state that was assumed initially equivalent
      -- abstracted over the bound variables representing the initial state
    , eqPostDomain :: PE.DomainSpec sym arch
      -- ^ the post-domain: the state that was proven equivalent after execution
      -- abstracted over the bound variables representing the final state
    } -> EquivTriple sym arch
