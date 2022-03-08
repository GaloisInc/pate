{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
-- | Support for calls to external functions (i.e., functions for which implementations are not provideD)
--
-- These arise for both calls to shared libraries and system calls.  Shared
-- libraries can be handled by including the shared libraries and incorporating
-- their code, but system calls will always require models.
--
-- These types are structured as values rather than classes because they may
-- vary based on OS or ABI choice (and not just architecture).
module Pate.Verification.ExternalCall (
    ExternalDomain(..)
  , CallK
  , SystemCall
  , ExternalCall
  ) where

import           Control.Monad.IO.Class ( MonadIO )
import           Data.Kind ( Type )
import qualified What4.Interface as WI

import qualified Pate.Equivalence.EquivalenceDomain as PED

data CallK = SystemCall | ExternalCall

type SystemCall = 'SystemCall
type ExternalCall = 'ExternalCall

-- | Return the pre-domain required for an external call (i.e., the domain of
-- locations that must be equivalent in the original and patched program at the
-- entry point to an external function)
--
-- It has a type-level tag to indicate whether it is for system calls or other
-- external calls, as system calls typically have different calling conventions.
--
-- TODO This needs to take enough inputs to be able to examine the program state
-- (e.g., to determine what the PC of the callee is, which would allow us to
-- apply precise summaries)
data ExternalDomain :: CallK -> Type -> Type where
  ExternalDomain :: (forall sym m . (MonadIO m, WI.IsExprBuilder sym)
                                 => (sym -> m (PED.EquivalenceDomain sym arch))) -> ExternalDomain callk arch
