{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Pate.Verification.Override (
    Override(..)
  , SomeOverride(..)
  , ArgumentMapping(..)
  ) where

import qualified Data.Parameterized.Context as Ctx
import qualified What4.FunctionName as WF

import qualified Data.Macaw.Symbolic as DMS

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT

-- | An 'Override' captures the information necessary to call a crucible
-- override with "natural" arguments (i.e., a C-like argument list, rather than
-- machine code register argument lists).
data Override sym args ext ret =
  Override { functionName :: WF.FunctionName
           , functionArgsRepr :: Ctx.Assignment LCT.TypeRepr args
           , functionRetRepr :: LCT.TypeRepr ret
           , functionOverride :: forall rtp args' ret' p
                               . (LCB.IsSymInterface sym)
                              => sym
                              -> Ctx.Assignment (LCS.RegEntry sym) args
                              -> LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret)
           }

-- | An existential wrapper around an 'Override' that quantifies out the
-- argument and return types
data SomeOverride arch sym where
  SomeOverride :: Override sym args (DMS.MacawExt arch) ret -> SomeOverride arch sym

data ArgumentMapping arch sym =
  ArgumentMapping {
      -- | A function to map machine registers (the 'Ctx.Assignment' of
      -- 'LCS.RegValue'') to a structured argument list in the style of a C
      -- function, intended to be passed to an 'Override'
      functionIntegerArgumentRegisters
        :: forall atps
         . Ctx.Assignment LCT.TypeRepr atps
        -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
        -> Ctx.Assignment (LCS.RegEntry sym) atps
      -- | Given an 'LCS.OverrideSim' action that returns a normal Crucible
      -- value (e.g., the 'functionOverride' in an 'Override'), construct an
      -- 'LCS.OverrideSim' action that returns a machine register state.
    , functionReturnRegister
        :: forall t r args rtp p
         . LCT.TypeRepr t
        -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym t)
        -> LCS.RegValue sym (DMS.ArchRegStruct arch)
        -- Argument registers from *before* the override executed, representing
        -- the register state that is updated by the called function
        -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
    }
