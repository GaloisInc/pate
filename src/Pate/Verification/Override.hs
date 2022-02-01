{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pate.Verification.Override (
    Override(..)
  , SomeOverride(..)
  , ArgumentMapping(..)
  , buildArgumentRegisterAssignment
  ) where

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           GHC.Stack ( HasCallStack )
import qualified What4.FunctionName as WF

import qualified Data.Macaw.Symbolic as DMS

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Protocol.Online as WPO

import qualified Pate.Panic as PP

-- | An 'Override' captures the information necessary to call a crucible
-- override with "natural" arguments (i.e., a C-like argument list, rather than
-- machine code register argument lists).
data Override sym args ext ret =
  Override { functionName :: WF.FunctionName
           , functionArgsRepr :: Ctx.Assignment LCT.TypeRepr args
           , functionRetRepr :: LCT.TypeRepr ret
           , functionOverride :: forall solver scope st fs rtp args' ret' p
                               . (LCB.IsSymInterface sym, WPO.OnlineSolver solver, sym ~ WE.ExprBuilder scope st fs)
                              => LCBO.OnlineBackend solver scope st fs
                              -> Ctx.Assignment (LCS.RegEntry sym) args
                              -> LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret)
           }

-- | An existential wrapper around an 'Override' that quantifies out the
-- argument and return types
data SomeOverride arch sym where
  SomeOverride :: Override sym args (DMS.MacawExt arch) ret -> SomeOverride arch sym

data ArgumentMapping arch =
  ArgumentMapping {
      -- | A function to map machine registers (the 'Ctx.Assignment' of
      -- 'LCS.RegValue'') to a structured argument list in the style of a C
      -- function, intended to be passed to an 'Override'
      functionIntegerArgumentRegisters
        :: forall atps sym
         . Ctx.Assignment LCT.TypeRepr atps
        -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
        -> Ctx.Assignment (LCS.RegEntry sym) atps
      -- | Given an 'LCS.OverrideSim' action that returns a normal Crucible
      -- value (e.g., the 'functionOverride' in an 'Override'), construct an
      -- 'LCS.OverrideSim' action that returns a machine register state.
    , functionReturnRegister
        :: forall t r args rtp p sym
         . LCT.TypeRepr t
        -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym t)
        -> LCS.RegValue sym (DMS.ArchRegStruct arch)
        -- Argument registers from *before* the override executed, representing
        -- the register state that is updated by the called function
        -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
    }

-- | Build an Assignment representing the arguments to a function from a list of
-- registers
buildArgumentRegisterAssignment
  :: forall w args sym
    . (HasCallStack)
  => PN.NatRepr w
  -- ^ Pointer width
  -> LCT.CtxRepr args
  -- ^ Types of arguments
  -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
  -- ^ List of argument registers
  -> Ctx.Assignment (LCS.RegEntry sym) args
  -- ^ Argument values
buildArgumentRegisterAssignment ptrW argTyps regEntries = go argTyps regEntries'
  where
    -- Drop unused registers from regEntries and reverse list to account for
    -- right-to-left processing when using 'Ctx.viewAssign'
    regEntries' = reverse (take (Ctx.sizeInt (Ctx.size argTyps)) regEntries)

    go :: forall args'
        . LCT.CtxRepr args'
       -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
       -> Ctx.Assignment (LCS.RegEntry sym) args'
    go typs regs =
      case Ctx.viewAssign typs of
        Ctx.AssignEmpty -> Ctx.empty
        Ctx.AssignExtend typs' (LCLM.LLVMPointerRepr w) | Just PC.Refl <- PC.testEquality w ptrW ->
          case regs of
            [] -> PP.panic PP.Override
                           "buildArgumentRegisterAssignment"
                           ["Override expects too many arguments"]
            reg : regs' ->
              (go typs' regs') Ctx.:> reg
        _ -> PP.panic PP.Override
                      "buildArgumentRegisterAssignment"
                      ["Currently only LLVMPointer arguments are supported"]
