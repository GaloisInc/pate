{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Register (
    RegisterCase(..)
  , registerCase
  , zipRegStates
  , zipRegStatesPar
  , zipWithRegStatesM
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( join )
import           Data.Functor.Const ( Const(..) )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import qualified Pate.Parallel as PP

-- | Helper for doing a case-analysis on registers
data RegisterCase arch tp where
  -- | instruction pointer
  RegIP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | stack pointer
  RegSP :: RegisterCase arch (CLM.LLVMPointerType (MM.ArchAddrWidth arch))
  -- | non-specific bitvector (zero-region pointer) register
  RegBV :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific pointer register
  RegGPtr :: RegisterCase arch (CLM.LLVMPointerType w)
  -- | non-specific non-pointer register
  RegElse :: RegisterCase arch tp
  -- | A dedicated register whose value is determined by the ABI (see
  -- 'PA.DedicatedRegister' for details)
  RegDedicated :: PA.DedicatedRegister arch tp -> RegisterCase arch tp

registerCase ::
  forall arch tp.
  PA.ValidArch arch =>
  PA.HasDedicatedRegister arch ->
  CC.TypeRepr (MS.ToCrucibleType tp) ->
  MM.ArchReg arch tp ->
  RegisterCase arch (MS.ToCrucibleType tp)
registerCase hdr repr r =
  if | Just PC.Refl <- PC.testEquality r (MM.ip_reg @(MM.ArchReg arch)) -> RegIP
     | Just PC.Refl <- PC.testEquality r (MM.sp_reg @(MM.ArchReg arch)) -> RegSP
     | Just dr <- PA.asDedicatedRegister hdr r -> RegDedicated dr
     | CLM.LLVMPointerRepr {} <- repr ->
       case PA.rawBVReg r of
         True -> RegBV
         False -> RegGPtr
     | otherwise -> RegElse

zipRegStatesPar :: PP.IsFuture m future
                => MM.RegisterInfo r
                => MM.RegState r f
                -> MM.RegState r g
                -> (forall u. r u -> f u -> g u -> m (future h))
                -> m (future [h])
zipRegStatesPar regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> Const <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  PP.promise $ mapM (\(MapF.Pair _ (Const v)) -> PP.joinFuture v) $ MapF.toList $ MM.regStateMap regs'

zipRegStates :: Monad m
             => MM.RegisterInfo r
             => MM.RegState r f
             -> MM.RegState r g
             -> (forall u. r u -> f u -> g u -> m h)
             -> m [h]
zipRegStates regs1 regs2 f = join $ zipRegStatesPar regs1 regs2 (\r e1 e2 -> return $ f r e1 e2)

zipWithRegStatesM :: Monad m
                  => MM.RegisterInfo r
                  => MM.RegState r f
                  -> MM.RegState r g
                  -> (forall u. r u -> f u -> g u -> m (h u))
                  -> m (MM.RegState r h)
zipWithRegStatesM regs1 regs2 f = MM.mkRegStateM (\r -> f r (regs1 ^. MM.boundValue r) (regs2 ^. MM.boundValue r))
