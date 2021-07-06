{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Pate.Equivalence.StatePred (
    StatePred(..)
  , muxStatePred
  , statePredFalse
  ) where

import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.Some ( Some(..) )
import qualified What4.Interface as WI


import qualified Data.Macaw.CFG as MM

import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.ExprMappable as PEM

---------------------------------------------
-- State predicate

-- | This is a predicate over machine state that says whether or not a given
-- piece of machine state should be included in an operation.  Notionally, this
-- could be thought of as a function:
--
-- > statePred :: MachineLocation -> 'WI.Pred'
--
-- Note that the predicate is 'WI.Pred' rather than 'Bool', potentially allowing
-- for additional expressivity.
data StatePred sym arch =
  StatePred
    { predRegs :: M.Map (Some (MM.ArchReg arch)) (WI.Pred sym)
    -- ^ Predicates covering machine registers; if a machine register is missing from the map, the
    -- predicate is considered to be false
    , predStack :: PEM.MemPred sym arch
    -- ^ The predicate over stack memory locations
    , predMem :: PEM.MemPred sym arch
    -- ^ The predicate over other memory locations
    }

muxStatePred ::
  WI.IsExprBuilder sym =>
  PC.OrdF (WI.SymExpr sym) =>
  PC.OrdF (MM.ArchReg arch) =>
  sym ->
  WI.Pred sym ->
  StatePred sym arch ->
  StatePred sym arch ->
  IO (StatePred sym arch)
muxStatePred sym p predT predF = case WI.asConstantPred p of
  Just True -> return predT
  Just False -> return predF
  _ -> do
    notp <- WI.notPred sym p
    regs <- M.mergeA
      (M.traverseMissing (\_ pT -> WI.andPred sym pT p))
      (M.traverseMissing (\_ pF -> WI.andPred sym pF notp))
      (M.zipWithAMatched (\_ p1 p2 -> WI.baseTypeIte sym p p1 p2))
      (predRegs predT)
      (predRegs predF)
    stack <- PEM.muxMemPred sym p (predStack predT) (predStack predF)
    mem <- PEM.muxMemPred sym p (predMem predT) (predMem predF)
    return $ StatePred regs stack mem

statePredFalse :: WI.IsExprBuilder sym => sym -> StatePred sym arch
statePredFalse sym = StatePred M.empty (PEM.memPredFalse sym) (PEM.memPredFalse sym)

instance PEM.ExprMappable sym (StatePred sym arch) where
  mapExpr sym f stPred = do
    regs <- mapM f (predRegs stPred)
    stack <- PEM.mapExpr sym f (predStack stPred)
    mem <- PEM.mapExpr sym f (predMem stPred)
    return $ StatePred regs stack mem
