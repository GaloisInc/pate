{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.Concretize (
    Concretize
  , concreteBV
  , concreteInteger
  , resolveSingletonSymbolicAs
  , resolveSingletonPointer
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.BaseTypes as WT
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

import qualified Pate.Panic as PP

data Concretize sym tp where
  Concretize :: (Show (WEG.GroundValue tp))
             => WT.BaseTypeRepr tp
             -> (WI.SymExpr sym tp -> Maybe (WEG.GroundValue tp)) -- Convert a symbolic term to a concrete value
             -> (sym -> WI.SymExpr sym tp -> WEG.GroundValue tp -> IO (WI.SymExpr sym WT.BaseBoolType)) -- Create a blocking clause from a concrete value
             -> (sym -> WEG.GroundValue tp -> IO (WI.SymExpr sym tp)) -- Create a symbolic term wrapping the concrete result
             -> Concretize sym tp

concreteBV :: (LCB.IsSymInterface sym, 1 <= w) => PN.NatRepr w -> Concretize sym (WI.BaseBVType w)
concreteBV w = Concretize (WT.BaseBVRepr w) WI.asBV toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.bvEq sym symVal =<< WI.bvLit sym w gv
    injectSymbolic sym gv = WI.bvLit sym w gv

concreteInteger :: (LCB.IsSymInterface sym) => Concretize sym WI.BaseIntegerType
concreteInteger = Concretize WT.BaseIntegerRepr WI.asInteger toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.intEq sym symVal =<< WI.intLit sym gv
    injectSymbolic = WI.intLit

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it. Otherwise, return the original symbolic value
resolveSingletonSymbolicAs
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> sym
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (WI.SymExpr sym tp)
resolveSingletonSymbolicAs (Concretize _tp asConcrete toBlocking injectSymbolic) sym val =
  case asConcrete val of
    Just _ -> return val
    Nothing -> do
      LCBO.withSolverProcess sym onlinePanic $ \sp -> do
        val' <- WPO.inNewFrame sp $ do
          msat <- WPO.checkAndGetModel sp "Concretize value (with no assumptions)"
          mmodel <- case msat of
            WSat.Unknown -> return Nothing
            WSat.Unsat {} -> return Nothing
            WSat.Sat mdl -> return (Just mdl)
          T.forM mmodel $ \mdl -> WEG.groundEval mdl val
        case val' of
          Nothing -> return val -- We failed to get a model... leave it symbolic
          Just concVal -> do
            WPO.inNewFrame sp $ do
              block <- toBlocking sym val concVal
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> return val -- Total failure
                WSat.Sat _mdl -> do
                  return val  -- There are multiple models
                WSat.Unsat {} -> injectSymbolic sym concVal -- There is a single concrete result
  where
    onlinePanic = PP.panic PP.InlineCallee "resolveSingletonSymbolicValue" ["Online solver support is not enabled"]

resolveSingletonPointer
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => sym
  -- ^ The symbolic backend
  -> LCLM.LLVMPtr sym w
  -- ^ The symbolic term to concretize
  -> IO (LCLM.LLVMPtr sym w)
resolveSingletonPointer sym ptr@(LCLM.LLVMPointer base off) = do
  base' <- WI.integerToNat sym =<< resolveSingletonSymbolicAs concreteInteger sym =<< WI.natToInteger sym base
  off' <- resolveSingletonSymbolicAs (concreteBV (LCLM.ptrWidth ptr)) sym off
  return (LCLM.LLVMPointer base' off')
