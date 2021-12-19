{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.Concretize (
  resolveSingletonSymbolicValue
  , resolveSingletonSymbolicValueInt
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

import qualified Pate.Panic as PP

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it. Otherwise, return the original symbolic value
resolveSingletonSymbolicValue
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => sym
  -> PN.NatRepr w
  -> WI.SymExpr sym (WT.BaseBVType w)
  -> IO (WI.SymExpr sym (WT.BaseBVType w))
resolveSingletonSymbolicValue sym w val = do
  case WI.asBV val of
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
        putStrLn ("Initial model is: " ++ show val')
        case val' of
          Nothing -> return val -- We failed to get a model... leave it symbolic
          Just concVal -> do
            WPO.inNewFrame sp $ do
              block <- WI.notPred sym =<< WI.bvEq sym val =<< WI.bvLit sym w concVal
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> return val -- Total failure
                WSat.Sat mdl -> do
                  other <- WEG.groundEval mdl val
                  putStrLn ("  Second model is: " ++ show other)
                  return val  -- There are multiple models
                WSat.Unsat {} -> WI.bvLit sym w concVal -- There is a single concrete result
  where
    onlinePanic = PP.panic PP.InlineCallee "resolveSingletonSymbolicValue" ["Online solver support is not enabled"]

resolveSingletonSymbolicValueInt
  :: ( LCB.IsSymInterface sym
     , sym ~ LCBO.OnlineBackend scope solver fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => sym
  -> WI.SymExpr sym WT.BaseIntegerType
  -> IO (WI.SymExpr sym WT.BaseIntegerType)
resolveSingletonSymbolicValueInt sym val = do
 case WI.asInteger val of
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
        putStrLn ("Initial model is: " ++ show val')
        case val' of
          Nothing -> return val -- We failed to get a model... leave it symbolic
          Just concVal -> do
            WPO.inNewFrame sp $ do
              block <- WI.notPred sym =<< WI.intEq sym val =<< WI.intLit sym concVal
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.check sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> return val -- Total failure
                WSat.Sat {} -> return val  -- There are multiple models
                WSat.Unsat {} -> WI.intLit sym concVal -- There is a single concrete result
  where
    onlinePanic = PP.panic PP.InlineCallee "resolveSingletonSymbolicValue" ["Online solver support is not enabled"]
