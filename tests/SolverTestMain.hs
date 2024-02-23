{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
module Main ( main ) where

import           Control.Monad ( forM )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.IORef as IO
import           Data.Proxy
import qualified Data.Set as Set
import qualified Test.Tasty as TT
import qualified Test.Tasty.ExpectedFailure as TT
import qualified Test.Tasty.HUnit as TTH

import           Data.Parameterized.Some
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.SetF as SetF
import qualified What4.Expr as WE

import           Pate.AArch32 (AArch32)
import qualified Pate.Monad as PM
import qualified Pate.Config as PC
import qualified Pate.Solver as PS
import qualified Pate.AssumptionSet as PAs
import qualified What4.Interface as W4
import qualified What4.Solver as W4
import qualified Pate.Timeout as PT
import qualified Pate.Arch as PA
import           Pate.TraceTree
import qualified Data.Map as Map

withEqEnv :: forall arch a. PA.ValidArch arch => Proxy arch -> (forall sym. PM.EquivEnv sym arch -> IO a) -> IO a
withEqEnv _px f = do
  -- ha <- CFH.newHandleAllocator
  Some gen <- N.newIONonceGenerator
  sym <- WE.newExprBuilder WE.FloatRealRepr WE.EmptyExprBuilderState gen
  let (validArchData :: PA.ValidArchData arch) = error "validArchData"
  let validArch = PA.SomeValidArch validArchData

  WE.startCaching sym
  satCache <- IO.newIORef SetF.empty
  unsatCache <- IO.newIORef SetF.empty
  symNonce <- N.freshNonce N.globalNonceGenerator

  let vcfg = PC.defaultVerificationCfg
  let solver = PC.cfgSolver vcfg
  let saveInteraction = PC.cfgSolverInteractionFile vcfg
  (treeBuilder :: TreeBuilder '(sym, arch)) <- liftIO $ startSomeTreeBuilder (PA.ValidRepr sym validArch) (PC.cfgTraceTree vcfg)

  PS.withOnlineSolver solver saveInteraction sym $ \bak -> do
    let eenv = PM.EquivEnv {
            PM.envWhichBinary = Nothing
          , PM.envValidArch = validArch
          , PM.envCtx = error "envCtx"
          , PM.envArchVals = error "envArchVals"
          , PM.envLLVMArchVals = error "envLLVMArchVals"
          , PM.envExtensions = error "envExtensions"
          , PM.envPCRegion = error "envPCRegion"
          , PM.envMemTraceVar = error "envMemTraceVar"
          , PM.envBlockEndVar = error "envBlockEndVar"
          , PM.envLogger = error "envLogger"
          , PM.envConfig = vcfg
          , PM.envValidSym = PS.Sym symNonce sym bak
          , PM.envStartTime = error "envStartTime"
          , PM.envCurrentFrame = mempty
          , PM.envPathCondition = mempty
          , PM.envNonceGenerator = gen
          , PM.envParentNonce = error "envParentNonce"
          , PM.envUndefPointerOps = error "envUndefPointerOps"
          , PM.envParentBlocks = []
          , PM.envEqCondFns = Map.empty
          , PM.envStatistics = error "envStatistics"
          , PM.envOverrides = \_ -> Map.empty
          , PM.envTreeBuilder = treeBuilder
          , PM.envResetTraceTree = return ()
          , PM.envUnsatCacheRef = unsatCache
          , PM.envSatCacheRef = satCache
          , PM.envTargetEquivRegs = Set.empty
          , PM.envPtrAssertions = error "envPtrAssertions"
          , PM.envCurrentPriority = PM.normalPriority PM.PriorityUserRequest
          
          
    }
    f eenv

inEquivM :: PA.ValidArch arch => Proxy arch -> (forall sym. PM.EquivM sym arch a) -> IO a
inEquivM px f = do
  mx <- withEqEnv px (\eenv -> PM.runEquivM eenv f)
  case mx of
    Left err -> fail (show err)
    Right a -> return a

inEquivM' :: PA.ValidArch arch => Proxy arch -> (forall sym. PM.EquivEnv sym arch -> PM.EquivEnv sym arch) -> (forall sym. PM.EquivM sym arch a) -> IO a
inEquivM' px g f = do
  mx <- withEqEnv px (\eenv -> PM.runEquivM (g eenv) f)
  case mx of
    Left err -> fail (show err)
    Right a -> return a

main :: IO ()
main = do
  let tests = TT.testGroup "SolverTests" $ [
          TT.testGroup "Assumptions" $ 
            [ TTH.testCase "negation_impossible" $ inEquivM (Proxy @AArch32) $ PM.withSym $ \sym -> do
                x1 <- liftIO $ W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
                x2 <- liftIO $ W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
                x1_eq_x2 <- liftIO $ W4.isEq sym x1 x2
                not_x1_eq_x2 <- liftIO $ W4.notPred sym x1_eq_x2
                PM.withAssumption x1_eq_x2 $ do
                  PM.goalSat "test" not_x1_eq_x2 $ \case
                    W4.Sat{} -> liftIO $ TTH.assertFailure "Unexpected Sat"
                    W4.Unsat{} -> return ()
                    W4.Unknown{} -> liftIO $ TTH.assertFailure "Unexpected Timeout"
                PM.goalSat "test" not_x1_eq_x2 $ \case
                  W4.Sat{} -> return ()
                  W4.Unsat{} -> liftIO $ TTH.assertFailure "Unexpected Unsat"
                  W4.Unknown{} -> liftIO $ TTH.assertFailure "Unexpected Timeout"                
            ]
          , TT.testGroup "Timeout" $
            [ TTH.testCase "timeout_then_check" $ inEquivM' (Proxy @AArch32) 
                (\eenv -> eenv { PM.envConfig = (PM.envConfig eenv){PC.cfgGoalTimeout = PT.Microseconds 1}}) $ PM.withSym $ \sym -> do
                asm1 <- manyDistinctVars 10
                PM.withAssumptionSet asm1 $ do
                  asm2 <- manyDistinctVars 10
                  PM.withAssumptionSet asm2 $ do
                    goal <- manyDistinctVars 250 >>= PAs.toPred sym
                    liftIO $ putStrLn "check sat"
                    PM.goalSat "test" goal $ \case
                      W4.Sat _ -> liftIO $ TTH.assertFailure "Expected Timeout"
                      W4.Unsat{} -> liftIO $ TTH.assertFailure "Unexpected Unsat"
                      W4.Unknown{} -> return ()
                  goal <- manyDistinctVars 250 >>= PAs.toPred sym
                  PM.goalSat "test" goal $ \case
                    W4.Sat{} -> liftIO $ TTH.assertFailure "Expected Timeout"
                    W4.Unsat{} -> liftIO $ TTH.assertFailure "Unsat"
                    W4.Unknown{} -> return ()
            ]
        ]
  TT.defaultMain tests

manyDistinctVars :: forall sym arch. Int -> PM.EquivM sym arch (PAs.AssumptionSet sym)
manyDistinctVars i = PM.withSym $ \sym -> do
  es <- forM [0..i] $ \_ -> liftIO $ W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
  fmap mconcat $ forM [0..(i-1)] $ \j -> do
    (head_,(x:xs)) <- return $ splitAt j es
    fmap mconcat $ forM (head_ ++ xs) $ \x' -> do
      p <- liftIO $ W4.isEq sym x x'
      p' <- liftIO $ W4.notPred sym p
      return $ PAs.fromPred @sym p'
