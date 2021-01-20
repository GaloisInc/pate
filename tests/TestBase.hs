{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module TestBase
  ( runTests
  , TestConfig(..)
  ) where

import           System.Directory
import           System.FilePath
import           System.FilePath.Glob (namesMatching)

import           Data.Maybe
import qualified Lumberjack as LJ
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import qualified Test.Tasty.ExpectedFailure as T

import qualified Pate.Loader as PL
import qualified Pate.Types as PT
import qualified Pate.Event as PE
import qualified Pate.CounterExample as PCE

data TestConfig where
  TestConfig ::
    { testArchName :: String
    , testArchProxy :: PL.ValidArchProxy arch
    , testExpectEquivalenceFailure :: [String]
    -- ^ tests which are failing now but eventually should succeed
    , testExpectSelfEquivalenceFailure :: [String]
    -- ^ tests which fail to prove self-equivalence
    } -> TestConfig

runTests :: TestConfig -> IO ()
runTests cfg = do
  let
    name = testArchName cfg
    glob = "tests" </> name </> "*.original.exe"
    globUnequal = "tests" </> name </> "unequal" </> "*.original.exe"

  equivTestFiles <- mapMaybe (stripExtension "original.exe") <$> namesMatching glob
  inequivTestFiles <- mapMaybe (stripExtension "original.exe") <$> namesMatching globUnequal

  T.defaultMain $ T.testGroup name $
    [ T.testGroup "equivalence" $ map (mkTest cfg) equivTestFiles
    , T.testGroup "inequivalence" $ map (\fp -> T.testGroup fp $ [mkEquivTest cfg ShouldNotVerify fp]) inequivTestFiles
    ]

expectSelfEquivalenceFailure :: TestConfig -> FilePath -> Bool
expectSelfEquivalenceFailure cfg fp = baseName `elem` (testExpectSelfEquivalenceFailure cfg)
  where
     (_, baseName) = splitFileName fp

expectEquivalenceFailure :: TestConfig -> FilePath -> Bool
expectEquivalenceFailure cfg fp =
  expectSelfEquivalenceFailure cfg fp || baseName `elem` (testExpectEquivalenceFailure cfg)
  where
     (_, baseName) = splitFileName fp

mkTest :: TestConfig -> FilePath -> T.TestTree
mkTest cfg@(TestConfig { testArchProxy = proxy}) fp =
  T.testGroup fp $
    [ wrap $ T.testCase "original-self" $ doTest (Just PT.OriginalRepr) ShouldVerify proxy fp
    , wrap $ T.testCase "patched-self" $ doTest (Just PT.PatchedRepr) ShouldVerify proxy fp
    , mkEquivTest cfg ShouldVerify fp
    ]
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectSelfEquivalenceFailure cfg fp) then T.expectFail t else t    

data ShouldVerify = ShouldVerify | ShouldNotVerify

mkEquivTest :: TestConfig -> ShouldVerify -> FilePath -> T.TestTree
mkEquivTest cfg@(TestConfig { testArchProxy = proxy}) sv fp =
  wrap $ T.testCase "equivalence" $ doTest Nothing sv proxy fp
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectEquivalenceFailure cfg fp) then T.expectFail t else t

doTest ::
  forall arch bin.
  Maybe (PT.WhichBinaryRepr bin) ->
  ShouldVerify ->
  PL.ValidArchProxy arch ->
  FilePath ->
  IO ()
doTest mwb sv proxy@PL.ValidArchProxy fp = do
  infoCfgExists <- doesFileExist (fp <.> "info")
  let
    infoPath = if infoCfgExists then Left $ fp <.> "info" else Right PL.noPatchData
    rcfg = PL.RunConfig
      { PL.archProxy = proxy
      , PL.infoPath = infoPath
      , PL.origPath = fp <.> "original" <.> "exe"
      , PL.patchedPath = fp <.> "patched" <.> "exe"
      , PL.verificationCfg =
          -- avoid frame computations for self-tests
          PT.defaultVerificationCfg { PT.cfgComputeEquivalenceFrames = False }
      , PL.logger =
          LJ.LogAction $ \e -> case e of
            PE.AnalysisStart pPair -> do
              putStrLn $ concat $
                [ "Checking equivalence of "
                , PT.ppBlock (PT.pOrig pPair)
                , " and "
                , PT.ppBlock (PT.pPatched pPair)
                , " (" ++ PT.ppBlockEntry (PT.concreteBlockEntry (PT.pOrig pPair)) ++ ") "
                , ": "
                ]
            PE.CheckedEquivalence _ PE.Equivalent time -> do
              putStrLn $ "Successful equivalence check: " ++ show time
            PE.CheckedEquivalence _ _ time -> do
              putStrLn $ "Failed equivalence check: " ++ show time
            PE.CheckedBranchCompleteness _ PE.BranchesComplete time -> do
              putStrLn $ "Branch completeness check: " ++ show time
            PE.ComputedPrecondition _ time -> do
              putStrLn $ "Precondition propagation: " ++ show time
            PE.ProvenGoal _ goal time -> do
              putStrLn $ "Proof result: " ++ show time ++ "\n" ++ show goal
            PE.Warning _ err -> do
              putStrLn $ "WARNING: " ++ show err
            PE.ErrorRaised err -> putStrLn $ "Error: " ++ PCE.ppEquivalenceError err
            _ -> return ()
      }
  result <- case mwb of
    Just wb -> PL.runSelfEquivConfig rcfg wb
    Nothing -> PL.runEquivConfig rcfg
  case result of
    Left err -> T.assertFailure (show err)
    Right True | ShouldVerify <- sv -> return ()
    Right False | ShouldNotVerify <- sv -> return ()
    Right False | ShouldVerify <- sv -> T.assertFailure "Failed to prove equivalence."
    Right True | ShouldNotVerify <- sv -> T.assertFailure "Unexpectedly proved equivalence."
