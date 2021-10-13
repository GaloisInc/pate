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

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Loader as PL
import qualified Pate.PatchPair as PPa

data TestConfig where
  TestConfig ::
    { testArchName :: String
    , testArchProxy :: PA.SomeValidArch arch
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
    globCondequal = "tests" </> name </> "conditional" </> "*.original.exe"

  equivTestFiles <- mapMaybe (stripExtension "original.exe") <$> namesMatching glob
  inequivTestFiles <- mapMaybe (stripExtension "original.exe") <$> namesMatching globUnequal
  condequivTestFiles <- mapMaybe (stripExtension "original.exe") <$> namesMatching globCondequal

  T.defaultMain $ T.testGroup name $
    [ T.testGroup "equivalence" $ map (mkTest cfg) equivTestFiles
    , T.testGroup "inequivalence" $ map (\fp -> T.testGroup fp $ [mkEquivTest cfg ShouldNotVerify fp]) inequivTestFiles
    , T.testGroup "conditional equivalence" $ map (\fp -> T.testGroup fp $ [mkEquivTest cfg ShouldConditionallyVerify fp]) condequivTestFiles
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
    [ wrap $ T.testCase "original-self" $ doTest (Just PBi.OriginalRepr) ShouldVerify proxy fp
    , wrap $ T.testCase "patched-self" $ doTest (Just PBi.PatchedRepr) ShouldVerify proxy fp
    , mkEquivTest cfg ShouldVerify fp
    ]
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectSelfEquivalenceFailure cfg fp) then T.expectFail t else t    

data ShouldVerify = ShouldVerify | ShouldNotVerify | ShouldConditionallyVerify

mkEquivTest :: TestConfig -> ShouldVerify -> FilePath -> T.TestTree
mkEquivTest cfg@(TestConfig { testArchProxy = proxy}) sv fp =
  wrap $ T.testCase "equivalence" $ doTest Nothing sv proxy fp
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectEquivalenceFailure cfg fp) then T.expectFail t else t

doTest ::
  forall arch bin.
  Maybe (PBi.WhichBinaryRepr bin) ->
  ShouldVerify ->
  PA.SomeValidArch arch ->
  FilePath ->
  IO ()
doTest mwb sv proxy@(PA.SomeValidArch {}) fp = do
  infoCfgExists <- doesFileExist (fp <.> "info")
  let
    infoPath = if infoCfgExists then Left $ fp <.> "info" else Right PC.noPatchData
    -- avoid frame computations for self-tests
    computeFrames = case mwb of
      Just _ -> False
      Nothing -> True
    rcfg = PC.RunConfig
      { PC.archProxy = proxy
      , PC.infoPath = infoPath
      , PC.origPath = fp <.> "original" <.> "exe"
      , PC.patchedPath = fp <.> "patched" <.> "exe"
      , PC.origHints = mempty
      , PC.patchedHints = mempty
      , PC.verificationCfg =
          PC.defaultVerificationCfg { PC.cfgComputeEquivalenceFrames = computeFrames }
      , PC.logger =
          LJ.LogAction $ \e -> case e of
            PE.AnalysisStart pPair -> do
              putStrLn $ concat $
                [ "Checking equivalence of "
                , PB.ppBlock (PPa.pOriginal pPair)
                , " and "
                , PB.ppBlock (PPa.pPatched pPair)
                , " (" ++ PB.ppBlockEntry (PB.concreteBlockEntry (PPa.pOriginal pPair)) ++ ") "
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
            PE.ProofIntermediate _ _ time -> do
              putStrLn $ "Intermediate Proof result: " ++ show time
            PE.ProvenGoal _ goal time -> do
              putStrLn $ "Toplevel Proof result: " ++ show time ++ "\n" ++ show goal
            PE.Warning _ err -> do
              putStrLn $ "WARNING: " ++ show err
            PE.ErrorRaised err -> putStrLn $ "Error: " ++ show err
            _ -> return ()
      }
  result <- case mwb of
    Just wb -> PL.runSelfEquivConfig rcfg wb
    Nothing -> PL.runEquivConfig rcfg
  case result of
    PEq.Errored err -> T.assertFailure (show err)
    PEq.Equivalent -> case sv of
      ShouldVerify -> return ()
      _ -> T.assertFailure "Unexpectedly proved equivalence."
    PEq.Inequivalent -> case sv of
      ShouldVerify -> T.assertFailure "Failed to prove equivalence."
      ShouldNotVerify -> return ()
      ShouldConditionallyVerify -> T.assertFailure "Failed to prove conditional equivalence."    
    PEq.ConditionallyEquivalent -> case sv of
      ShouldVerify -> T.assertFailure "Failed to prove equivalence."
      ShouldNotVerify -> T.assertFailure "Unexpectedly proved conditional equivalence."
      ShouldConditionallyVerify -> return ()
