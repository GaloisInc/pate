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

data TestConfig where
  TestConfig ::
    { testArchName :: String
    , testArchProxy :: PL.ValidArchProxy arch
    , testExpectFailure :: [String]
    -- ^ tests which are failing now but eventually should succeed
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
    , T.testGroup "inequivalence" $ map (mkEquivTest cfg ShouldNotVerify) inequivTestFiles
    ]


mkTest :: TestConfig -> FilePath -> T.TestTree
mkTest cfg@(TestConfig { testArchProxy = proxy}) fp =
  T.testGroup fp $
    [ T.testCase "original-self" $ doTest (Just PT.Original) ShouldVerify proxy fp
    , T.testCase "patched-self" $ doTest (Just PT.Rewritten) ShouldVerify proxy fp
    , mkEquivTest cfg ShouldVerify fp
    ]

data ShouldVerify = ShouldVerify | ShouldNotVerify

mkEquivTest :: TestConfig -> ShouldVerify -> FilePath -> T.TestTree
mkEquivTest cfg@(TestConfig { testArchProxy = proxy}) sv fp =
  wrap $ T.testCase "equivalence" $ doTest Nothing sv proxy fp
  where
    (_, baseName) = splitFileName fp
    shouldFail = baseName `elem` (testExpectFailure cfg)

    wrap :: T.TestTree -> T.TestTree
    wrap t = if shouldFail then T.expectFail t else t

doTest ::
  forall arch.
  Maybe PT.WhichBinary ->
  ShouldVerify ->
  PL.ValidArchProxy arch ->
  FilePath ->
  IO ()
doTest mwb sv proxy fp = do
  infoCfgExists <- doesFileExist (fp <.> "info")
  let
    infoPath = if infoCfgExists then Left $ fp <.> "info" else Right PL.noPatchData
    rcfg = PL.RunConfig
      { PL.archProxy = proxy
      , PL.infoPath = infoPath
      , PL.origPath = fp <.> "original" <.> "exe"
      , PL.patchedPath = fp <.> "patched" <.> "exe"
      , PL.discoveryCfg = PT.defaultDiscoveryCfg
      , PL.logger =
          -- We discard logs while testing
          LJ.LogAction $ \_ -> return ()
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
