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

import           System.FilePath
import           System.FilePath.Glob (namesMatching)

import           Data.Maybe
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
    } -> TestConfig

runTests :: TestConfig -> IO ()
runTests cfg = do
  let
    name = testArchName cfg
    glob = "tests" </> name </> "*.info"
  testFiles <- mapMaybe (stripExtension "info") <$> namesMatching glob
  T.defaultMain $ T.testGroup name $ map (mkTest cfg) testFiles

mkTest :: TestConfig -> FilePath -> T.TestTree
mkTest cfg@(TestConfig { testArchProxy = proxy}) fp =
  T.testGroup fp $
    [ T.testCase "original-self" $ doTest (Just PT.Original) proxy fp
    , T.testCase "patched-self" $ doTest (Just PT.Rewritten) proxy fp
    , wrap $ T.testCase "equivalence" $ doTest Nothing proxy fp
    ]
  where
    (_, baseName) = splitFileName fp
    shouldFail = baseName `elem` (testExpectFailure cfg)

    wrap :: T.TestTree -> T.TestTree
    wrap t = if shouldFail then T.expectFail t else t

doTest :: forall arch. Maybe PT.WhichBinary -> PL.ValidArchProxy arch -> FilePath -> IO ()
doTest mwb proxy fp = do
  let rcfg = PL.RunConfig
        { PL.archProxy = proxy
        , PL.infoPath = Left $ fp <.> "info"
        , PL.origPath = fp <.> "original" <.> "exe"
        , PL.patchedPath = fp <.> "patched" <.> "exe"
        }
  result <- case mwb of
    Just wb -> PL.runSelfEquivConfig rcfg wb
    Nothing -> PL.runEquivConfig rcfg
  case result of
    Left err -> T.assertFailure (show err)
    Right _ -> return ()
