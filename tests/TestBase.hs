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
mkTest cfg@(TestConfig { testArchProxy = proxy}) fp = wrap $ T.testCase fp $ doTest proxy fp
  where
    (_, baseName) = splitFileName fp
    shouldFail = baseName `elem` (testExpectFailure cfg)

    wrap :: T.TestTree -> T.TestTree
    wrap t = if shouldFail then T.expectFail t else t

doTest :: forall arch. PL.ValidArchProxy arch -> FilePath -> IO ()
doTest proxy fp = do
  let rcfg = PL.RunConfig
        { PL.archProxy = proxy
        , PL.infoPath = Left $ fp <.> "info"
        , PL.origPath = fp <.> "original" <.> "exe"
        , PL.patchedPath = fp <.> "patched" <.> "exe"
        }

  PL.runEquivConfig rcfg >>= \case
    Left err -> T.assertFailure (show err)
    Right _ -> return ()
