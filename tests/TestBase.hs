{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module TestBase
  ( runTests
  ) where

import           System.FilePath
import           System.FilePath.Glob (namesMatching)

import           Data.Maybe
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Pate.Loader as PL

runTests :: String -> PL.ValidArchProxy arch -> IO ()
runTests name proxy = do
  let glob = "tests" </> name </> "*.info"
  testFiles <- mapMaybe (stripExtension "info") <$> namesMatching glob
  T.defaultMain $ T.testGroup name $ map (mkTest proxy) testFiles

mkTest :: PL.ValidArchProxy arch -> FilePath -> T.TestTree
mkTest proxy fp = T.testCase fp $ doTest proxy fp

doTest :: forall arch. PL.ValidArchProxy arch -> FilePath -> IO ()
doTest proxy fp = do
  let cfg = PL.RunConfig
        { PL.archProxy = proxy
        , PL.infoPath = Left $ fp <.> "info"
        , PL.origPath = fp <.> "original" <.> "exe"
        , PL.patchedPath = fp <.> "patched" <.> "exe"
        }
  PL.runEquivConfig cfg >>= \case
    Left err -> T.assertFailure (show err)
    Right _ -> return ()
