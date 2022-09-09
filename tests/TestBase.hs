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

import qualified Data.IORef as IOR

import           Data.Maybe
import           Data.List ( intercalate )
import qualified Lumberjack as LJ
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import qualified Test.Tasty.ExpectedFailure as T

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Loader as PL
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Equivalence.Error as PEE

data TestConfig where
  TestConfig ::
    { testArchName :: String
    , testArchLoader :: PA.ArchLoader PEE.LoadError
    , testExpectEquivalenceFailure :: [String]
    -- ^ tests which are failing now but eventually should succeed
    , testExpectSelfEquivalenceFailure :: [String]
    -- ^ tests which fail to prove self-equivalence
    , testOutputAddress :: PC.Address
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

expectEquivalenceFailure :: TestConfig -> ShouldVerify -> FilePath -> Bool
expectEquivalenceFailure cfg sv fp =
  baseName `elem` (testExpectEquivalenceFailure cfg)
  where
     (_, baseName') = splitFileName fp
     baseName = case sv of
       ShouldVerify -> baseName'
       ShouldNotVerify -> "unequal/" ++ baseName'
       ShouldConditionallyVerify -> "conditional/" ++ baseName'

mkTest :: TestConfig -> FilePath -> T.TestTree
mkTest cfg fp =
  T.testGroup fp $
    [ wrap $ T.testCase "original-self" $ doTest (Just PBi.OriginalRepr) cfg ShouldVerify fp
    , wrap $ T.testCase "patched-self" $ doTest (Just PBi.PatchedRepr) cfg ShouldVerify fp
    , mkEquivTest cfg ShouldVerify fp
    ]
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectSelfEquivalenceFailure cfg fp) then T.expectFail t else t    

data ShouldVerify = ShouldVerify | ShouldNotVerify | ShouldConditionallyVerify

mkEquivTest :: TestConfig -> ShouldVerify -> FilePath -> T.TestTree
mkEquivTest cfg sv fp =
  wrap $ T.testCase "equivalence" $ doTest Nothing cfg sv fp
  where
    wrap :: T.TestTree -> T.TestTree
    wrap t = if (expectEquivalenceFailure cfg sv fp) then T.expectFail t else t


-- We assume that all of the tests have be compiled with a linker script that
-- defines this section *after* the default data section as the output memory section
defaultOutputRegion :: TestConfig -> PC.MemRegion
defaultOutputRegion cfg  = PC.MemRegion
  { PC.memRegionStart = testOutputAddress cfg
  -- NB: in general we could read the actual section from the ELF, but we
  -- assume the linker script has placed only read-only memory after this
  -- section
  -- see: https://github.com/GaloisInc/pate/issues/294
  , PC.memRegionLength = 4000
  }

defaultPatchData :: TestConfig -> PC.PatchData
defaultPatchData cfg =
  mempty { PC.observableMemory = [defaultOutputRegion cfg] }

doTest ::
  forall bin.
  Maybe (PBi.WhichBinaryRepr bin) ->
  TestConfig ->
  ShouldVerify ->
  FilePath ->
  IO ()
doTest mwb cfg sv fp = do
  infoCfgExists <- doesFileExist (fp <.> "toml")
  (logsRef :: IOR.IORef [String]) <- IOR.newIORef []

  let
    addLogMsg :: String -> IO ()
    addLogMsg msg = IOR.atomicModifyIORef' logsRef $ \logs -> (msg : logs, ())

    failTest :: String -> IO ()
    failTest msg = do
      logs <- IOR.readIORef logsRef
      T.assertFailure (msg ++ "\n" ++ (intercalate "\n" (reverse logs)))

    infoPath = if infoCfgExists then Just $ fp <.> "toml" else Nothing
    rcfg = PL.RunConfig
      { PL.patchInfoPath = infoPath
      , PL.patchData = defaultPatchData cfg
      , PL.origPaths = PLE.simplePaths (fp <.> "original" <.> "exe")
      , PL.patchedPaths = PLE.simplePaths (fp <.> "patched" <.> "exe")
      , PL.verificationCfg = PC.defaultVerificationCfg { PC.cfgFailureMode = PC.ThrowOnAnyFailure }
      , PL.logger = \(PA.SomeValidArch{}) -> do
          let
            act = LJ.LogAction $ \e -> case e of
              PE.Warning err -> do
                addLogMsg $ "WARNING: " ++ show err
              PE.ErrorRaised err -> putStrLn $ "Error: " ++ show err
              PE.ProofTraceEvent _ oAddr pAddr msg _ -> do
                let addr = case oAddr == pAddr of
                      True -> show oAddr
                      False -> "(" ++ show oAddr ++ "," ++ show pAddr ++ ")"
                addLogMsg $ addr ++ ":" ++ show msg
              PE.StrongestPostDesync pPair _ ->
                addLogMsg $ "Desync at: " ++ show pPair
              PE.StrongestPostObservable pPair _ ->
                addLogMsg $ "Observable counterexample at: " ++ show pPair
              PE.StrongestPostOverallResult status _ ->
                addLogMsg $ "Overall Result:" ++ show status
              _ -> return ()
          return $ PL.Logger act []
      , PL.archLoader = testArchLoader cfg
      , PL.useDwarfHints = False
      }
  result <- case mwb of
    Just wb -> PL.runSelfEquivConfig rcfg wb
    Nothing -> PL.runEquivConfig rcfg
  case result of
    PEq.Errored err -> failTest (show err)
    PEq.Equivalent -> case sv of
      ShouldVerify -> return ()
      _ -> failTest "Unexpectedly proved equivalence."
    PEq.Inequivalent -> case sv of
      ShouldVerify -> failTest "Failed to prove equivalence."
      ShouldNotVerify -> return ()
      ShouldConditionallyVerify -> failTest "Failed to prove conditional equivalence."
    PEq.ConditionallyEquivalent -> case sv of
      ShouldVerify -> failTest "Failed to prove equivalence."
      ShouldNotVerify -> failTest "Unexpectedly proved conditional equivalence."
      ShouldConditionallyVerify -> return ()
