{-# LANGUAGE ScopedTypeVariables #-}
module Main ( main ) where

import           Control.Monad ( unless )
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Set as Set
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import qualified Text.Read as TR

import qualified Pate.Hints as PH
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Hints.DWARF as PHD

main :: IO ()
main = do
  funCSVs <- SFG.namesMatching "tests/hints/*.functions.csv.expected"
  anvillJSONs <- SFG.namesMatching "tests/hints/*.anvill.json.expected"
  probJSONs <- SFG.namesMatching "tests/hints/*.prob.json.expected"
  dwarves <- SFG.namesMatching "tests/hints/*.elf.expected"
  let tests = TT.testGroup "LoaderTests" [
          TT.testGroup "FunctionCSV" (map mkFunctionCSVTest funCSVs)
        , TT.testGroup "AnvillJSON" (map mkAnvillJSONTest anvillJSONs)
        , TT.testGroup "ProbJSON" (map mkProbJSONTest probJSONs)
        , TT.testGroup "DWARF" (map mkDWARFTest dwarves)
        ]
  TT.defaultMain tests

assertEquivalentHints :: PH.VerificationHints -> PH.VerificationHints -> TTH.Assertion
assertEquivalentHints expected actual = do
  TTH.assertEqual "Block Mappings" (Set.fromList (PH.blockMappings expected)) (Set.fromList (PH.blockMappings actual))
  TTH.assertEqual "Function Entries" (Set.fromList (PH.functionEntries expected)) (Set.fromList (PH.functionEntries actual))
  TTH.assertEqual "Data Symbols" (Set.fromList (PH.dataSymbols expected)) (Set.fromList (PH.dataSymbols actual))

mkFunctionCSVTest :: FilePath -> TT.TestTree
mkFunctionCSVTest expectedFile = TTH.testCase testName $ do
  bytes <- BSL.readFile testFile
  expected <- readFile expectedFile
  case TR.readMaybe expected of
    Just expectedHints -> do
      let (actualHints, errs) = PHC.parseFunctionHints bytes
      TTH.assertEqual "Expect no parse errors" [] errs
      assertEquivalentHints expectedHints actualHints
    Nothing -> TTH.assertFailure ("Invalid expected hints: " ++ expectedFile)
  where
    testFile = SF.dropExtension expectedFile
    testName = SF.takeFileName testFile

mkAnvillJSONTest :: FilePath -> TT.TestTree
mkAnvillJSONTest expectedFile = TTH.testCase testName $ do
  bytes <- BSL.readFile testFile
  expected <- readFile expectedFile
  case TR.readMaybe expected of
    Just expectedHints -> do
      let (actualHints, errs) = PHJ.parseAnvillSpecHints bytes
      TTH.assertEqual "Expect no parse errors" [] errs
      assertEquivalentHints expectedHints actualHints
    Nothing -> TTH.assertFailure ("Invalid expected hints: " ++ expectedFile)
  where
    testFile = SF.dropExtension expectedFile
    testName = SF.takeFileName testFile

mkProbJSONTest :: FilePath -> TT.TestTree
mkProbJSONTest expectedFile = TTH.testCase testName $ do
  bytes <- BSL.readFile testFile
  expected <- readFile expectedFile
  case TR.readMaybe expected of
    Just expectedHints -> do
      let (actualHints, errs) = PHJ.parseProbabilisticHints bytes
      TTH.assertEqual "Expect no parse errors" [] errs
      assertEquivalentHints expectedHints actualHints
    Nothing -> TTH.assertFailure ("Invalid expected hints: " ++ expectedFile)
  where
    testFile = SF.dropExtension expectedFile
    testName = SF.takeFileName testFile

mkDWARFTest :: FilePath -> TT.TestTree
mkDWARFTest expectedFile = TTH.testCase testName $ do
  bytes <- BSL.readFile testFile
  expected <- readFile expectedFile
  case TR.readMaybe expected of
    Just expectedHints -> do
      let (actualHints, errs) = PHD.parseDWARFHints bytes
      unless (null errs) $ do
        TTH.assertFailure ("DWARF parsing errors: " ++ show errs)
      assertEquivalentHints expectedHints actualHints
    Nothing -> TTH.assertFailure ("Invalid expected hints: " ++ expectedFile)
  where
    testFile = SF.dropExtension expectedFile
    testName = SF.takeFileName testFile
