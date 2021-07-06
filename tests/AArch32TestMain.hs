{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.AArch32 as AArch32
import           TestBase

main :: IO ()
main = do
  let cfg = TestConfig
        { testArchName = "aarch32"
        , testArchProxy = PA.SomeValidArch @AArch32.AArch32 AArch32.handleSystemCall AArch32.handleExternalCall
        , testExpectEquivalenceFailure =
            [
            -- see: https://github.com/GaloisInc/pate/issues/10
              "test-direct-calls"
            -- see: https://github.com/GaloisInc/pate/issues/17
            , "test-int-ref-ref"
            -- see: https://github.com/GaloisInc/pate/issues/31
            , "test-write-reorder-call"
             -- see: https://github.com/GaloisInc/pate/issues/30
            -- test is now passing, although the classification bug
            -- still causes a warning
             , "test-write-reorder"
            ]
        , testExpectSelfEquivalenceFailure = [ ]
        }
  runTests cfg
