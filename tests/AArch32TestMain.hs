{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.AArch32 as AArch32
import qualified Pate.Loader as PL
import           TestBase

main :: IO ()
main = do
  let cfg = TestConfig
        { testArchName = "aarch32"
        , testArchProxy = PL.ValidArchProxy @AArch32.AArch32
        , testExpectEquivalenceFailure =
            [
            -- see: https://github.com/GaloisInc/pate/issues/10
              "test-direct-calls"
            -- see: https://github.com/GaloisInc/pate/issues/17
            , "test-int-ref-ref"
            -- see: https://github.com/GaloisInc/pate/issues/31
            , "test-write-reorder-call"
            , "test-call-twice"
            , "test-fun-reorder"
            -- see: https://github.com/GaloisInc/pate/issues/33
            , "test-read-reorder"
             -- see: https://github.com/GaloisInc/pate/issues/30
            -- test is now passing, although the classification bug
            -- still causes a warning
             --, "test-write-reorder"
            ]
        , testExpectSelfEquivalenceFailure = [ ]
        }
  runTests cfg
