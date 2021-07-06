{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let cfg = TestConfig
        { testArchName = "ppc"
        , testArchProxy = PA.SomeValidArch @PPC.PPC64 PPC.handleSystemCall PPC.handleExternalCall
        , testExpectEquivalenceFailure =
            [
            -- see: https://github.com/GaloisInc/pate/issues/10
              "test-direct-calls"
            -- see: https://github.com/GaloisInc/pate/issues/17
            , "test-int-ref-ref"
            ]
        , testExpectSelfEquivalenceFailure = []
        }
  runTests cfg
