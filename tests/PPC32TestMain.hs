{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let cfg32 = TestConfig
        { testArchName = "ppc32"
        , testArchProxy = PA.SomeValidArch @PPC.PPC32 PPC.handleSystemCall PPC.handleExternalCall PPC.ppc32HasDedicatedRegister
        , testExpectEquivalenceFailure =
            [
            -- see: https://github.com/GaloisInc/pate/issues/10
              "test-direct-calls"
            -- see: https://github.com/GaloisInc/pate/issues/17
            -- , "test-int-ref-ref"

            -- see: https://github.com/GaloisInc/pate/issues/128
            , "test-call-twice"
            , "test-fun-reorder-args"
            , "test-fun-reorder"
            ]
        , testExpectSelfEquivalenceFailure = []
        }
  runTests cfg32
