{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let cfg64 = TestConfig
        { testArchName = "ppc"
        , testArchProxy = PA.SomeValidArch @PPC.PPC64 PPC.handleSystemCall PPC.handleExternalCall PPC.ppc64HasDedicatedRegister
        , testExpectEquivalenceFailure =
            [
            -- see: https://github.com/GaloisInc/pate/issues/10
              "test-direct-calls"
            -- see: https://github.com/GaloisInc/pate/issues/17
            , "test-int-ref-ref"
            ]
        , testExpectSelfEquivalenceFailure = []
        }
  runTests cfg64
  -- let cfg32 = TestConfig
  --       { testArchName = "ppc32"
  --       , testArchProxy = PA.SomeValidArch @PPC.PPC32 PPC.handleSystemCall PPC.handleExternalCall
  --       , testExpectEquivalenceFailure =
  --           [
  --           -- see: https://github.com/GaloisInc/pate/issues/10
  --             "test-direct-calls"
  --           -- see: https://github.com/GaloisInc/pate/issues/17
  --           , "test-int-ref-ref"
  --           ]
  --       , testExpectSelfEquivalenceFailure = []
  --       }
  -- runTests cfg32
