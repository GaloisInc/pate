module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let archData = PA.ValidArchData { PA.validArchSyscallDomain = PPC.handleSystemCall
                                  , PA.validArchFunctionDomain = PPC.handleExternalCall
                                  , PA.validArchDedicatedRegisters = PPC.ppc32HasDedicatedRegister
                                  , PA.validArchArgumentMapping = PPC.argumentMapping
                                  , PA.validArchOrigExtraSymbols = mempty
                                  , PA.validArchPatchedExtraSymbols = mempty
                                  }
  let cfg32 = TestConfig
        { testArchName = "ppc32"
        , testArchProxy = PA.SomeValidArch archData
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
