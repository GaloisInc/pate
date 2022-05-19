module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let archData = PA.ValidArchData { PA.validArchSyscallDomain = PPC.handleSystemCall
                                  , PA.validArchFunctionDomain = PPC.handleExternalCall
                                  , PA.validArchDedicatedRegisters = PPC.ppc64HasDedicatedRegister
                                  , PA.validArchArgumentMapping = PPC.argumentMapping
                                  , PA.validArchOrigExtraSymbols = mempty
                                  , PA.validArchPatchedExtraSymbols = mempty
                                  }
  let cfg64 = TestConfig
        { testArchName = "ppc"
        , testArchProxy = PA.SomeValidArch archData
        , testExpectEquivalenceFailure =
            [
              "const-args"
            ]
        , testExpectSelfEquivalenceFailure = []
        , testOutputAddress = read "0003f000"
        }
  runTests cfg64
