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
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "0003f000"
        }
  runTests cfg64
