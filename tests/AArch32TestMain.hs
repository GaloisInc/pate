module Main ( main ) where

import qualified Pate.Arch as PA
import qualified Pate.AArch32 as AArch32
import           TestBase

main :: IO ()
main = do
  let archData = PA.ValidArchData { PA.validArchSyscallDomain = AArch32.handleSystemCall
                                  , PA.validArchFunctionDomain = AArch32.handleExternalCall
                                  , PA.validArchDedicatedRegisters = AArch32.hasDedicatedRegister
                                  , PA.validArchArgumentMapping = AArch32.argumentMapping
                                  , PA.validArchOrigExtraSymbols = mempty
                                  , PA.validArchPatchedExtraSymbols = mempty
                                  }
  let cfg = TestConfig
        { testArchName = "aarch32"
        , testArchProxy = PA.SomeValidArch archData
        , testExpectEquivalenceFailure =
            [ "stack-struct", "unequal/stack-struct"
            ]
        , testExpectSelfEquivalenceFailure = [ ]
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "0003f000"
        }
  runTests cfg
