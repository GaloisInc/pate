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
              "const-args"

              -- failing due to macaw analysis failures:
              -- see: https://github.com/GaloisInc/pate/issues/128
            , "reorder-call"
            , "args-equal"
            , "reestablish-equality"
            ]
        , testExpectSelfEquivalenceFailure =
            [
              -- failing due to macaw analysis failures:
              -- see: https://github.com/GaloisInc/pate/issues/128
              "const-args"
            , "reorder-call"
            , "args-equal"
            , "reestablish-equality"
            ]
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "1003f000"
        }
  runTests cfg32
