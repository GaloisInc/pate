module Main ( main ) where

import qualified Pate.AArch32 as AArch32
import           TestBase

main :: IO ()
main = do
  let cfg = TestConfig
        { testArchName = "aarch32"
        , testArchLoader = AArch32.archLoader
        , testExpectEquivalenceFailure =
            [ "stack-struct", "unequal/stack-struct", "max-signed"
              -- missing interactive test support
            ]
        , testExpectSelfEquivalenceFailure = []
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "0003f000"
        }
  runTests cfg
