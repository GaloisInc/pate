module Main ( main ) where

import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let cfg32 = TestConfig
        { testArchName = "ppc32"
        , testArchLoader = PPC.archLoader
        , testExpectEquivalenceFailure =
            [ "stack-struct", "unequal/stack-struct"
            -- https://github.com/GaloisInc/pate/issues/327
            , "malloc-simple", "unequal/malloc-simple"
            ]
        , testExpectSelfEquivalenceFailure = [
            -- https://github.com/GaloisInc/pate/issues/327
            "malloc-simple"
            ]
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "1003f000"
        }
  runTests cfg32
