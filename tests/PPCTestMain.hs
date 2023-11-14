module Main ( main ) where

import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = do
  let cfg64 = TestConfig
        { testArchName = "ppc"
        , testArchLoader = PPC.archLoader
        , testExpectEquivalenceFailure =
            [ "stack-struct", "unequal/stack-struct"
            -- https://github.com/GaloisInc/pate/issues/350
            , "malloc-simple", "unequal/malloc-simple"
            -- missing interactive test support
            , "desync-defer", "desync-simple"
            ]
        , testExpectSelfEquivalenceFailure = [
            -- https://github.com/GaloisInc/pate/issues/350
            "malloc-simple"
            ]
        -- TODO: we should define a section name here and read its address
        -- from the ELF
        -- see: https://github.com/GaloisInc/pate/issues/294
        , testOutputAddress = read "0003f000"
        }
  runTests cfg64
