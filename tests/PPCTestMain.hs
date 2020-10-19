{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.PPC as PPC
import qualified Pate.Loader as PL
import           TestBase

main :: IO ()
main = do
  let cfg = TestConfig
        { testArchName = "ppc"
        , testArchProxy = PL.ValidArchProxy @PPC.PPC64
        , testExpectFailure = [
                              -- see: https://github.com/GaloisInc/pate/issues/10
                                "test-direct-calls"
                              -- see: https://github.com/GaloisInc/pate/issues/9
                              , "test-stack-variable"
                              -- see: https://github.com/GaloisInc/pate/issues/17
                              , "test-int-ref-ref"
                              ]
        }
  runTests cfg
