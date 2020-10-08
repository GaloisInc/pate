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
        , testExpectFailure = [ "test-direct-calls"
                              , "test-read-reorder"
                              , "test-write-reorder"
                              , "test-stack-variable"
                              ]
        }
  runTests cfg
