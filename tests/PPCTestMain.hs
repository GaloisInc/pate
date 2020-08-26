{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Pate.PPC as PPC
import qualified Pate.Loader as PL
import           TestBase

main :: IO ()
main = runTests "ppc" (PL.ValidArchProxy @PPC.PPC64)
