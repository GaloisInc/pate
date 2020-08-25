{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where
import qualified Pate.PPC as PPC
import           TestBase

main :: IO ()
main = runTests "ppc" (ValidArchProxy @PPC.PPC64)
