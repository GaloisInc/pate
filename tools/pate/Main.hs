module Main ( main ) where

import qualified System.Exit as SE

import           Pate.TraceTree
import qualified Pate.CLI as CLI
import qualified Options.Applicative as OA
import qualified Pate.ArchLoader as PAL
import qualified Pate.Loader as PL
import qualified Pate.Equivalence as PEq


main :: IO ()
main = do
  opts <- OA.execParser CLI.cliOptions
  let cfg = CLI.mkRunConfig PAL.archLoader opts
  status <- PL.runEquivConfig cfg
  case status of
    PEq.Errored err -> SE.die (show err)
    _ -> pure ()