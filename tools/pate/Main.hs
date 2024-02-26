{-# LANGUAGE LambdaCase #-}
module Main ( main ) where

import qualified System.Exit as SE

import qualified Pate.CLI as CLI
import qualified Options.Applicative as OA
import qualified Pate.ArchLoader as PAL
import qualified Pate.Loader as PL
import qualified Pate.Equivalence as PEq
import qualified System.IO as IO

main :: IO ()
main = do
  opts <- OA.execParser CLI.cliOptions
  CLI.mkRunConfig PAL.archLoader opts Nothing >>= \case
    Left err -> SE.die (show err)
    Right cfg -> do
      status <- PL.runEquivConfig cfg
      case status of
        PEq.Errored err -> SE.die (show err)
        _ -> IO.putStrLn (show status)
