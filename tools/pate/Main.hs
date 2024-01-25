{-# LANGUAGE LambdaCase #-}
module Main ( main ) where

import qualified System.Exit as SE

import           Pate.TraceTree
import qualified Pate.CLI as CLI
import qualified Options.Applicative as OA
import qualified Pate.ArchLoader as PAL
import qualified Pate.Loader as PL
import qualified Pate.Equivalence as PEq
import qualified Pate.Config as PC
import qualified Pate.Script as PS

main :: IO ()
main = do
  opts <- OA.execParser CLI.cliOptions
  let cfg' = CLI.mkRunConfig PAL.archLoader opts
  cfg <- case PC.cfgScriptPath (PL.verificationCfg cfg') of
    Just fp -> PS.readScript fp >>= \case
      Left err -> SE.die (show err)
      Right scr -> do
        let tt = PC.cfgTraceTree (PL.verificationCfg cfg')
        tt' <- forkTraceTreeHook (PS.runScript scr) tt
        return $ PL.setTraceTree tt' cfg'
    Nothing -> return cfg'
  status <- PL.runEquivConfig cfg
  case status of
    PEq.Errored err -> SE.die (show err)
    _ -> pure ()
