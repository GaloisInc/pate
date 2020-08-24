{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Control.Applicative
import           Control.Lens hiding ( pre )
import           Control.Monad.Except
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import           Data.Foldable
import           Data.Functor.Const ( Const(..) )
import qualified Options.Applicative as OA
import           System.Exit

import qualified Data.Map as Map
import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Macaw.PPC as PPC
import           Data.Macaw.PPC.PPCReg ()
import qualified Dismantle.PPC as DP
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Renovate as R
import qualified Renovate.Arch.PPC as RP
import qualified Pate.Verification as V
import           Pate.Utils ( (<>|) )

import           ELF ( parseElfOrDie )

main :: IO ()
main = do
  opts <- OA.execParser cliOptions
  bs_original <- BS.readFile (originalBinary opts)
  e64_original <- parseElfOrDie (error "32") return bs_original

  bs_patched <- BS.readFile (patchedBinary opts)
  e64_patched <- parseElfOrDie (error "32") return bs_patched  
  
  mem_original <- MBL.loadBinary MM.defaultLoadOptions e64_original
  mem_patched <- MBL.loadBinary MM.defaultLoadOptions e64_patched
  
  hdlAlloc <- CFH.newHandleAllocator
  let archInfo = PPC.ppc64_linux_info mem_original

  info <- R.analyzeElf config hdlAlloc
  v <- runExceptT (V.verifyPairs archInfo mem_original mem_patched Map.empty (ri ^. R.riRewritePairs))
  case v of
    Left err -> die (show err)
    Right _ -> pure ()

data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  } deriving (Eq, Ord, Read, Show)

cliOptions :: OA.ParserInfo CLIOptions
cliOptions = OA.info (OA.helper <*> parser)
  (  OA.fullDesc
  <> OA.progDesc "Run a quick test of rewrite verification"
  ) where
  parser = pure CLIOptions
    <*> (OA.strOption
      (  OA.long "original"
      <> OA.short 'o'
      <> OA.metavar "EXE"
      <> OA.help "Original binary"
      ))
    <*> (OA.strOption
      (  OA.long "patched"
      <> OA.short 'p'
      <> OA.metavar "EXE"
      <> OA.help "Patched binary"
      ))


layout :: R.LayoutStrategy
layout = R.LayoutStrategy R.Parallel R.BlockGrouping R.WholeFunctionTrampoline

config :: R.RenovateConfig RP.PPC64 (E.Elf 64) R.AnalyzeOnly (Const (R.BlockInfo RP.PPC64))
config = RP.config64 analysis

analysis :: R.AnalyzeOnly RP.PPC64 binFmt (Const (R.BlockInfo RP.PPC64))
analysis = R.AnalyzeOnly
  { R.aoAnalyze = \e -> return $ Const $ R.analysisBlockInfo e }

