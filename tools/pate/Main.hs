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


import qualified Options.Applicative as OA
import           System.Exit

import           Data.Parameterized.Some

import qualified Pate.AArch32 as AArch32
import qualified Pate.PPC as PPC
import qualified Pate.Loader as PL
import qualified Pate.Types as PT

main :: IO ()
main = do
  opts <- OA.execParser cliOptions
  Some proxy <- return $ archKToProxy (archK opts)
  let
    infoPath = case blockInfo opts of
      Just path -> Left path
      Nothing -> Right PL.noPatchData
    discoverCfg =
      PT.defaultDiscoveryCfg
        { PT.cfgPairMain = not $ noPairMain opts
        , PT.cfgDiscoverFuns = not $ noDiscoverFuns opts
        }
    cfg = PL.RunConfig
        { PL.archProxy = proxy
        , PL.infoPath = infoPath
        , PL.origPath = originalBinary opts
        , PL.patchedPath = patchedBinary opts
        , PL.discoveryCfg = discoverCfg
        }
  PL.runEquivConfig cfg >>= \case
    Left err -> die (show err)
    Right _ -> pure ()

data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  , blockInfo :: Maybe FilePath
  , archK :: ArchK
  , noPairMain :: Bool
  , noDiscoverFuns :: Bool
  } deriving (Eq, Ord, Read, Show)

data ArchK = PPC | ARM
  deriving (Eq, Ord, Read, Show)

archKToProxy :: ArchK -> Some PL.ValidArchProxy
archKToProxy a = case a of
  PPC -> Some (PL.ValidArchProxy @PPC.PPC64)
  ARM -> Some (PL.ValidArchProxy @AArch32.AArch32)


cliOptions :: OA.ParserInfo CLIOptions
cliOptions = OA.info (OA.helper <*> parser)
  (  OA.fullDesc
  <> OA.progDesc "Verify the equivalence of two binaries"
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
    <*> (OA.optional (OA.strOption
      (  OA.long "blockinfo"
      <> OA.short 'b'
      <> OA.metavar "FILENAME"
      <> OA.help "Block information relating binaries"
      -- <> OA.value Nothing
      )))
    <*> (OA.option (OA.auto @ArchK)
      (  OA.long "arch"
      <> OA.short 'a'
      <> OA.metavar "ARCH"
      <> OA.help "Architecture of the given binaries"
      ))
    <*> (OA.switch
      (  OA.long "ignoremain"
      <> OA.short 'm'
      <> OA.help "Don't add the main entry points to the set of function equivalence checks."
      ))
    <*> (OA.switch
      (  OA.long "nodiscovery"
      <> OA.short 'd'
      <> OA.help "Don't dynamically discover function pairs based on calls."
      ))
