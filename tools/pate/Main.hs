{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

import           Control.Applicative ( (<|>) )
import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import           Control.Monad ( join )
import qualified Data.Binary.Get as DB
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Language.C as LC
import qualified Lumberjack as LJ
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PPRT
import qualified System.Exit as SE
import qualified System.IO as IO

import qualified Data.ElfEdit as DEE
import           Data.Parameterized.Some ( Some(..) )

import qualified Pate.AArch32 as AArch32
import qualified Pate.Event as PE
import qualified Pate.PPC as PPC
import qualified Pate.Loader as PL
import qualified Pate.Types as PT

import qualified Interactive as I
import qualified Interactive.State as IS

main :: IO ()
main = do
  opts <- OA.execParser cliOptions
  ep <- archToProxy (originalBinary opts) (patchedBinary opts)
  case ep of
    Left err -> SE.die (show err)
    Right (elfErrs, Some proxy) -> do
      chan <- CC.newChan
      (logger, mConsumer) <- startLogger proxy (logTarget opts) chan
      LJ.writeLog logger (PE.ElfLoaderWarnings elfErrs)
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
            , PL.logger = logger
            , PL.discoveryCfg = discoverCfg
            }
      PL.runEquivConfig cfg >>= \case
        Left err -> SE.die (show err)
        Right _ -> pure ()

      -- Shut down the logger cleanly (if we can - the interactive logger will be
      -- persistent until the user kills it)
      CC.writeChan chan Nothing
      F.forM_ mConsumer CCA.wait

data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  , blockInfo :: Maybe FilePath
  , logTarget :: LogTarget
  , noPairMain :: Bool
  , noDiscoverFuns :: Bool
  } deriving (Eq, Ord, Read, Show)

data LogTarget = Interactive (Maybe (IS.SourcePair FilePath))
               -- ^ Logs will go to an interactive viewer
               --
               -- If source files (corresponding to the original and patched
               -- source) are provided, their contents are displayed when
               -- appropriate (on a per-function basis).
               | LogFile FilePath
               -- ^ Logs will go to a file (if present)
               | StdoutLogger
               -- ^ Log to stdout
               | NullLogger
               -- ^ Discard logs
               deriving (Eq, Ord, Read, Show)

-- | Create a logger based on the user's desire for an interactive session.
--
-- If the user requests an interactive session, this function will set up a web
-- server to stream logging events from the verifier, which the user can connect
-- to.
--
-- Otherwise, just make a basic logger that will write logs to a user-specified
-- location
startLogger :: PL.ValidArchProxy arch
            -> LogTarget
            -> CC.Chan (Maybe (PE.Event arch))
            -> IO (LJ.LogAction IO (PE.Event arch), Maybe (CCA.Async ()))
startLogger PL.ValidArchProxy lt chan =
  case lt of
    NullLogger -> return (LJ.LogAction $ \_ -> return (), Nothing)
    StdoutLogger -> logToHandle IO.stdout
    LogFile fp -> do
      hdl <- IO.openFile fp IO.WriteMode
      IO.hSetBuffering hdl IO.LineBuffering
      logToHandle hdl
    Interactive mSourceFiles -> do
      -- This odd structure makes all of the threading explicit at this top
      -- level so that there is no thread creation hidden in the Interactive
      -- module
      --
      -- The data producer/manager and the UI communicate via an IORef, which
      -- contains the up-to-date version of the state
      consumer <- CCA.async $ do
        mSourceContent <- join <$> T.traverse parseSources mSourceFiles
        stateRef <- I.newState mSourceContent
        watcher <- CCA.async $ I.consumeEvents chan stateRef
        ui <- CCA.async $ I.startInterface stateRef
        CCA.wait watcher
        CCA.wait ui
      return (logAct, Just consumer)
  where
    logAct = LJ.LogAction $ \evt -> CC.writeChan chan (Just evt)
    logToHandle hdl = do
      let consumeLogs = do
            me <- CC.readChan chan
            case me of
              Nothing -> return ()
              Just evt -> do
                PPRT.renderIO hdl (terminalFormatEvent evt)
                consumeLogs

      consumer <- CCA.async consumeLogs
      return (logAct, Just consumer)

parseSources :: IS.SourcePair FilePath -> IO (Maybe (IS.SourcePair LC.CTranslUnit))
parseSources (IS.SourcePair os ps) = do
  eos' <- LC.parseCFilePre os
  eps' <- LC.parseCFilePre ps
  case (eos', eps') of
    (Right ou, Right pu) -> return (Just (IS.SourcePair ou pu))
    (Left e, _) -> do
      IO.hPutStrLn IO.stderr ("Error parsing " ++ os)
      IO.hPutStrLn IO.stderr (show e)
      return Nothing
    (_, Left e) -> do
      IO.hPutStrLn IO.stderr ("Error parsing " ++ os)
      IO.hPutStrLn IO.stderr (show e)
      return Nothing

layout :: PP.Doc ann -> PP.SimpleDocStream ann
layout = PP.layoutPretty PP.defaultLayoutOptions

terminalFormatEvent :: PE.Event arch -> PP.SimpleDocStream PPRT.AnsiStyle
terminalFormatEvent evt =
  case evt of
    PE.LoadedBinaries {} -> layout "Loaded original and patched binaries"
    PE.ElfLoaderWarnings pes ->
      let msg = "Warnings during ELF loading:"
      in layout $ PP.vsep (msg : [ "  " <> PP.viaShow err | err <- pes ])
    PE.CheckedEquivalence (PE.BlocksPair (PE.Blocks blkO _) (PE.Blocks blkP _)) res duration ->
      let
        origAddr = PT.concreteAddress blkO
        patchedAddr = PT.concreteAddress blkP
        pfx = mconcat [ "Checking original block at "
                      , PP.viaShow origAddr
                      , " against patched block at "
                      , PP.viaShow patchedAddr
                      , " "
                      , PP.parens (PP.viaShow duration)
                      ]
      in case res of
        PE.Equivalent ->
          let okStyle = PPRT.color PPRT.Green <> PPRT.bold
          in layout (pfx <> " " <> PP.brackets (PP.annotate okStyle "✓"))
        PE.Inconclusive ->
          let qStyle = PPRT.color PPRT.Magenta <> PPRT.bold
          in layout (pfx <> " " <> PP.brackets (PP.annotate qStyle "?"))
        PE.Inequivalent _mdl ->
          let failStyle = PPRT.color PPRT.Red <> PPRT.bold
          in layout (pfx <> " " <> PP.brackets (PP.annotate failStyle "✗"))
    -- FIXME: handle other events
    _ -> layout "Unsupported event."

data LoadError where
  ElfHeaderParseError :: FilePath -> DB.ByteOffset -> String -> LoadError
  ElfArchitectureMismatch :: [DEE.ElfParseError] -> DEE.ElfMachine -> DEE.ElfMachine -> LoadError
  UnsupportedArchitecture :: DEE.ElfMachine -> LoadError

deriving instance Show LoadError

-- | Examine the input files to determine the architecture
archToProxy :: FilePath -> FilePath -> IO (Either LoadError ([DEE.ElfParseError], Some PL.ValidArchProxy))
archToProxy origBinaryPath patchedBinaryPath = do
  origBin <- BS.readFile origBinaryPath
  patchedBin <- BS.readFile patchedBinaryPath
  case (DEE.parseElf origBin, DEE.parseElf patchedBin) of
    (DEE.ElfHeaderError off msg, _) -> return (Left (ElfHeaderParseError origBinaryPath off msg))
    (_, DEE.ElfHeaderError off msg) -> return (Left (ElfHeaderParseError patchedBinaryPath off msg))
    (DEE.Elf32Res errs32 e32, DEE.Elf64Res errs64 e64) ->
      return (Left (ElfArchitectureMismatch (errs32 ++ errs64) (DEE.elfMachine e32) (DEE.elfMachine e64)))
    (DEE.Elf64Res errs64 e64, DEE.Elf32Res errs32 e32) ->
      return (Left (ElfArchitectureMismatch (errs64 ++ errs32) (DEE.elfMachine e64) (DEE.elfMachine e32)))
    (DEE.Elf32Res origErrs (DEE.elfMachine -> origMachine), DEE.Elf32Res patchedErrs (DEE.elfMachine -> patchedMachine))
      | origMachine == patchedMachine ->
        return (fmap (origErrs ++ patchedErrs,) (machineToProxy origMachine))
      | otherwise ->
        return (Left (ElfArchitectureMismatch (origErrs ++ patchedErrs) origMachine patchedMachine))
    (DEE.Elf64Res origErrs (DEE.elfMachine -> origMachine), DEE.Elf64Res patchedErrs (DEE.elfMachine -> patchedMachine))
      | origMachine == patchedMachine ->
        return (fmap (origErrs ++ patchedErrs,) (machineToProxy origMachine))
      | otherwise ->
        return (Left (ElfArchitectureMismatch (origErrs ++ patchedErrs) origMachine patchedMachine))

machineToProxy :: DEE.ElfMachine -> Either LoadError (Some PL.ValidArchProxy)
machineToProxy em =
  case em of
    DEE.EM_PPC -> Right (Some (PL.ValidArchProxy @PPC.PPC32))
    DEE.EM_PPC64 -> Right (Some (PL.ValidArchProxy @PPC.PPC64))
    DEE.EM_ARM -> Right (Some (PL.ValidArchProxy @AArch32.AArch32))
    _ -> Left (UnsupportedArchitecture em)


logParser :: OA.Parser LogTarget
logParser = interactiveParser <|> logFileParser <|> nullLoggerParser <|> pure StdoutLogger
  where
    interactiveParser = Interactive <$  OA.flag' ()
                                     (  OA.long "interactive"
                                     <> OA.short 'i'
                                     <> OA.help "Start a web server providing an interactive view of results"
                                     )
                                    <*> OA.optional parseSourceFiles
    parseSourceFiles = IS.SourcePair <$> OA.strOption (  OA.long "original-source"
                                                      <> OA.metavar "FILE"
                                                      <> OA.help "The source file for the original program"
                                                      )
                                     <*> OA.strOption ( OA.long "patched-source"
                                                      <> OA.metavar "FILE"
                                                      <> OA.help "The source file for the patched program"
                                                      )
    nullLoggerParser = OA.flag' NullLogger
                    (  OA.long "discard-logs"
                    <> OA.help "Discard all logging information"
                    )
    logFileParser = LogFile <$> OA.strOption
                             (  OA.long "log-file"
                             <> OA.metavar "FILE"
                             <> OA.help "Record logs in the given file"
                             )

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
      )))
    <*> logParser
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
