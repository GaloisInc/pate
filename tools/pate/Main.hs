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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Applicative ( (<|>) )
import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import           Control.Monad ( join )
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Language.C as LC
import qualified Lumberjack as LJ
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PPRT
import           System.Exit
import qualified System.IO as IO

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
  Some proxy <- return $ archKToProxy (archK opts)
  chan <- CC.newChan
  (logger, mConsumer) <- startLogger proxy (logTarget opts) chan
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
    Left err -> die (show err)
    Right _ -> pure ()

  -- Shut down the logger cleanly (if we can - the interactive logger will be
  -- persistent until the user kills it)
  CC.writeChan chan Nothing
  F.forM_ mConsumer CCA.wait

data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  , blockInfo :: Maybe FilePath
  , archK :: ArchK
  , logTarget :: LogTarget
  , noPairMain :: Bool
  , noDiscoverFuns :: Bool
  } deriving (Eq, Ord, Read, Show)

data ArchK = PPC | ARM
  deriving (Eq, Ord, Read, Show)

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
    PE.CheckedEquivalence (PE.Blocks origAddr _) (PE.Blocks patchedAddr _) res duration ->
      let pfx = mconcat [ "Checking original block at "
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

archKToProxy :: ArchK -> Some PL.ValidArchProxy
archKToProxy a = case a of
  PPC -> Some (PL.ValidArchProxy @PPC.PPC64)
  ARM -> Some (PL.ValidArchProxy @AArch32.AArch32)

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
      -- <> OA.value Nothing
      )))
    <*> (OA.option (OA.auto @ArchK)
      (  OA.long "arch"
      <> OA.short 'a'
      <> OA.metavar "ARCH"
      <> OA.help "Architecture of the given binaries"
      ))
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
