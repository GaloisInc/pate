{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
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
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as DLN
import           Data.Maybe ( maybeToList )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Traversable as T
import qualified Language.C as LC
import qualified Lumberjack as LJ
import           Numeric ( showHex )
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PPRT
import qualified System.Exit as SE
import qualified System.IO as IO
import qualified What4.Interface as WI

import qualified Data.ElfEdit as DEE
import qualified Data.ElfEdit.Prim as EEP
import qualified Data.Macaw.CFG as MC
import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.Some ( Some(..) )
import qualified SemMC.Architecture.AArch32 as SA

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery.PLT as PLT
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Hints.CSV as PHC
import qualified Pate.Hints.DWARF as PHD
import qualified Pate.Hints.JSON as PHJ
import qualified Pate.Loader as PL
import qualified Pate.PatchPair as PPa
import qualified Pate.Solver as PS
import qualified Pate.Timeout as PTi
import qualified Pate.Verbosity as PV

import qualified Pate.AArch32 as AArch32
import qualified Pate.PPC as PPC

import qualified JSONReport as JR
import qualified Pate.Interactive as I
import qualified Pate.Interactive.Port as PIP
import qualified Pate.Interactive.State as IS

-- | Post-process parsed command line options and normalize them as-needed
--
-- As a concrete example, this looks at the interactive mode trace file and
-- switches the verbosity to Debug (no matter what the user specified, as the
-- trace file specification takes precedence)
validateOptions :: CLIOptions -> CLIOptions
validateOptions = normalizeVerbosity
  where
    normalizeVerbosity o =
      case logTarget o of
        Interactive _port _srcs (Just _) -> o { verbosity = PV.Debug }
        _ -> o


parseHints
  :: LJ.LogAction IO (PE.Event arch)
  -> CLIOptions
  -> IO (PH.VerificationHints, PH.VerificationHints)
parseHints logAction opts = do
  oHints <- parseOne (originalBinary opts) (originalAnvillHints opts) (originalProbabilisticHints opts) (originalCsvFunctionHints opts) (dwarfHints opts)
  pHints <- parseOne (patchedBinary opts) (patchedAnvillHints opts) (patchedProbabilisticHints opts) (patchedCsvFunctionHints opts) (dwarfHints opts)
  return (oHints, pHints)
  where
    parseOne binPath anvillDir mprobFile mcsvFile useDwarf = do
      anvills <- T.forM anvillDir $ \anvillFile -> do
        bytes <- BSL.readFile anvillFile
        let (hints, errs) = PHJ.parseAnvillSpecHints bytes
        case errs of
          e1 : es -> LJ.writeLog logAction (PE.HintErrorsJSON (e1 DLN.:| es))
          _ -> return ()
        return hints

      probs <- T.forM (maybeToList mprobFile) $ \probFile -> do
        bytes <- BSL.readFile probFile
        let (hints, errs) = PHJ.parseProbabilisticHints bytes
        case errs of
          e1 : es -> LJ.writeLog logAction (PE.HintErrorsJSON (e1 DLN.:| es))
          _ -> return ()
        return hints

      csvs <- T.forM (maybeToList mcsvFile) $ \csvFile -> do
        bytes <- BSL.readFile csvFile
        let (hints, errs) = PHC.parseFunctionHints bytes
        case errs of
          e1 : es -> LJ.writeLog logAction (PE.HintErrorsCSV (e1 DLN.:| es))
          _ -> return ()
        return hints

      let dwarfSource = if useDwarf then [binPath] else []
      dwarves <- T.forM dwarfSource $ \elfFile -> do
        bytes <- BSL.readFile elfFile
        let (hints, errs) = PHD.parseDWARFHints bytes
        case errs of
          e1 : es -> LJ.writeLog logAction (PE.HintErrorsDWARF (e1 DLN.:| es))
          _ -> return ()
        return hints

      return (mconcat (concat [anvills, probs, csvs, dwarves]))

main :: IO ()
main = do
  opts <- validateOptions <$> OA.execParser cliOptions
  ep <- archToProxy (originalBinary opts) (patchedBinary opts)
  case ep of
    Left err -> SE.die (show err)
    Right (elfErrs, Some proxy) -> do
      proofConsumer <- T.traverse JR.consumeProofEvents (proofSummaryJSON opts)
      chan <- CC.newChan
      (logger, mConsumer) <- startLogger proxy (verbosity opts) (logTarget opts) chan proofConsumer
      (origHints, patchedHints) <- parseHints logger opts
      LJ.writeLog logger (PE.ElfLoaderWarnings elfErrs)
      let
        infoPath = case blockInfo opts of
          Just path -> Left path
          Nothing -> Right PC.noPatchData
        verificationCfg =
          PC.defaultVerificationCfg
            { PC.cfgPairMain = not $ noPairMain opts
            , PC.cfgDiscoverFuns = not $ noDiscoverFuns opts
            , PC.cfgComputeEquivalenceFrames = not $ trySimpleFrames opts
            , PC.cfgEmitProofs = not $ noProofs opts
            , PC.cfgSolver = solver opts
            , PC.cfgHeuristicTimeout = heuristicTimeout opts
            , PC.cfgGoalTimeout = goalTimeout opts
            , PC.cfgMacawDir = saveMacawCFGs opts
            , PC.cfgSolverInteractionFile = solverInteractionFile opts
            }
        cfg = PC.RunConfig
            { PC.archProxy = proxy
            , PC.infoPath = infoPath
            , PC.origPath = originalBinary opts
            , PC.patchedPath = patchedBinary opts
            , PC.logger = logger
            , PC.verificationCfg = verificationCfg
            , PC.origHints = origHints
            , PC.patchedHints = patchedHints
            }


      status <- PL.runEquivConfig cfg


      -- Shut down the logger cleanly (if we can - the interactive logger will be
      -- persistent until the user kills it)
      CC.writeChan chan Nothing
      F.forM_ mConsumer CCA.wait
      _ <- T.traverse JR.waitForConsumer proofConsumer

      case status of
        PEq.Errored err -> SE.die (show err)
        _ -> pure ()


data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  , blockInfo :: Maybe FilePath
  , logTarget :: LogTarget
  , noPairMain :: Bool
  , noDiscoverFuns :: Bool
  , noProofs :: Bool
  , trySimpleFrames :: Bool
  , solver :: PS.Solver
  , goalTimeout :: PTi.Timeout
  , heuristicTimeout :: PTi.Timeout
  , originalAnvillHints :: [FilePath]
  , patchedAnvillHints :: [FilePath]
  , originalProbabilisticHints :: Maybe FilePath
  , patchedProbabilisticHints :: Maybe FilePath
  , originalCsvFunctionHints :: Maybe FilePath
  , patchedCsvFunctionHints :: Maybe FilePath
  , dwarfHints :: Bool
  , verbosity :: PV.Verbosity
  , saveMacawCFGs :: Maybe FilePath
  , solverInteractionFile :: Maybe FilePath
  , proofSummaryJSON :: Maybe FilePath
  } deriving (Eq, Ord, Show)

data LogTarget = Interactive PIP.Port (Maybe (IS.SourcePair FilePath)) (Maybe FilePath)
               -- ^ Logs will go to an interactive viewer
               --
               -- If source files (corresponding to the original and patched
               -- source) are provided, their contents are displayed when
               -- appropriate (on a per-function basis).
               --
               -- The third argument is an optional path to save trace-level
               -- messages to; note that if this is provided, it implies that
               -- the verbosity level is Debug
               | LogFile FilePath
               -- ^ Logs will go to a file (if present)
               | StdoutLogger
               -- ^ Log to stdout
               | NullLogger
               -- ^ Discard logs
               deriving (Eq, Ord, Show)

printAtVerbosity
  :: PV.Verbosity
  -> PE.Event arch
  -> Bool
printAtVerbosity verb evt =
  case verb of
    PV.Debug -> True
    PV.Info ->
      case evt of
        PE.ProofTraceEvent {} -> False
        PE.ProofTraceFormulaEvent {} -> False
        _ -> True

-- | Create a logger based on the user's desire for an interactive session.
--
-- If the user requests an interactive session, this function will set up a web
-- server to stream logging events from the verifier, which the user can connect
-- to.
--
-- Otherwise, just make a basic logger that will write logs to a user-specified
-- location
startLogger :: PA.SomeValidArch arch
            -> PV.Verbosity
            -> LogTarget
            -> CC.Chan (Maybe (PE.Event arch))
            -> Maybe (JR.ProofEventConsumer arch)
            -> IO (LJ.LogAction IO (PE.Event arch), Maybe (CCA.Async ()))
startLogger (PA.SomeValidArch {}) verb lt chan proofConsumer =
  case lt of
    NullLogger -> return (LJ.LogAction $ \_ -> return (), Nothing)
    StdoutLogger -> logToHandle IO.stdout
    LogFile fp -> do
      hdl <- IO.openFile fp IO.WriteMode
      IO.hSetBuffering hdl IO.LineBuffering
      logToHandle hdl
    Interactive port mSourceFiles mTraceFile -> do
      mTraceHandle <- T.traverse (\fp -> IO.openFile fp IO.WriteMode) mTraceFile
      F.forM_ mTraceHandle $ \hdl -> do
        IO.hSetBuffering hdl IO.NoBuffering
      -- This odd structure makes all of the threading explicit at this top
      -- level so that there is no thread creation hidden in the Interactive
      -- module
      --
      -- The data producer/manager and the UI communicate via an IORef, which
      -- contains the up-to-date version of the state
      consumer <- CCA.async $ do
        mSourceContent <- join <$> T.traverse parseSources mSourceFiles
        stateRef <- I.newState mSourceContent
        watcher <- CCA.async $ I.consumeEvents chan stateRef verb mTraceHandle
        ui <- CCA.async $ I.startInterface port stateRef
        CCA.wait watcher
        CCA.wait ui
      return (logAct, Just consumer)
  where
    logAct = LJ.LogAction $ \evt -> CC.writeChan chan (Just evt)
    logToHandle hdl = do
      let consumeLogs = do
            me <- CC.readChan chan
            case me of
              Nothing -> do
                -- Shut down the proof summary process once we are out of events
                _ <- T.traverse (\pc -> JR.sendEvent pc Nothing) proofConsumer
                return ()
              Just evt -> do
                case (proofConsumer, evt) of
                  (Just pc, PE.ProofIntermediate bp sp _) -> JR.sendEvent pc (Just (JR.SomeProofEvent bp sp))
                  _ -> return ()
                if | printAtVerbosity verb evt -> do
                       PPRT.renderIO hdl (terminalFormatEvent evt)
                       consumeLogs
                   | otherwise -> consumeLogs

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

layoutLn :: PP.Doc ann -> PP.SimpleDocStream ann
layoutLn doc = layout (doc <> PP.line)

ppHex :: (Integral a, Show a) => a -> PP.Doc ann
ppHex i = PP.pretty (showHex i "")

terminalFormatEvent :: (MC.MemWidth (MC.ArchAddrWidth arch)) => PE.Event arch -> PP.SimpleDocStream PPRT.AnsiStyle
terminalFormatEvent evt =
  case evt of
    PE.LoadedBinaries {} -> layoutLn "Loaded original and patched binaries"
    PE.ElfLoaderWarnings pes ->
      let msg = "Warnings during ELF loading:"
      in layout $ PP.vsep (msg : [ "  " <> PP.viaShow err | err <- pes ]) <> PP.line
    PE.AnalysisStart (PPa.PatchPair blkO blkP) ->
      layout $ mconcat [ "Checking original block at "
                       , PP.viaShow $ PB.concreteAddress blkO
                       , " against patched block at "
                       , PP.viaShow $ PB.concreteAddress blkP
                       , PP.line
                       ]
    PE.CheckedEquivalence (PPa.PatchPair (PE.Blocks _ blkO _) (PE.Blocks _ blkP _)) res duration ->
      let
        origAddr = PB.concreteAddress blkO
        patchedAddr = PB.concreteAddress blkP
        pfx = mconcat [ "Checked original block at "
                      , PP.viaShow origAddr
                      , " against patched block at "
                      , PP.viaShow patchedAddr
                      , " "
                      , PP.parens (PP.viaShow duration)
                      ]
      in case res of
        PE.Equivalent ->
          let okStyle = PPRT.color PPRT.Green <> PPRT.bold
          in layoutLn (pfx <> " " <> PP.brackets (PP.annotate okStyle "✓"))
        PE.Inconclusive ->
          let qStyle = PPRT.color PPRT.Magenta <> PPRT.bold
          in layoutLn (pfx <> " " <> PP.brackets (PP.annotate qStyle "?"))
        PE.Inequivalent _mdl ->
          let failStyle = PPRT.color PPRT.Red <> PPRT.bold
          in layoutLn (pfx <> " " <> PP.brackets (PP.annotate failStyle "✗"))
    PE.ErrorRaised err -> layoutLn (PP.viaShow err)
    PE.ProvenGoal _ prf _ -> layoutLn (PP.viaShow prf)
    PE.HintErrorsCSV errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.HintErrorsJSON errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.HintErrorsDWARF errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.FunctionEntryInvalidHints _ errs ->
      layout ("Invalid function entry hints:" <> PP.line
               <> PP.vsep [ PP.pretty fn <> "@" <> ppHex addr
                          | (fn, addr) <- errs
                          ]
             <> PP.line)
    PE.FunctionsDiscoveredFromHints _ extraAddrs ->
      layout ("Additional functions discovered based on hits: " <> PP.line
             <> PP.vcat (map PP.viaShow extraAddrs) <> PP.line)
    PE.ProofTraceEvent _stack origAddr _patchedAddr msg _tm ->
      layout (PP.pretty origAddr <> ": " <> PP.pretty msg <> PP.line)
    PE.ProofTraceFormulaEvent _stk origAddr _patchedAddr _sym expr _tm ->
      layout (PP.pretty origAddr <> ": " <> WI.printSymExpr expr <> PP.line)
    -- FIXME: handle other events
    _ -> layout ""

data LoadError where
  ElfHeaderParseError :: FilePath -> DB.ByteOffset -> String -> LoadError
  ElfArchitectureMismatch :: FilePath -> FilePath -> LoadError
  UnsupportedArchitecture :: DEE.ElfMachine -> LoadError

deriving instance Show LoadError

-- | Examine the input files to determine the architecture
archToProxy :: FilePath -> FilePath -> IO (Either LoadError ([DEE.ElfParseError], Some PA.SomeValidArch))
archToProxy origBinaryPath patchedBinaryPath = do
  origBin <- BS.readFile origBinaryPath
  patchedBin <- BS.readFile patchedBinaryPath
  case (EEP.decodeElfHeaderInfo origBin, EEP.decodeElfHeaderInfo patchedBin) of
    (Right (EEP.SomeElf origHdr), Right (EEP.SomeElf patchedHdr))
      | Just PC.Refl <- PC.testEquality (DEE.headerClass (DEE.header origHdr)) (DEE.headerClass (DEE.header patchedHdr))
      , DEE.headerMachine (DEE.header origHdr) == DEE.headerMachine (DEE.header patchedHdr) ->
        let (origParseErrors, _origElf) = DEE.getElf origHdr
            (patchedParseErrors, _patchedElf) = DEE.getElf patchedHdr
            origMachine = DEE.headerMachine (DEE.header origHdr)
        in return (fmap (origParseErrors ++ patchedParseErrors,) (machineToProxy origMachine origHdr patchedHdr))
    (Left (off, msg), _) -> return (Left (ElfHeaderParseError origBinaryPath off msg))
    (_, Left (off, msg)) -> return (Left (ElfHeaderParseError patchedBinaryPath off msg))
    _ -> return (Left (ElfArchitectureMismatch origBinaryPath patchedBinaryPath))

-- | Create a 'PA.SomeValidArch' from parsed ELF files
--
-- Note that we do additional ELF parsing here so that we do not have to
-- propagate ELF-specific constraints throughout the analysis.  This includes
-- finding additional (dynamic) symbols from ELF files, which requires deep
-- ELF-specific inspection.
machineToProxy
  :: DEE.ElfMachine
  -> EEP.ElfHeaderInfo w
  -> EEP.ElfHeaderInfo w
  -> Either LoadError (Some PA.SomeValidArch)
machineToProxy em origHdr patchedHdr =
  case (em, EEP.headerClass (EEP.header origHdr)) of
    (DEE.EM_PPC, _) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = PPC.handleSystemCall
                                 , PA.validArchFunctionDomain = PPC.handleExternalCall
                                 , PA.validArchDedicatedRegisters = PPC.ppc32HasDedicatedRegister
                                 , PA.validArchArgumentMapping = PPC.argumentMapping
                                 , PA.validArchOrigExtraSymbols = mempty
                                 , PA.validArchPatchedExtraSymbols = mempty
                                 }
      in Right (Some (PA.SomeValidArch vad))
    (DEE.EM_PPC64, _) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = PPC.handleSystemCall
                                 , PA.validArchFunctionDomain = PPC.handleExternalCall
                                 , PA.validArchDedicatedRegisters = PPC.ppc64HasDedicatedRegister
                                 , PA.validArchArgumentMapping = PPC.argumentMapping
                                 , PA.validArchOrigExtraSymbols = mempty
                                 , PA.validArchPatchedExtraSymbols = mempty
                                 }
      in Right (Some (PA.SomeValidArch vad))
    (DEE.EM_ARM, EEP.ELFCLASS32) ->
      let vad = PA.ValidArchData { PA.validArchSyscallDomain = AArch32.handleSystemCall
                                 , PA.validArchFunctionDomain = AArch32.handleExternalCall
                                 , PA.validArchDedicatedRegisters = AArch32.hasDedicatedRegister
                                 , PA.validArchArgumentMapping = AArch32.argumentMapping
                                 , PA.validArchOrigExtraSymbols =
                                     PLT.pltStubSymbols (Proxy @SA.AArch32) (Proxy @EEP.ARM32_RelocationType) origHdr
                                 , PA.validArchPatchedExtraSymbols =
                                     PLT.pltStubSymbols (Proxy @SA.AArch32) (Proxy @EEP.ARM32_RelocationType) patchedHdr
                                 }
      in Right (Some (PA.SomeValidArch vad))
    _ -> Left (UnsupportedArchitecture em)


logParser :: OA.Parser LogTarget
logParser = interactiveParser <|> logFileParser <|> nullLoggerParser <|> pure StdoutLogger
  where
    interactiveParser = Interactive <$  OA.flag' ()
                                     (  OA.long "interactive"
                                     <> OA.short 'i'
                                     <> OA.help "Start a web server providing an interactive view of results"
                                     )
                                    <*> OA.option (OA.maybeReader PIP.portMaybe)
                                         ( OA.long "port"
                                         <> OA.short 'p'
                                         <> OA.metavar "PORT"
                                         <> OA.value (PIP.port 5000)
                                         <> OA.showDefault
                                         <> OA.help "The port to run the interactive visualizer on"
                                         )
                                    <*> OA.optional parseSourceFiles
                                    <*> OA.optional (OA.strOption ( OA.long "trace-file"
                                                     <> OA.metavar "FILE"
                                                     <> OA.help "A file to save trace-level messages to (note: this implies trace-level debugging)"
                                                     ))
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
    <*> (OA.switch
      (  OA.long "noproofs"
      <> OA.help "Don't print structured proofs after checking."
      ))
    <*> (OA.switch
      (  OA.long "try-simple-frames"
      <> OA.help "Attempt simple frame propagation first, falling back to heuristic analysis upon failure."
      ))
    <*> OA.option OA.auto (OA.long "solver"
                    <> OA.help "The SMT solver to use to solve verification conditions. One of CVC4, Yices, or Z3"
                    <> OA.value PS.Yices
                    <> OA.showDefault
                  )
    <*> (PTi.Seconds <$> (OA.option OA.auto (OA.long "goal-timeout"
                                    <> OA.value 300
                                    <> OA.showDefault
                                    <> OA.help "The timeout for verifying individual goals in seconds"
                                    )))
    <*> (PTi.Seconds <$> (OA.option OA.auto (OA.long "heuristic-timeout"
                                    <> OA.value 10
                                    <> OA.showDefault
                                    <> OA.help "The timeout for verifying heuristic goals in seconds"
                                    )))
    <*> OA.many (OA.strOption
        ( OA.long "original-anvill-hints"
        <> OA.help "Parse an Anvill specification for code discovery hints"
        ))
    <*> OA.many (OA.strOption
        ( OA.long "patched-anvill-hints"
        <> OA.help "Parse an Anvill specification for code discovery hints"
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "original-probabilistic-hints"
        <> OA.help "Parse a JSON file containing probabilistic function name/address hints"
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "patched-probabilistic-hints"
        <> OA.help "Parse a JSON file containing probabilistic function name/address hints"
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "original-csv-function-hints"
         <> OA.help "Parse a CSV file containing function name/address hints"
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "patched-csv-function-hints"
         <> OA.help "Parse a CSV file containing function name/address hints"
        ))
    <*> OA.switch ( OA.long "dwarf-hints"
                  <> OA.help "Extract hints from the unpatched DWARF binary"
                  )
    <*> OA.option OA.auto ( OA.long "verbosity"
                          <> OA.short 'V'
                          <> OA.showDefault
                          <> OA.value PV.Info
                          <> OA.help "The verbosity of logging output"
                          )
    <*> OA.optional (OA.strOption
         ( OA.long "save-macaw-cfgs"
         <> OA.metavar "DIR"
         <> OA.help "Save macaw CFGs to the provided directory"
         ))
    <*> OA.optional (OA.strOption
         ( OA.long "solver-interaction-file"
         <> OA.metavar "FILE"
         <> OA.help "Save interactions with the SMT solver during symbolic execution to this file"
         ))
    <*> OA.optional (OA.strOption
        ( OA.long "proof-summary-json"
        <> OA.metavar "FILE"
        <> OA.help "A file to save interesting proof results to in JSON format"
        ))
