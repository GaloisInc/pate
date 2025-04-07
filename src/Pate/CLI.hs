{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Pate.CLI
    ( CLIOptions(..)
    , cliOptions
    , mkRunConfig
    ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Data.Foldable as F
import qualified Lumberjack as LJ
import           Numeric ( showHex )
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PPRT
import qualified Prettyprinter.Render.Text as PPText
import qualified System.Console.ANSI as SCA
import qualified System.IO as IO
import qualified What4.Interface as WI

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFGSlice as MCS

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Loader as PL
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.PatchPair as PPa
import qualified Pate.Solver as PS
import qualified Pate.Script as PSc
import qualified Pate.Timeout as PTi
import qualified Pate.Verbosity as PV
import qualified Pate.Verification.StrongestPosts.CounterExample as PVSC

import           Pate.TraceTree
import Data.Maybe (fromMaybe)

mkRunConfig :: PA.ArchLoader PEE.LoadError -> CLIOptions -> PSc.ScriptRunConfig -> Maybe (SomeTraceTree PA.ValidRepr) -> IO (Either String PL.RunConfig)
mkRunConfig archLoader opts rcfg mtt = let
    origPaths = PLE.LoadPaths
      { PLE.binPath = originalBinary opts
      , PLE.anvillHintsPaths = originalAnvillHints opts
      , PLE.mprobHintsPath = originalProbabilisticHints opts
      , PLE.mcsvHintsPath = originalCsvFunctionHints opts
      , PLE.mbsiHintsPath = originalBSIFunctionHints opts
      }
    patchedPaths = PLE.LoadPaths
      { PLE.binPath = patchedBinary opts
      , PLE.anvillHintsPaths = patchedAnvillHints opts
      , PLE.mprobHintsPath = patchedProbabilisticHints opts
      , PLE.mcsvHintsPath = patchedCsvFunctionHints opts
      , PLE.mbsiHintsPath = patchedBSIFunctionHints opts
      }

    mklogger :: forall arch. PA.SomeValidArch arch -> IO (PL.Logger arch)
    mklogger proxy = do
      (logger, consumers) <- startLogger proxy (verbosity opts) (logFile opts)
      return $ PL.Logger logger consumers

    verificationCfg =
      PC.defaultVerificationCfg
        { PC.cfgStartSymbols = startSymbols opts
        , PC.cfgDiscoverFuns = not $ noDiscoverFuns opts
        , PC.cfgSolver = solver opts
        , PC.cfgHeuristicTimeout = heuristicTimeout opts
        , PC.cfgGoalTimeout = goalTimeout opts
        , PC.cfgMacawDir = saveMacawCFGs opts
        , PC.cfgSolverInteractionFile = solverInteractionFile opts
        , PC.cfgFailureMode = errMode opts
        , PC.cfgIgnoreUnnamedFunctions = skipUnnamedFns opts
        , PC.cfgIgnoreDivergedControlFlow = skipDivergedControl opts
        , PC.cfgTargetEquivRegs = targetEquivRegs opts
        , PC.cfgRescopingFailureMode = rerrMode opts
        , PC.cfgScriptPath = scriptPath opts
        , PC.cfgTraceTree = fromMaybe noTraceTree mtt
        , PC.cfgStackScopeAssume = assumeStackScope opts
        , PC.cfgIgnoreWarnings = ignoreWarnings opts
        , PC.cfgAlwaysClassifyReturn = alwaysClassifyReturn opts
        , PC.cfgTraceConstraints = traceConstraints opts
        , PC.cfgQuickStart = quickStart opts
        }
    cfg = PL.RunConfig
        { PL.archLoader = archLoader
        , PL.patchInfoPath = blockInfo opts
        , PL.patchData = mempty
        , PL.origPaths = origPaths
        , PL.patchedPaths = patchedPaths
        , PL.logger = mklogger
        , PL.verificationCfg = verificationCfg
        , PL.useDwarfHints = not $ noDwarfHints opts
        , PL.elfLoaderConfig = PLE.defaultElfLoaderConfig { PLE.ignoreSegments = ignoreSegments opts }
        , PL.scriptConfig = rcfg
        }
  in PL.parseAndAttachScript cfg

data CLIOptions = CLIOptions
  { originalBinary :: FilePath
  , patchedBinary :: FilePath
  , blockInfo :: Maybe FilePath
  -- , interactiveConfig :: Maybe InteractiveConfig
  , startSymbols :: [String]
  , noDiscoverFuns :: Bool
  , solver :: PS.Solver
  , goalTimeout :: PTi.Timeout
  , heuristicTimeout :: PTi.Timeout
  , originalAnvillHints :: [FilePath]
  , patchedAnvillHints :: [FilePath]
  , originalProbabilisticHints :: Maybe FilePath
  , patchedProbabilisticHints :: Maybe FilePath
  , originalCsvFunctionHints :: Maybe FilePath
  , patchedCsvFunctionHints :: Maybe FilePath
  , originalBSIFunctionHints :: Maybe FilePath
  , patchedBSIFunctionHints :: Maybe FilePath
  , noDwarfHints :: Bool
  , verbosity :: PV.Verbosity
  , saveMacawCFGs :: Maybe FilePath
  , solverInteractionFile :: Maybe FilePath
  , proofSummaryJSON :: Maybe FilePath
  , logFile :: Maybe FilePath
  -- ^ The path to store trace information to (logs will be discarded if not provided)
  , errMode :: PC.VerificationFailureMode
  , rerrMode :: PC.RescopingFailureMode
  , skipUnnamedFns :: Bool
  , skipDivergedControl :: Bool
  , targetEquivRegs :: [String]
  , ignoreSegments :: [Int]
  , jsonToplevel :: Bool
  , readOnlySegments :: [Int]
  , scriptPath :: Maybe FilePath
  , assumeStackScope :: Bool
  , ignoreWarnings :: [String]
  , alwaysClassifyReturn :: Bool
  , preferTextInput :: Bool
  , traceConstraints :: Bool
  , quickStart :: Bool
  } deriving (Eq, Ord, Show)

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
--
-- The 'LJ.LogAction' returned is the logger to be used in the entire
-- application. It will forward messages to consumers as appropriate. Each
-- consumer is an action to call after shutting down the 'CCA.Async', which is
-- paired up with an associated action that should be run to shut down the async
-- cleanly.
startLogger :: PA.SomeValidArch arch
            -> PV.Verbosity
            -- -> Maybe InteractiveConfig
            -> Maybe FilePath
            -> IO (LJ.LogAction IO (PE.Event arch), [(IO (), IO ())])
startLogger (PA.SomeValidArch {}) verb {- mIntConf -} mLogFile = do
  (fileLogger, loggerAsync) <- case mLogFile of
        Nothing -> return (LJ.LogAction $ \_ -> return (), [])
        Just fp -> do
          hdl <- IO.openFile fp IO.WriteMode
          IO.hSetBuffering hdl IO.LineBuffering
          IO.hSetEncoding hdl IO.utf8
          logToHandle hdl
  return (fileLogger, loggerAsync)
  where
    logToHandle hdl = do
      chan <- CC.newChan
      isTerm <- SCA.hSupportsANSIColor hdl
      let consumeLogs = do
            me <- CC.readChan chan
            case me of
              Nothing -> return ()
              Just evt ->
                if | printAtVerbosity verb evt -> do
                       if isTerm
                         then PPRT.renderIO hdl (terminalFormatEvent evt)
                         else PPText.renderIO hdl (PP.unAnnotateS (terminalFormatEvent evt))
                       consumeLogs
                   | otherwise -> consumeLogs

      consumer <- CCA.async consumeLogs
      let logAct = LJ.LogAction $ \evt -> CC.writeChan chan (Just evt)
      let shutdown = CC.writeChan chan Nothing
      return (logAct, [(CCA.wait consumer, shutdown)])


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
    PE.ErrorRaised err -> layoutLn ("ERROR:" <> PP.pretty err)
    PE.Warning err -> layoutLn ("WARNING:" <> PP.pretty err)
    PE.HintErrorsCSV errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.HintErrorsJSON errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.HintErrorsDWARF errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.HintErrorsBSI errs -> layoutLn (PP.vsep (map PP.viaShow (F.toList errs)))
    PE.FunctionEntryInvalidHints _ errs ->
      layout ("Invalid function entry hints:" <> PP.line
               <> PP.vsep [ PP.pretty fn <> "@" <> ppHex addr
                          | (fn, addr) <- errs
                          ]
             <> PP.line)
    PE.FunctionsDiscoveredFromHints _ extraAddrs ->
      layout ("Additional functions discovered based on hits: " <> PP.line
             <> PP.vcat (map PP.viaShow extraAddrs) <> PP.line)
    PE.ProofTraceEvent _stack addrPair msg _tm ->
      layout (PPa.ppPatchPairC PP.pretty addrPair <> ": " <> PP.pretty msg <> PP.line)
    PE.ProofTraceFormulaEvent _stk origAddr _patchedAddr _sym expr _tm ->
      layout (PP.pretty origAddr <> ": " <> WI.printSymExpr expr <> PP.line)
    PE.StrongestPostOverallResult status _ ->
      layoutLn ("Overall strongest postcondition verification result: " <> PP.viaShow status)
    PE.GasExhausted pPair ->
      layoutLn (PP.pretty pPair PP.<+> "analysis failed to converge (i.e., ran out of gas)")
    PE.StrongestPostMiscError pPair msg ->
      layoutLn ("Error at " <> PP.pretty pPair <> ":" PP.<+> PP.pretty msg)
    PE.StrongestPostObservable pPair (PVSC.ObservableCounterexample _ oEvs pEvs) ->
      layout ( PP.vcat (concat [ [ PP.pretty pPair PP.<+> "observable sequences disagree"
                                 , "Original sequence:"
                                 ]
                               , [ PP.indent 2 (PMT.prettyMemEvent ev) | ev <- oEvs ]
                               , [ "Patched sequence:" ]
                               , [ PP.indent 2 (PMT.prettyMemEvent ev) | ev <- pEvs ]
                               ]
                       ) <> PP.line)
    PE.StrongestPostDesync pPair (PVSC.TotalityCounterexample (oIP, oEnd, oInstr) (pIP, pEnd, pInstr)) ->
      layout ( PP.vcat [ PP.pretty pPair PP.<+> "program control flow desynchronized"
                       , "  Original: 0x" <> PP.pretty (showHex oIP "") PP.<+> PP.pretty (MCS.ppExitCase oEnd) PP.<+> PP.viaShow oInstr
                       , "  Patched : 0x" <> PP.pretty (showHex pIP "") PP.<+> PP.pretty (MCS.ppExitCase pEnd) PP.<+> PP.viaShow pInstr
                       ] <> PP.line)
    -- FIXME: handle other events
    _ -> layout ""


modeParser :: OA.Parser PC.VerificationFailureMode
modeParser = OA.option OA.auto (OA.long "errormode"
                                <> OA.help "Verifier error handling mode"
                                <> OA.short 'e'
                                <> OA.value PC.ThrowOnAnyFailure
                                <> OA.showDefault)

rescopeModeParser :: OA.Parser PC.RescopingFailureMode
rescopeModeParser = OA.option OA.auto (OA.long "rescopemode"
                                <> OA.help "Variable rescoping failure handling mode"
                                <> OA.short 'r'
                                <> OA.value PC.ThrowOnEqRescopeFailure
                                <> OA.showDefault)

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
    -- <*> logParser
    <*> (OA.many (OA.strOption
      (  OA.long "startsymbol"
      <> OA.short 's'
      <> OA.help "Start analysis from the function with this symbol"
      )))
    <*> (OA.switch
      (  OA.long "nodiscovery"
      <> OA.short 'd'
      <> OA.help "Don't dynamically discover function pairs based on calls."
      <> OA.internal -- DEPRECATED
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
    <*> OA.optional (OA.strOption
        ( OA.long "original-bsi-hints"
         <> OA.help "Parse a JSON file containing function name/address hints"
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "patched-bsi-hints"
         <> OA.help "Parse a JSON file containing function name/address hints"
        ))
    <*> OA.switch ( OA.long "no-dwarf-hints"
                  <> OA.help "Do not extract metadata from the DWARF information in the binaries"
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
        <> OA.internal -- DEPRECATED
        ))
    <*> OA.optional (OA.strOption
        ( OA.long "log-file"
        <> OA.metavar "FILE"
        <> OA.help "A file to save debug logs to"
        ))
   <*> modeParser
   <*> rescopeModeParser
   <*> OA.switch
       (  OA.long "skip-unnamed-functions"
       <> OA.help "Skip analysis of functions without symbols"
       )
   <*> OA.switch
       (  OA.long "skip-divergent-control-flow"
       <> OA.help "<DEPRECATED>"
       <> OA.internal -- DEPRECATED
       )
    <*> OA.many (OA.strOption
        ( OA.long "target-equiv-regs"
        <> OA.help "Compute an equivalence condition sufficient to establish equality on the given registers after the toplevel entrypoint returns. <DEPRECATED>"
        <> OA.internal -- DEPRECATED
        ))
    <*> OA.many (OA.option OA.auto
        ( OA.long "ignore-segments"
        <> OA.help "Skip segments (0-indexed) when loading ELF"
        ))
   <*> OA.switch
       (  OA.long "json-toplevel"
       <> OA.help "Run toplevel in JSON-output mode (interactive mode only)"
       <> OA.hidden -- only for binja plugin
       )
    <*> OA.many (OA.option OA.auto
        ( OA.long "read-only-segments"
        <> OA.help "Mark segments as read-only (0-indexed) when loading ELF"
        ))
    <*> OA.optional (OA.strOption
         ( OA.long "script"
         <> OA.metavar "FILENAME"
         <> OA.help (
                 "Path to a pate script file. Provides pre-defined input for user prompts" 
              ++ " (see tests/integration/packet-mod/packet.pate for an example and"
              ++ " src/Pate/Script.hs for details)" )
         ))
    <*> OA.switch
         ( OA.long "assume-stack-scope"
         <> OA.help "Add additional assumptions about stack frame scoping during function calls (unsafe)"
         )
    <*> OA.many (OA.strOption
        ( OA.long "ignore-warnings"
        <> OA.help "Don't raise any of the given warning types"
        ))
    <*> OA.switch
         ( OA.long "always-classify-return"
         <> OA.help "Always resolve classifier failures by assuming function returns, if possible."
         )
    <*> OA.switch
         ( OA.long "prefer-text-input"
         <> OA.help "Prefer taking text input over multiple choice menus where possible."
         <> OA.internal -- deprecated (mostly unsupported)
         )
    <*> OA.switch
         ( OA.long "add-trace-constraints"
         <> OA.help "Prompt to add additional constraints when generating traces."
         )
    <*> OA.switch
         ( OA.long "quickstart"
         <> OA.help "Start analysis immediately from the given entrypoint (provided from -s)"
         )