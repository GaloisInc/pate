{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Pate.Loader
  (
    runEquivVerification
  , runSelfEquivConfig
  , runEquivConfig
  , RunConfig(..)
  , Logger(..)
  )
where

import qualified Control.Monad.Except as CME
import qualified Control.Monad.Writer as CMW
import qualified Control.Monad.IO.Class as IO
import qualified Data.List.NonEmpty as DLN
import           Data.Maybe ( mapMaybe )
import qualified Data.Foldable as F

import qualified Data.ByteString as BS
import           Data.Parameterized.Some ( Some(..) )
import qualified Lumberjack as LJ


import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import           Pate.Loader.ELF ( LoaderM )
import qualified Pate.Verification as PV
import qualified Pate.Equivalence.Error as PEE

data RunConfig =
  RunConfig
    { patchInfoPath :: Maybe FilePath
    , patchData :: PC.PatchData
    , origPaths :: PLE.LoadPaths
    , patchedPaths :: PLE.LoadPaths
    , logger :: forall arch. PA.SomeValidArch arch -> IO (Logger arch)
    , verificationCfg :: PC.VerificationConfig PA.ValidRepr
    , archLoader :: PA.ArchLoader PEE.LoadError
    , useDwarfHints :: Bool
    }

data Logger arch =
  Logger
    { logAction :: LJ.LogAction IO (PE.Event arch)
    , logConsumers :: [(IO (), IO ())]
    }

runEquivVerification ::
  PA.SomeValidArch arch ->
  [PEE.LoadError] ->
  Logger arch ->
  PC.PatchData ->
  PC.VerificationConfig PA.ValidRepr ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  IO (PEq.EquivalenceStatus)
runEquivVerification validArch@(PA.SomeValidArch {}) loadErrs (Logger logAct consumers) pd dcfg original patched = do
  let elfErrs = mapMaybe (\e -> case e of PEE.ElfParseError pe -> Just pe; _ -> Nothing) loadErrs
  case elfErrs of
    (_e : _es) -> LJ.writeLog logAct (PE.ElfLoaderWarnings elfErrs)
    _ -> return ()
  let jsonErrs = mapMaybe (\e -> case e of PEE.JSONParseError _fp pe -> Just pe; _ -> Nothing) loadErrs
  case jsonErrs of
    (e : es) -> LJ.writeLog logAct (PE.HintErrorsJSON (e DLN.:| es))
    _ -> return ()
  let csvErrs = mapMaybe (\e -> case e of PEE.CSVParseError _fp pe -> Just pe; _ -> Nothing) loadErrs
  case csvErrs of
    (e : es) -> LJ.writeLog logAct (PE.HintErrorsCSV (e DLN.:| es))
    _ -> return ()
  let dwarfErrs = mapMaybe (\e -> case e of PEE.DWARFError _fp pe -> Just pe; _ -> Nothing) loadErrs
  case dwarfErrs of
    (e : es) -> LJ.writeLog logAct (PE.HintErrorsDWARF (e DLN.:| es))
    _ -> return ()
  let bsiErrs = mapMaybe (\e -> case e of PEE.BSIParseError _fp pe -> Just pe; _ -> Nothing) loadErrs
  case bsiErrs of
    (e : es) -> LJ.writeLog logAct (PE.HintErrorsBSI (e DLN.:| es))
    _ -> return ()
  st <- (CME.runExceptT $ PV.verifyPairs validArch logAct original patched dcfg pd) >>= \case
    Left err -> return $ PEq.Errored err
    Right st -> return st
  -- Shut down the logger cleanly (if we can - the interactive logger will be
  -- persistent until the user kills it)
  --
  -- Each log consumer has its own shutdown action that we have to invoke
  -- before the async action will finish; we then wait for each one to
  -- finish.
  F.forM_ consumers $ \(_wait, shutdown) -> shutdown
  F.forM_ consumers $ \(wait, _shutdown) -> wait
  return st

liftToEquivStatus ::
  LoaderM (PEq.EquivalenceStatus) ->
  IO (PEq.EquivalenceStatus)
liftToEquivStatus f = do
  v <- CME.runExceptT (CMW.runWriterT f)
  case v of
    Left err -> return $ PEq.Errored (PEE.loaderError err)
    Right (b, _) -> return b

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall bin.
  RunConfig ->
  PB.WhichBinaryRepr bin ->
  IO (PEq.EquivalenceStatus)
runSelfEquivConfig cfg wb = liftToEquivStatus $ do
  pd <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- IO.liftIO $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left e -> CME.throwError $ PEE.BadPatchInfo fp e
        Right r -> return (r <> patchData cfg)
    Nothing -> return $ patchData cfg
  let
    swapPair (PC.BlockAlignment { PC.originalBlockStart = obs, PC.patchedBlockStart = pbs }) = case wb of
      PB.OriginalRepr -> PC.BlockAlignment obs obs
      PB.PatchedRepr -> PC.BlockAlignment pbs pbs
    path :: PLE.LoadPaths = case wb of
      PB.OriginalRepr -> origPaths cfg
      PB.PatchedRepr -> patchedPaths cfg
    pairs' = map swapPair $ PC.patchPairs pd
    -- Note that we ignore the patched ignore list because this is a
    -- self-comparison of the original binary for diagnostic purposes
    oIgn = PC.ignoreOriginalAllocations pd
    pd' = PC.PatchData
      { PC.patchPairs = pairs'
      , PC.ignoreOriginalAllocations = oIgn
      , PC.ignorePatchedAllocations = oIgn
      , PC.equatedFunctions = PC.equatedFunctions pd
      , PC.ignoreOriginalFunctions = PC.ignoreOriginalFunctions pd
      , PC.ignorePatchedFunctions = PC.ignoreOriginalFunctions pd
      , PC.observableMemory = PC.observableMemory pd
      , PC.archOpts = PC.archOpts pd
      }
  (Some (PLE.LoadedElfPair proxy bin _), errs) <- CMW.listen $ PLE.loadELFs (archLoader cfg) pd' path path (useDwarfHints cfg)
  logger' <- IO.liftIO $ logger cfg proxy
  IO.liftIO $ runEquivVerification proxy errs logger' pd' (verificationCfg cfg) bin bin

runEquivConfig ::
  RunConfig ->
  IO (PEq.EquivalenceStatus)
runEquivConfig cfg = liftToEquivStatus $ do
  pdata <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- IO.liftIO $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left err -> CME.throwError $ PEE.BadPatchInfo fp err
        Right r -> return (r <> patchData cfg)
    Nothing -> return $ patchData cfg
  (Some (PLE.LoadedElfPair proxy original patched), errs) <-
    CMW.listen $ PLE.loadELFs (archLoader cfg) pdata (origPaths cfg) (patchedPaths cfg) (useDwarfHints cfg)
  logger' <- IO.liftIO $ logger cfg proxy
  IO.liftIO $ runEquivVerification proxy errs logger' pdata (verificationCfg cfg) original patched
