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
  )
where

import qualified Control.Monad.Except as CME

import qualified Data.ByteString as BS
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.ElfEdit as DEE
import qualified Lumberjack as LJ

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification as PV
import qualified Pate.Equivalence.Error as PEE

data RunConfig =
  RunConfig
    { patchInfoPath :: Maybe FilePath
    , patchData :: PC.PatchData
    , origPath :: FilePath
    , patchedPath :: FilePath
    , logger :: forall arch. PA.SomeValidArch arch -> LJ.LogAction IO (PE.Event arch)
    , verificationCfg :: PC.VerificationConfig
    , origHints :: PH.VerificationHints
    , patchedHints :: PH.VerificationHints
    , archLoader :: PA.ArchLoader PEE.LoadError
    }


runEquivVerification ::
  PA.SomeValidArch arch ->
  [DEE.ElfParseError] ->
  LJ.LogAction IO (PE.Event arch) ->
  PC.PatchData ->
  PC.VerificationConfig ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  IO PEq.EquivalenceStatus
runEquivVerification validArch@(PA.SomeValidArch {}) elfErrs logAction pd dcfg original patched = do
  LJ.writeLog logAction (PE.ElfLoaderWarnings elfErrs)
  (CME.runExceptT $ PV.verifyPairs validArch logAction original patched dcfg pd) >>= \case
    Left err -> return $ PEq.Errored err
    Right st -> return st

type LoaderM = CME.ExceptT PEE.LoadError IO

liftToEquivStatus ::
  LoaderM PEq.EquivalenceStatus ->
  IO PEq.EquivalenceStatus
liftToEquivStatus f = do
  v <- CME.runExceptT f
  case v of
    Left err -> return $ PEq.Errored (PEE.loaderError err)
    Right b -> return b

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall bin.
  RunConfig ->
  PB.WhichBinaryRepr bin ->
  IO PEq.EquivalenceStatus
runSelfEquivConfig cfg wb = liftToEquivStatus $ do
  pd <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left e -> CME.throwError $ PEE.BadPatchInfo fp e
        Right r -> return (r <> patchData cfg)
    Nothing -> return $ patchData cfg
  let
    swapPair (PC.BlockAlignment { PC.originalBlockStart = obs, PC.patchedBlockStart = pbs }) = case wb of
      PB.OriginalRepr -> PC.BlockAlignment obs obs
      PB.PatchedRepr -> PC.BlockAlignment pbs pbs
    path :: String = case wb of
      PB.OriginalRepr -> origPath cfg
      PB.PatchedRepr -> patchedPath cfg
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
      }
  Some (PLE.LoadedElfPair proxy errs bin _) <- PLE.loadELFs (archLoader cfg) path path
  let hintedBin = PH.Hinted (origHints cfg) bin
  let logger' = logger cfg proxy
  CME.lift $ runEquivVerification proxy errs logger' pd' (verificationCfg cfg) hintedBin hintedBin

runEquivConfig ::
  RunConfig ->
  IO PEq.EquivalenceStatus
runEquivConfig cfg = liftToEquivStatus $ do
  pdata <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left err -> CME.throwError $ PEE.BadPatchInfo fp err
        Right r -> return (r <> patchData cfg)
    Nothing -> return $ patchData cfg
  Some (PLE.LoadedElfPair proxy errs original patched) <-
    PLE.loadELFs (archLoader cfg) (origPath cfg) (patchedPath cfg)
  let hintedOrig = PH.Hinted (origHints cfg) original
  let hintedPatched = PH.Hinted (patchedHints cfg) patched
  let logger' = logger cfg proxy
  CME.lift $ runEquivVerification proxy errs logger' pdata (verificationCfg cfg) hintedOrig hintedPatched
