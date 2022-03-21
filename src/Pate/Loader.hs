{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Loader
  (
    runEquivVerification
  , runSelfEquivConfig
  , runEquivConfig
  )
where

import qualified Control.Monad.Except as CME

import qualified Data.ByteString as BS
import           Data.Proxy ( Proxy(..) )
import qualified Lumberjack as LJ

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification as PV

runEquivVerification ::
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PC.PatchData ->
  PC.VerificationConfig ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  IO PEq.EquivalenceStatus
runEquivVerification validArch@(PA.SomeValidArch {}) logAction pd dcfg original patched = do
  liftToEquivStatus $ PV.verifyPairs validArch logAction original patched dcfg pd

liftToEquivStatus ::
  Show e =>
  Monad m =>
  CME.ExceptT e m PEq.EquivalenceStatus ->
  m PEq.EquivalenceStatus
liftToEquivStatus f = do
  v <- CME.runExceptT f
  case v of
    Left err -> return $ PEq.Errored $ show err
    Right b -> return b

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall arch bin.
  PC.RunConfig arch ->
  PB.WhichBinaryRepr bin ->
  IO PEq.EquivalenceStatus
runSelfEquivConfig cfg wb = liftToEquivStatus $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left e -> CME.throwError ("Bad patch info file: " ++ show e)
        Right r -> return r
    Right r -> return r
  let
    swapPair (PC.BlockAlignment { PC.originalBlockStart = obs, PC.patchedBlockStart = pbs }) = case wb of
      PB.OriginalRepr -> PC.BlockAlignment obs obs
      PB.PatchedRepr -> PC.BlockAlignment pbs pbs
    path :: String = case wb of
      PB.OriginalRepr -> PC.origPath cfg
      PB.PatchedRepr -> PC.patchedPath cfg
    pairs' = map swapPair $ PC.patchPairs patchData
    -- Note that we ignore the patched ignore list because this is a
    -- self-comparison of the original binary for diagnostic purposes
    oIgn = PC.ignoreOriginalAllocations patchData
    patchData' = PC.PatchData
      { PC.patchPairs = pairs'
      , PC.ignoreOriginalAllocations = oIgn
      , PC.ignorePatchedAllocations = oIgn
      , PC.equatedFunctions = PC.equatedFunctions patchData
      }
  PA.SomeValidArch {} <- return $ PC.archProxy cfg
  bin <- CME.lift $ PLE.loadELF @arch Proxy $ path
  let hintedBin = PH.Hinted (PC.origHints cfg) bin
  CME.lift $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) patchData' (PC.verificationCfg cfg) hintedBin hintedBin

runEquivConfig :: forall arch.
  PC.RunConfig arch ->
  IO PEq.EquivalenceStatus
runEquivConfig cfg = liftToEquivStatus $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left err -> CME.throwError ("Bad patch info file: " ++ show err)
        Right r -> return r
    Right r -> return r
  PA.SomeValidArch {} <- return $ PC.archProxy cfg
  original <- CME.lift $ PLE.loadELF @arch Proxy $ (PC.origPath cfg)
  patched <- CME.lift $ PLE.loadELF @arch Proxy $ (PC.patchedPath cfg)
  let hintedOrig = PH.Hinted (PC.origHints cfg) original
  let hintedPatched = PH.Hinted (PC.patchedHints cfg) patched
  CME.lift $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) patchData (PC.verificationCfg cfg) hintedOrig hintedPatched
