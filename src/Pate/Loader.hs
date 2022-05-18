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
  , RunConfig(..)
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


data RunConfig arch =
  RunConfig
    { archProxy :: PA.SomeValidArch arch
    , patchInfoPath :: Maybe FilePath
    , patchData :: PC.PatchData
    , origPath :: FilePath
    , patchedPath :: FilePath
    , logger :: LJ.LogAction IO (PE.Event arch)
    , verificationCfg :: PC.VerificationConfig
    , origHints :: PH.VerificationHints
    , patchedHints :: PH.VerificationHints
    }

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
  RunConfig arch ->
  PB.WhichBinaryRepr bin ->
  IO PEq.EquivalenceStatus
runSelfEquivConfig cfg wb = liftToEquivStatus $ do
  pd <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left e -> CME.throwError ("Bad patch info file: " ++ show e)
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
  PA.SomeValidArch {} <- return $ archProxy cfg
  bin <- CME.lift $ PLE.loadELF @arch Proxy $ path
  let hintedBin = PH.Hinted (origHints cfg) bin
  CME.lift $ runEquivVerification (archProxy cfg) (logger cfg) pd' (verificationCfg cfg) hintedBin hintedBin

runEquivConfig :: forall arch.
  RunConfig arch ->
  IO PEq.EquivalenceStatus
runEquivConfig cfg = liftToEquivStatus $ do
  patchData <- case patchInfoPath cfg of
    Just fp -> do
      bytes <- CME.lift $ BS.readFile fp
      case PC.parsePatchConfig bytes of
        Left err -> CME.throwError ("Bad patch info file: " ++ show err)
        Right r -> return (r <> patchData cfg)
    Nothing -> return $ patchData cfg
  PA.SomeValidArch {} <- return $ archProxy cfg
  original <- CME.lift $ PLE.loadELF @arch Proxy $ (origPath cfg)
  patched <- CME.lift $ PLE.loadELF @arch Proxy $ (patchedPath cfg)
  let hintedOrig = PH.Hinted (origHints cfg) original
  let hintedPatched = PH.Hinted (patchedHints cfg) patched
  CME.lift $ runEquivVerification (archProxy cfg) (logger cfg) patchData (verificationCfg cfg) hintedOrig hintedPatched
