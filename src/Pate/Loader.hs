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
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as DPC
import           Data.Proxy ( Proxy(..) )
import           Data.Word ( Word64 )
import qualified Lumberjack as LJ
import           Text.Read ( readMaybe )

import qualified Data.Macaw.Memory as MM

import qualified Pate.Address as PA
import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.PatchPair as PPa
import qualified Pate.Types as PT
import qualified Pate.Verification as PV

hexToAddr :: PA.SomeValidArch arch -> PC.Hex Word64 -> PA.ConcreteAddress arch
hexToAddr (PA.SomeValidArch {}) (PC.Hex w) = PA.ConcreteAddress $ MM.absoluteAddr $ MM.memWord w

unpackBlockData :: PB.KnownBinary bin => PA.SomeValidArch arch -> PC.BlockData -> PB.ConcreteBlock arch bin
unpackBlockData proxy start =
  PB.ConcreteBlock
    { PB.concreteAddress = hexToAddr proxy start
      -- we assume that all provided blocks begin a function
    , PB.concreteBlockEntry = PB.BlockEntryInitFunction
    , PB.blockBinRepr = DPC.knownRepr
    }

unpackPatchData :: PA.SomeValidArch arch -> PC.PatchData -> (PT.BlockMapping arch, [PPa.BlockPair arch])
unpackPatchData proxy (PC.PatchData pairs bmap) =
  let
    bmap' = PT.BlockMapping $ 
      Map.fromList $ map (\(addr, addr') -> (hexToAddr proxy addr, hexToAddr proxy addr')) bmap
    ppairs = map (\(bd, bd') -> PPa.PatchPair (unpackBlockData proxy bd) (unpackBlockData proxy bd')) pairs
  in (bmap', ppairs)


runEquivVerification ::
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  Maybe PH.VerificationHints ->
  PC.PatchData ->
  PC.VerificationConfig ->
  PLE.LoadedELF arch ->
  PLE.LoadedELF arch ->
  IO PT.EquivalenceStatus
runEquivVerification validArch@(PA.SomeValidArch {}) logAction mhints pd dcfg original patched = do
  let (bmap, ppairs) = unpackPatchData validArch pd
  liftToEquivStatus $ PV.verifyPairs validArch logAction mhints original patched bmap dcfg ppairs

liftToEquivStatus ::
  Show e =>
  Monad m =>
  CME.ExceptT e m PT.EquivalenceStatus ->
  m PT.EquivalenceStatus
liftToEquivStatus f = do
  v <- CME.runExceptT f
  case v of
    Left err -> return $ PT.Errored $ show err
    Right b -> return b  

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall arch bin.
  PC.RunConfig arch ->
  PB.WhichBinaryRepr bin ->
  IO PT.EquivalenceStatus
runSelfEquivConfig cfg wb = liftToEquivStatus $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> CME.lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> CME.throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  let
    swapPair :: forall a. (a, a) -> (a, a)
    swapPair (a1, a2) = case wb of
      PB.OriginalRepr -> (a1, a1)
      PB.PatchedRepr -> (a2, a2)
    path :: String = case wb of
      PB.OriginalRepr -> PC.origPath cfg
      PB.PatchedRepr -> PC.patchedPath cfg
    pairs' = map swapPair $ PC.patchPairs patchData
    patchData' = PC.PatchData
      { PC.patchPairs = pairs'
      , PC.blockMapping = []
      }
  PA.SomeValidArch {} <- return $ PC.archProxy cfg
  bin <- CME.lift $ PLE.loadELF @arch Proxy $ path
  CME.lift $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) (PC.hints cfg) patchData' (PC.verificationCfg cfg) bin bin

runEquivConfig :: forall arch.
  PC.RunConfig arch ->
  IO PT.EquivalenceStatus
runEquivConfig cfg = liftToEquivStatus $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> CME.lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> CME.throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  PA.SomeValidArch {} <- return $ PC.archProxy cfg
  original <- CME.lift $ PLE.loadELF @arch Proxy $ (PC.origPath cfg)
  patched <- CME.lift $ PLE.loadELF @arch Proxy $ (PC.patchedPath cfg)
  CME.lift $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) (PC.hints cfg) patchData (PC.verificationCfg cfg) original patched
