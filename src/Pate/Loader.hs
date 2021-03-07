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


import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Config as PC
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Types as PT
import qualified Pate.Verification as PV


hexToAddr :: PA.ValidArchProxy arch -> PC.Hex Word64 -> PT.ConcreteAddress arch
hexToAddr PA.ValidArchProxy (PC.Hex w) = PT.ConcreteAddress $ MM.absoluteAddr $ MM.memWord w

unpackBlockData :: PT.KnownBinary bin => PA.ValidArchProxy arch -> PC.BlockData -> PT.ConcreteBlock arch bin
unpackBlockData proxy start =
  PT.ConcreteBlock
    { PT.concreteAddress = hexToAddr proxy start
      -- we assume that all provided blocks begin a function
    , PT.concreteBlockEntry = PT.BlockEntryInitFunction
    , PT.blockBinRepr = DPC.knownRepr
    }

unpackPatchData :: PA.ValidArchProxy arch -> PC.PatchData -> (PT.BlockMapping arch, [PT.PatchPair arch])
unpackPatchData proxy (PC.PatchData pairs bmap) =
  let
    bmap' = PT.BlockMapping $ 
      Map.fromList $ map (\(addr, addr') -> (hexToAddr proxy addr, hexToAddr proxy addr')) bmap
    ppairs = map (\(bd, bd') -> PT.PatchPair (unpackBlockData proxy bd) (unpackBlockData proxy bd')) pairs
  in (bmap', ppairs)

runEquivVerification ::
  PA.ValidArchProxy arch ->
  LJ.LogAction IO (PE.Event arch) ->
  Maybe PH.VerificationHints ->
  PC.PatchData ->
  PC.VerificationConfig ->
  PB.LoadedELF arch ->
  PB.LoadedELF arch ->
  IO (Either String Bool)
runEquivVerification proxy@PA.ValidArchProxy logAction mhints pd dcfg original patched = do
  let (bmap, ppairs) = unpackPatchData proxy pd
  v <- CME.runExceptT (PV.verifyPairs logAction mhints original patched bmap dcfg ppairs)
  case v of
    Left err -> return $ Left $ show err
    Right b -> return $ Right b

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall arch bin.
  PC.RunConfig arch ->
  PT.WhichBinaryRepr bin ->
  IO (Either String Bool)
runSelfEquivConfig cfg wb = CME.runExceptT $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> CME.lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> CME.throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  let
    swapPair :: forall a. (a, a) -> (a, a)
    swapPair (a1, a2) = case wb of
      PT.OriginalRepr -> (a1, a1)
      PT.PatchedRepr -> (a2, a2)
    path :: String = case wb of
      PT.OriginalRepr -> PC.origPath cfg
      PT.PatchedRepr -> PC.patchedPath cfg
    pairs' = map swapPair $ PC.patchPairs patchData
    patchData' = PC.PatchData
      { PC.patchPairs = pairs'
      , PC.blockMapping = []
      }
  PA.ValidArchProxy <- return $ PC.archProxy cfg
  bin <- CME.lift $ PB.loadELF @arch Proxy $ path
  CME.ExceptT $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) (PC.hints cfg) patchData' (PC.verificationCfg cfg) bin bin


runEquivConfig :: forall arch.
  PC.RunConfig arch ->
  IO (Either String Bool)
runEquivConfig cfg = CME.runExceptT $ do
  patchData <- case PC.infoPath cfg of
    Left fp -> CME.lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> CME.throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  PA.ValidArchProxy <- return $ PC.archProxy cfg
  original <- CME.lift $ PB.loadELF @arch Proxy $ (PC.origPath cfg)
  patched <- CME.lift $ PB.loadELF @arch Proxy $ (PC.patchedPath cfg)
  CME.ExceptT $ runEquivVerification (PC.archProxy cfg) (PC.logger cfg) (PC.hints cfg) patchData (PC.verificationCfg cfg) original patched
