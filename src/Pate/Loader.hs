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
  , PatchData(..)
  , noPatchData
  , RunConfig(..)
  , ValidArchProxy(..)
  )
where

import           Control.Monad.Except

import           Data.Word ( Word64 )
import           Data.Proxy
import qualified Data.Map as Map
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import qualified Data.Macaw.Memory as MM

import qualified Pate.Binary as PB
import qualified Pate.Types as PT
import qualified Pate.Monad as PM
import qualified Pate.Verification as PV


data ValidArchProxy arch where
  ValidArchProxy :: (PM.ValidArch arch, PB.ArchConstraints arch) => ValidArchProxy arch

newtype Hex a = Hex a
  deriving (Eq, Ord, Num, PrintfArg)

instance (Num a, Show a, PrintfArg a) => Show (Hex a) where
  show (Hex a) = printf "0x%x" a

instance (Read a) => Read (Hex a) where
  readsPrec i s = [ (Hex a, s') | (a, s') <- readsPrec i s ]

type BlockData = Hex Word64

data PatchData =
  PatchData { patchPairs :: [(BlockData, BlockData)]
            , blockMapping :: [(Hex Word64, Hex Word64)]
            }
  deriving (Read, Show, Eq)

noPatchData :: PatchData
noPatchData = PatchData [] []

hexToAddr :: ValidArchProxy arch -> Hex Word64 -> PT.ConcreteAddress arch
hexToAddr ValidArchProxy (Hex w) = PT.ConcreteAddress $ MM.absoluteAddr $ MM.memWord w

unpackBlockData :: ValidArchProxy arch -> BlockData -> PT.ConcreteBlock arch
unpackBlockData proxy start =
  PT.ConcreteBlock
    { PT.concreteAddress = (hexToAddr proxy start)
      -- we assume that all provided blocks begin a function
    , PT.concreteBlockEntry = PT.BlockEntryInitFunction
    }

unpackPatchData :: ValidArchProxy arch -> PatchData -> (PT.BlockMapping arch, [PT.PatchPair arch])
unpackPatchData proxy (PatchData pairs bmap) =
  let
    bmap' = PT.BlockMapping $ 
      Map.fromList $ map (\(addr, addr') -> (hexToAddr proxy addr, hexToAddr proxy addr')) bmap
    ppairs = map (\(bd, bd') -> PT.PatchPair (unpackBlockData proxy bd) (unpackBlockData proxy bd')) pairs
  in (bmap', ppairs)

runEquivVerification ::
  ValidArchProxy arch ->
  PatchData ->
  PT.DiscoveryConfig ->
  PB.LoadedELF arch ->
  PB.LoadedELF arch ->
  IO (Either String Bool)
runEquivVerification proxy@ValidArchProxy pd dcfg original patched = do
  let (bmap, ppairs) = unpackPatchData proxy pd
  v <- runExceptT (PV.verifyPairs original patched bmap dcfg ppairs)
  case v of
    Left err -> return $ Left $ show err
    Right b -> return $ Right b

data RunConfig arch =
  RunConfig
    { archProxy :: ValidArchProxy arch
    , infoPath :: Either FilePath PatchData
    , origPath :: FilePath
    , patchedPath :: FilePath
    , discoveryCfg :: PT.DiscoveryConfig
    }

-- | Given a patch configuration, check that
-- either the original or patched binary can be
-- proven self-equivalent
runSelfEquivConfig :: forall arch.
  RunConfig arch ->
  PT.WhichBinary ->
  IO (Either String Bool)
runSelfEquivConfig cfg wb = runExceptT $ do
  patchData <- case infoPath cfg of
    Left fp -> lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  let
    swapPair :: forall a. (a, a) -> (a, a)
    swapPair (a1, a2) = case wb of
      PT.Original -> (a1, a1)
      PT.Rewritten -> (a2, a2)
    path = case wb of
      PT.Original -> origPath cfg
      PT.Rewritten -> patchedPath cfg
    pairs' = map swapPair $ patchPairs patchData
    patchData' = PatchData
      { patchPairs = pairs'
      , blockMapping = []
      }
  ValidArchProxy <- return $ archProxy cfg
  bin <- lift $ PB.loadELF @arch Proxy $ path
  ExceptT $ runEquivVerification (archProxy cfg) patchData' (discoveryCfg cfg) bin bin


runEquivConfig :: forall arch.
  RunConfig arch ->
  IO (Either String Bool)
runEquivConfig cfg = runExceptT $ do
  patchData <- case infoPath cfg of
    Left fp -> lift (readMaybe <$> readFile fp) >>= \case
      Nothing -> throwError "Bad patch info file"
      Just r -> return r
    Right r -> return r
  ValidArchProxy <- return $ archProxy cfg
  original <- lift $ PB.loadELF @arch Proxy $ (origPath cfg)
  patched <- lift $ PB.loadELF @arch Proxy $ (patchedPath cfg)
  ExceptT $ runEquivVerification (archProxy cfg) patchData (discoveryCfg cfg) original patched
