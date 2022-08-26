{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase   #-}


module Pate.Loader.ELF (
    LoadedELF(..)
  , LoadedElfPair(..)
  , loadELF
  , loadELFs
  ) where

import qualified Control.Monad.Except as CME
import qualified Control.Monad.IO.Class as IO

import qualified Data.ByteString as BS
import qualified Data.Parameterized.Classes as DPC
import           Data.Proxy ( Proxy(..) )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Classes as PC

import qualified Data.ElfEdit as DEE
import qualified Data.ElfEdit.Prim as EEP
import qualified Data.Macaw.Memory.ElfLoader as MME
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.BinaryLoader as MBL

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.Error as PEE
import           Pate.Panic

data LoadedELF arch =
  LoadedELF
    { archInfo :: MI.ArchitectureInfo arch
    , loadedBinary :: MBL.LoadedBinary arch (DEE.ElfHeaderInfo (MC.ArchAddrWidth arch))
    , loadedHeader :: DEE.ElfHeader (MC.ArchAddrWidth arch)
    }

type LoaderM = CME.ExceptT PEE.LoadError IO

loadELF ::
  forall arch.
  PA.SomeValidArch arch ->
  FilePath ->
  LoaderM (LoadedELF arch)
loadELF (PA.SomeValidArch{}) path = do
  bs <- CME.lift $ BS.readFile path
  elf <- doParse bs
  mem <- CME.lift $ MBL.loadBinary MME.defaultLoadOptions elf
  return $ LoadedELF
    { archInfo = PA.binArchInfo mem
    , loadedBinary = mem
    , loadedHeader = (DEE.header elf)
    }
  where
    archWidthRepr :: MC.AddrWidthRepr (MC.ArchAddrWidth arch)
    archWidthRepr = MC.addrWidthRepr (Proxy @(MC.ArchAddrWidth arch))

    doParse :: BS.ByteString -> LoaderM (DEE.ElfHeaderInfo (MC.ArchAddrWidth arch))
    doParse bs = case DEE.decodeElfHeaderInfo bs of
      Left (off, msg) -> CME.throwError $ PEE.ElfHeaderParseError path off msg
      Right (DEE.SomeElf h) -> case DEE.headerClass (DEE.header h) of
        DEE.ELFCLASS32 -> return $ getElf h
        DEE.ELFCLASS64 -> return $ getElf h

    getElf :: forall w. MC.MemWidth w => DEE.ElfHeaderInfo w -> DEE.ElfHeaderInfo (MC.ArchAddrWidth arch)
    getElf e = case DPC.testEquality (MC.addrWidthRepr e) archWidthRepr of
      Just DPC.Refl -> e
      Nothing -> panic Loader "LoadElf" [ "Unexpected arch pointer width"
                                        , "expected: " ++ show archWidthRepr
                                        , "but got: " ++ show (MC.addrWidthRepr e)
                                        ]

data LoadedElfPair arch =
  LoadedElfPair (PA.SomeValidArch arch) [DEE.ElfParseError] (LoadedELF arch) (LoadedELF arch)

loadELFs ::
  PA.ArchLoader PEE.LoadError ->
  FilePath ->
  FilePath ->
  LoaderM (Some LoadedElfPair)
loadELFs archLoader fpOrig fpPatched = do
  (CME.lift $ archToProxy archLoader fpOrig fpPatched) >>= \case
    Left err -> CME.throwError err
    Right (elfErrs, Some proxy) -> do
      elfOrig <- loadELF proxy fpOrig
      elfPatched <- loadELF proxy fpPatched
      return $ Some (LoadedElfPair proxy elfErrs elfOrig elfPatched)

-- | Examine the input files to determine the architecture
archToProxy :: PA.ArchLoader PEE.LoadError -> FilePath -> FilePath -> IO (Either PEE.LoadError ([DEE.ElfParseError], Some PA.SomeValidArch))
archToProxy (PA.ArchLoader machineToProxy) origBinaryPath patchedBinaryPath = do
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
    (Left (off, msg), _) -> return (Left (PEE.ElfHeaderParseError origBinaryPath off msg))
    (_, Left (off, msg)) -> return (Left (PEE.ElfHeaderParseError patchedBinaryPath off msg))
    _ -> return (Left (PEE.ElfArchitectureMismatch origBinaryPath patchedBinaryPath))
