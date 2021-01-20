{- Helper functions for loading binaries -}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}


module Pate.Binary
  ( ArchConstraints(..)
  , LoadedELF(..)
  , loadELF
  )
where

import           GHC.TypeLits

import qualified Data.ByteString as BS
import           Data.Proxy

import           Data.Parameterized.Classes

import qualified Data.ElfEdit as E

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Memory.ElfLoader as MME
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.BinaryLoader as MBL

data LoadedELF arch =
  LoadedELF
    { archInfo :: MI.ArchitectureInfo arch
    , loadedBinary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
    }

class
  ( MC.MemWidth (MC.ArchAddrWidth arch)
  , MBL.BinaryLoader arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
  , E.ElfWidthConstraints (MC.ArchAddrWidth arch)
  , MS.SymArchConstraints arch
  , 16 <= MC.RegAddrWidth (MC.ArchReg arch)
  ) => ArchConstraints arch where
  binArchInfo :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MC.ArchAddrWidth arch)) -> MI.ArchitectureInfo arch

loadELF ::
  forall arch.
  ArchConstraints arch =>
  Proxy arch ->
  FilePath ->
  IO (LoadedELF arch)
loadELF _ path = do
  bs <- BS.readFile path
  elf <- doParse bs
  mem <- MBL.loadBinary MME.defaultLoadOptions elf
  return $ LoadedELF
    { archInfo = binArchInfo mem
    , loadedBinary = mem
    }
  where
    archWidthRepr :: MC.AddrWidthRepr (MC.ArchAddrWidth arch)
    archWidthRepr = MC.addrWidthRepr (Proxy @(MC.ArchAddrWidth arch))

    doParse :: BS.ByteString -> IO (E.ElfHeaderInfo (MC.ArchAddrWidth arch))
    doParse bs = case E.decodeElfHeaderInfo bs of
      Left (off, msg) -> error $ "Error while parsing ELF header at " ++ show off ++ ": " ++ msg
      Right (E.SomeElf h) -> case E.headerClass (E.header h) of
        E.ELFCLASS32 -> return $ getElf h
        E.ELFCLASS64 -> return $ getElf h
      
    getElf :: forall w. MC.MemWidth w => E.ElfHeaderInfo w -> E.ElfHeaderInfo (MC.ArchAddrWidth arch)
    getElf e = case testEquality (MC.addrWidthRepr e) archWidthRepr of
      Just Refl -> e
      Nothing -> error ("Unexpected arch pointer width; expected " ++ show archWidthRepr ++ " but got " ++ show (MC.addrWidthRepr e))
