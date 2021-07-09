{-# LANGUAGE GADTs #-}
module Pate.Loader.Wrapper ( SomeLoadedBinary(..) ) where

import qualified Data.Macaw.BinaryLoader as MBL

data SomeLoadedBinary arch where
  SomeLoadedBinary :: (MBL.BinaryLoader arch binFmt) => MBL.LoadedBinary arch binFmt -> SomeLoadedBinary arch
