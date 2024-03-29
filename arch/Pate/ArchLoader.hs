module Pate.ArchLoader (
  archLoader
  ) where

import qualified Pate.AArch32 as AArch32
import qualified Pate.PPC as PPC

import qualified Pate.Arch as PA
import qualified Pate.Equivalence.Error as PEE

archLoader :: PA.ArchLoader PEE.LoadError
archLoader = PA.mergeLoaders AArch32.archLoader PPC.archLoader
