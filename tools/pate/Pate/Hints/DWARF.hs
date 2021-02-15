module Pate.Hints.DWARF (
  parseDWARFHints,
  DWARFError(..)
  ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.ElfEdit as DE
import qualified Data.Dwarf as DD

import qualified Pate.Hints as PH

data DWARFError = ELFParseError [DE.ElfParseError]
                | ELFHeaderError Integer String
  deriving (Show)

traverseELFHints :: DE.Elf n -> (PH.VerificationHints, [DWARFError])
traverseELFHints = undefined
  where
    lookupSection e b = DE.findSectionByName b e
    -- dwarfSections = DD.mkSections

parseDWARFHints :: BSL.ByteString -> (PH.VerificationHints, [DWARFError])
parseDWARFHints bs0 =
  case DE.parseElf (BSL.toStrict bs0) of
    DE.Elf32Res errs e32 ->
      let (hints, derrs) = traverseELFHints e32
      in (hints, addELFErrors errs derrs)
    DE.Elf64Res errs e64 ->
      let (hints, derrs) = traverseELFHints e64
      in (hints, addELFErrors errs derrs)
    DE.ElfHeaderError off msg -> (mempty, [ELFHeaderError (toInteger off) msg])
  where
    addELFErrors elfErrs otherErrs
      | null elfErrs = otherErrs
      | otherwise = ELFParseError elfErrs : otherErrs
