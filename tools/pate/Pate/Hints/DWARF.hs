{-# LANGUAGE BangPatterns #-}
module Pate.Hints.DWARF (
  parseDWARFHints,
  DWARFError(..)
  ) where

import qualified Control.DeepSeq as CD
import qualified Control.Parallel.Strategies as CPS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ElfEdit as DE
import qualified Data.Dwarf as DD
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TE

import qualified Pate.Hints as PH

data DWARFError = ELFParseError [DE.ElfParseError]
                | ELFHeaderError !Integer String
                | ErrorLoadingDWARF
                | DWARFParseError String
                | ErrorReadingDIE String
                | DIEMissingAttribute !DD.DW_TAG !DD.DW_AT
                | DIEAttributeInvalidValueType !DD.DW_AT !DD.DW_ATVAL
  deriving (Show)

-- | We have to provide a manual instance because the 'DE.ElfParseError' type
-- does not have a 'CD.NFData' instance
instance CD.NFData DWARFError where
  rnf de =
    case de of
      ELFParseError errs -> length errs `CD.deepseq` ()
      ELFHeaderError _i msg -> msg `CD.deepseq` ()
      ErrorLoadingDWARF -> ()
      DWARFParseError msg -> msg `CD.deepseq` ()
      ErrorReadingDIE msg -> msg `CD.deepseq` ()
      DIEMissingAttribute !_ !_ -> ()
      DIEAttributeInvalidValueType !_ !_ -> ()

endianness :: DE.ElfData -> DD.Endianess
endianness ed =
  case ed of
    DE.ELFDATA2LSB -> DD.LittleEndian
    DE.ELFDATA2MSB -> DD.BigEndian

traverseCUDIE :: DD.CUContext -> (PH.VerificationHints, [DWARFError])
traverseCUDIE cu =
  case DD.cuFirstDie cu of
    Left err -> (mempty, [ErrorReadingDIE err])
    Right die -> traverseDIE die

withName :: DD.DW_TAG
         -> [(DD.DW_AT, DD.DW_ATVAL)]
         -> (T.Text -> (PH.VerificationHints, [DWARFError]))
         -> (PH.VerificationHints, [DWARFError])
withName tag attrs k =
  case lookup DD.DW_AT_name attrs of
    Nothing -> (mempty, [DIEMissingAttribute tag DD.DW_AT_name])
    Just (DD.DW_ATVAL_STRING nameBytes) -> k (TE.decodeUtf8With TE.lenientDecode nameBytes)
    Just (DD.DW_ATVAL_BLOB nameBytes) -> k (TE.decodeUtf8With TE.lenientDecode nameBytes)
    Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_AT_name atval])


variableHints :: [(DD.DW_AT, DD.DW_ATVAL)] -> (PH.VerificationHints, [DWARFError])
variableHints attrs =
  withName DD.DW_TAG_variable attrs $ \name ->
    case lookup DD.DW_AT_type attrs of
      Nothing -> (mempty, [DIEMissingAttribute DD.DW_TAG_variable DD.DW_AT_type])
      Just (DD.DW_ATVAL_UINT ty) -> variableLocation name ty
      Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_AT_type atval])
  where
    variableLocation name ty =
      case lookup DD.DW_AT_location attrs of
        Nothing -> (mempty, [DIEMissingAttribute DD.DW_TAG_variable DD.DW_AT_location])
        Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_AT_location atval])



-- | Subprograms have two things we are interested in:
--
-- 1. DW_AT_name
-- 2. DW_AT_low_pc
subprogramHints :: [(DD.DW_AT, DD.DW_ATVAL)] -> (PH.VerificationHints, [DWARFError])
subprogramHints attrs =
  withName DD.DW_TAG_subprogram attrs subprogramEntry
  where
    subprogramEntry name =
      case lookup DD.DW_AT_low_pc attrs of
        Nothing -> (mempty, [DIEMissingAttribute DD.DW_TAG_subprogram DD.DW_AT_low_pc])
        Just (DD.DW_ATVAL_UINT addr) ->
          let entry = (name, fromIntegral addr)
          in (mempty { PH.functionEntries = [entry] }, [])
        Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_AT_low_pc atval])

-- | Recursively traverse a 'DD.DIE' to find @DW_TAG_subprogram@ entries,
-- combining all of the results extracted from them.
traverseDIE :: DD.DIE -> (PH.VerificationHints, [DWARFError])
traverseDIE d =
  case DD.dieTag d of
    DD.DW_TAG_subprogram -> subprogramHints (DD.dieAttributes d)
    DD.DW_TAG_variable -> variableHints (DD.dieAttributes d)
    _ -> let (hints, errs) = unzip $ map traverseDIE (DD.dieChildren d)
         in (mconcat hints, mconcat errs)

dwarfCompilationUnits :: DD.Endianess -> DD.Sections -> ([DD.CUContext], [DWARFError])
dwarfCompilationUnits end sections = go (DD.firstCUContext end sections) ([], [])
  where
    go mCU acc@(cus, errs) =
      case mCU of
        Nothing -> acc
        Just (Left err) -> (cus, DWARFParseError err : errs)
        Just (Right cu) -> go (DD.nextCUContext cu) (cu : cus, errs)

traverseELFHints :: DE.Elf n -> (PH.VerificationHints, [DWARFError])
traverseELFHints e0 =
  case DD.mkSections lookupSection of
    Nothing -> (mempty, [ErrorLoadingDWARF])
    Just sections ->
      let (contexts, cuErrs) = dwarfCompilationUnits (endianness (DE.elfData e0)) sections
          (dieContexts, dieErrs) = unzip $ CPS.parMap CPS.rdeepseq traverseCUDIE contexts
      in (mconcat dieContexts, mconcat (cuErrs : dieErrs))
  where
    lookupSection b =
      case DE.findSectionByName b e0 of
        [s] -> Just (DE.elfSectionData s)
        _ -> Nothing

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
