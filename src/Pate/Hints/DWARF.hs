{-# LANGUAGE BangPatterns #-}
module Pate.Hints.DWARF (
  parseDWARFHints,
  DWARFError(..)
  ) where

import qualified Control.DeepSeq as CD
import qualified Control.Parallel.Strategies as CPS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Dwarf as DD
import qualified Data.ElfEdit as DE
import qualified Data.Foldable as F
import           Data.Int ( Int64 )
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TE
import           Data.Word ( Word64 )

import qualified Pate.Hints as PH

-- | Errors that can occur while parsing DWARF metadata
data DWARFError = ELFParseError [DE.ElfParseError]
                | ELFHeaderError !Integer String
                | ErrorLoadingDWARF
                | DWARFParseError String
                | ErrorReadingDIE String
                | DIEMissingAttribute !DD.DW_TAG !DD.DW_AT
                | DIEAttributeInvalidValueType !DD.DW_TAG !DD.DW_AT !DD.DW_ATVAL
                | InvalidDIERef !DD.DW_TAG !DD.DW_AT !DD.DieID
                | ErrorParsingDW_OP !BS.ByteString !Int64 String
                | UnexpectedVariableLocation !T.Text !Word64 !DD.DW_OP
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
      DIEAttributeInvalidValueType !_ !_ !_ -> ()
      InvalidDIERef !_ !_ !_ -> ()
      ErrorParsingDW_OP !_ !_ msg -> msg `CD.deepseq` ()
      UnexpectedVariableLocation t _ !_op -> t `CD.deepseq` ()

-- | Convert ELF endianness to DWARF endianness
endianness :: DE.ElfData -> DD.Endianess
endianness ed =
  case ed of
    DE.ELFDATA2LSB -> DD.LittleEndian
    DE.ELFDATA2MSB -> DD.BigEndian

-- | Kick off the traversal of a single 'DD.CUContext'
traverseCUDIE :: Map.Map DD.DieID DD.DIE -> DD.CUContext -> (PH.VerificationHints, [DWARFError])
traverseCUDIE dieMap cu =
  case DD.cuFirstDie cu of
    Left err -> (mempty, [ErrorReadingDIE err])
    Right die -> traverseDIE dieMap die

-- | Extract a name for the given entity from its attribute list, returning an
-- 'DWARFError' if there is no name.
withName :: DD.DW_TAG
         -> [(DD.DW_AT, DD.DW_ATVAL)]
         -> (T.Text -> (PH.VerificationHints, [DWARFError]))
         -> (PH.VerificationHints, [DWARFError])
withName tag attrs k =
  case lookup DD.DW_AT_name attrs of
    Nothing -> (mempty, [DIEMissingAttribute tag DD.DW_AT_name])
    Just (DD.DW_ATVAL_STRING nameBytes) -> k (TE.decodeUtf8With TE.lenientDecode nameBytes)
    Just (DD.DW_ATVAL_BLOB nameBytes) -> k (TE.decodeUtf8With TE.lenientDecode nameBytes)
    Just atval -> (mempty, [DIEAttributeInvalidValueType tag DD.DW_AT_name atval])

-- | Learn anything we can from variable declarations
--
-- Many things can appear under this tag; we only want the globals.  There may
-- be many variants to this that need to be handled, particularly around the
-- type inspection (which may be multi-layered in the presence of typedefs)
variableHints :: Map.Map DD.DieID DD.DIE
              -> DD.Reader
              -> [(DD.DW_AT, DD.DW_ATVAL)]
              -> (PH.VerificationHints, [DWARFError])
variableHints dieMap reader attrs =
  withName DD.DW_TAG_variable attrs $ \name ->
    case lookup DD.DW_AT_type attrs of
      Nothing -> (mempty, [DIEMissingAttribute DD.DW_TAG_variable DD.DW_AT_type])
      Just (DD.DW_ATVAL_UINT ty) -> variableLocation name ty
      Just atval@(DD.DW_ATVAL_REF refId)
        | Just tyDie <- Map.lookup refId dieMap ->
          fromMaybe (mempty, [DIEAttributeInvalidValueType DD.DW_TAG_variable DD.DW_AT_type atval]) $ do
            DD.DW_ATVAL_UINT nBytes <- lookup DD.DW_AT_byte_size (DD.dieAttributes tyDie)
            return (variableLocation name nBytes)
        | otherwise -> (mempty, [InvalidDIERef DD.DW_TAG_variable DD.DW_AT_type refId])
      Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_TAG_variable DD.DW_AT_type atval])
  where
    variableLocation name nBytes =
      case lookup DD.DW_AT_location attrs of
        Nothing -> (mempty, [DIEMissingAttribute DD.DW_TAG_variable DD.DW_AT_location])
        Just (DD.DW_ATVAL_BLOB bytes) ->
          case DD.parseDW_OP reader bytes of
            Left (off, msg) -> (mempty, [ErrorParsingDW_OP bytes off msg])
            Right (_, _, DD.DW_OP_addr addr) ->
              (mempty { PH.dataSymbols = [(name, PH.SymbolExtent addr (fromIntegral nBytes))] }, [])
            Right (_, _, op) ->
              (mempty, [UnexpectedVariableLocation name nBytes op])
        Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_TAG_variable DD.DW_AT_location atval])

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
        Just atval -> (mempty, [DIEAttributeInvalidValueType DD.DW_TAG_subprogram DD.DW_AT_low_pc atval])

-- | Recursively traverse a 'DD.DIE' to find @DW_TAG_subprogram@ entries,
-- combining all of the results extracted from them.
traverseDIE :: Map.Map DD.DieID DD.DIE -> DD.DIE -> (PH.VerificationHints, [DWARFError])
traverseDIE dieMap d =
  case DD.dieTag d of
    DD.DW_TAG_subprogram -> subprogramHints (DD.dieAttributes d)
    DD.DW_TAG_variable -> variableHints dieMap (DD.dieReader d) (DD.dieAttributes d)
    _ -> let (hints, errs) = unzip $ map (traverseDIE dieMap) (DD.dieChildren d)
         in (mconcat hints, mconcat errs)

-- | Walk the list of compilation unit contexts and eagerly decode them into a
-- normal Haskell list
--
-- This is potentially a lot of up-front work, but it lets us process each
-- compilation unit in parallel later.
dwarfCompilationUnits :: DD.Endianess -> DD.Sections -> ([DD.CUContext], [DWARFError])
dwarfCompilationUnits end sections = go (DD.firstCUContext end sections) ([], [])
  where
    go mCU acc@(cus, errs) =
      case mCU of
        Nothing -> acc
        Just (Left err) -> (cus, DWARFParseError err : errs)
        Just (Right cu) -> go (DD.nextCUContext cu) (cu : cus, errs)

-- | Like 'DD.mkSections', except treat missing sections as empty (under the
-- premise that they are not referenced) instead of fatally exiting
loadSections :: (BS.ByteString -> Maybe BS.ByteString)
             -> DD.Sections
loadSections lookupSection =
  DD.Sections { DD.dsInfoSection = lookupDefault ".debug_info"
              , DD.dsArangesSection = lookupDefault ".debug_aranges"
              , DD.dsAbbrevSection = lookupDefault ".debug_abbrev"
              , DD.dsLineSection = lookupDefault ".debug_line"
              , DD.dsLocSection = lookupDefault ".debug_loc"
              , DD.dsRangesSection = lookupDefault ".debug_ranges"
              , DD.dsStrSection = lookupDefault ".debug_str"
              }
  where
    lookupDefault s = fromMaybe mempty (lookupSection (BSC.pack s))

-- | Recursively traverse all of the 'DD.DIE's to build a map from 'DD.DieID' to
-- 'DD.DIE's.  We need this to resolve 'DD.DW_ATVAL_REF' entries.
indexDIEs :: Map.Map DD.DieID DD.DIE
          -> DD.CUContext
          -> Map.Map DD.DieID DD.DIE
indexDIEs m0 cu =
  case DD.cuFirstDie cu of
    Left _ -> m0
    Right die0 -> go m0 die0
  where
    go m die = F.foldl' go (Map.insert (DD.dieId die) die m) (DD.dieChildren die)

-- | Traverse every compilation unit (potentially in parallel) to collect any
-- location hints we can.
traverseELFHints :: DE.Elf n -> (PH.VerificationHints, [DWARFError])
traverseELFHints e0 =
  let (contexts, cuErrs) = dwarfCompilationUnits (endianness (DE.elfData e0)) sections
      dieMap = F.foldl' indexDIEs Map.empty contexts
      (dieContexts, dieErrs) = unzip $ CPS.parMap CPS.rdeepseq (traverseCUDIE dieMap) contexts
  in (mconcat dieContexts, mconcat (cuErrs : dieErrs))
  where
    sections = loadSections lookupSection
    lookupSection b =
      case DE.findSectionByName b e0 of
        [s] -> Just (DE.elfSectionData s)
        _ -> Nothing

-- | Load an ELF file and parse its DWARF metadata, collecting any verification
-- hints we can use.
--
-- We currently extract:
--
--  * Function names and locations
--  * Global variable names, locations, and sizes
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
