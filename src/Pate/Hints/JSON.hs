{-# LANGUAGE ViewPatterns #-}
module Pate.Hints.JSON (
  JSONError(..),
  parseProbabilisticHints,
  parseAnvillSpecHints
  ) where

import           Control.Applicative ( (<|>) )
import           Control.Monad ( guard )
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Foldable as F
import           Data.Function ( on )
import qualified Compat.Aeson as HMS

import qualified Data.List as L
import           Data.Maybe ( fromMaybe, mapMaybe )
import qualified Data.Scientific as DS
import qualified Data.Text as T
import           Data.Word ( Word32, Word64 )
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPCL

import qualified Pate.Hints as PH

data JSONError = JSONParseError String
               | UnexpectedTopLevel String JSON.Value
               | UnexpectedMatchEntryType Word64 String
               | MatchEntryMissingMatches Word64
               | InvalidAddressFormat DS.Scientific T.Text
               | MalformedAnvillFunctionAddress [JSON.Value]
               | MalformedAnvillVariableAddress [JSON.Value]
               | MalformedAnvillVariableSpec JSON.Value
               | UnknownTypeSize T.Text Word64
               | InvalidAddress T.Text
  deriving (Show, Eq)

readProbabilisticNameMap :: JSON.Value -> ([(T.Text, PH.FunctionDescriptor)], [JSONError])
readProbabilisticNameMap val =
  case val of
    JSON.Object o -> F.foldl' collectProbabilisticMappings ([], []) (HMS.toList o)
    JSON.Null -> ([], [])
    _ -> ([], [UnexpectedTopLevel "ProbNameMap" val])

-- | Parse an address of the form @code:<hexaddr>@ into a 'Word64'
parseAddress :: T.Text -> Maybe Word64
parseAddress = MP.parseMaybe parseCodeHex
  where
    parseCodeHex :: MP.Parsec () T.Text Word64
    parseCodeHex = do
      _ <- MPC.string (T.pack "0x")
      MPCL.hexadecimal

-- | The values are expected to be objects with a @matches@ key
collectProbabilisticMappings
  :: ([(T.Text, PH.FunctionDescriptor)], [JSONError])
  -> (T.Text, JSON.Value)
  -> ([(T.Text, PH.FunctionDescriptor)], [JSONError])
collectProbabilisticMappings (mapping, errs) (textAddr, val) =
  case parseAddress textAddr of
    Nothing -> (mapping, InvalidAddress textAddr : errs)
    Just addr ->
      case parseMappingVal addr val of
        Left err -> (mapping, err : errs)
        Right name ->
          let fd = PH.FunctionDescriptor { PH.functionSymbol = name
                                         , PH.functionAddress = addr
                                         , PH.functionArguments = []
                                         , PH.functionEnd = Nothing
                                         }
          in ((name, fd) : mapping, errs)

parseMappingVal :: Word64 -> JSON.Value -> Either JSONError T.Text
parseMappingVal addr val0 =
  case val0 of
    JSON.Object o ->
      case takeGroundTruth o <|> takeHighestConfidenceMatch o of
        Nothing -> Left (MatchEntryMissingMatches addr)
        Just r -> Right r
    JSON.Null -> Left (UnexpectedMatchEntryType addr "Null")
    JSON.Array _ -> Left (UnexpectedMatchEntryType addr "Array")
    JSON.String _ -> Left (UnexpectedMatchEntryType addr "String")
    JSON.Number _ -> Left (UnexpectedMatchEntryType addr "Number")
    JSON.Bool _ -> Left (UnexpectedMatchEntryType addr "Bool")

-- | If there is a ground truth entry under the key @symbol_name@, take that as the name
takeGroundTruth :: JSON.Object -> Maybe T.Text
takeGroundTruth o = do
  JSON.String s <- HMS.lookup (T.pack "symbol_name") o
  return s

data MatchStruct =
  MatchStruct { matchConfidence :: Float
              , matchName :: T.Text
              }

asMatchStruct :: JSON.Value -> Maybe MatchStruct
asMatchStruct v =
  case v of
    JSON.Object o -> do
      JSON.Number c <- HMS.lookup (T.pack "confidence") o
      JSON.String n <- HMS.lookup (T.pack "function") o
      return (MatchStruct (DS.toRealFloat c) n)
    _ -> Nothing

takeHighestConfidenceMatch :: JSON.Object -> Maybe T.Text
takeHighestConfidenceMatch o = do
  JSON.Array arr <- HMS.lookup (T.pack "matches") o
  let matches = mapMaybe asMatchStruct (F.toList arr)
  guard (not (null matches))
  return (matchName (L.maximumBy (compare `on` matchConfidence) matches))


-- | Parse a JSON file containing function addresses mapped (probabilistically)
-- to names
--
-- It will take the highest probability name for each function (or the first if
-- there is a tie)
parseProbabilisticHints :: BSL.ByteString -> (PH.VerificationHints, [JSONError])
parseProbabilisticHints bs =
  case JSON.eitherDecode' bs of
    Left err -> (mempty, [JSONParseError err])
    Right val ->
      let (mappings, errs) = readProbabilisticNameMap val
      in (mempty { PH.functionEntries = mappings }, errs)

collectAnvillFunctions :: HMS.HashMap Word64 T.Text
                       -> ([(T.Text, PH.FunctionDescriptor)], [JSONError])
                       -> JSON.Value
                       -> ([(T.Text, PH.FunctionDescriptor)], [JSONError])
collectAnvillFunctions addrSymMap (fnSpecs, errs) v =
  case v of
    JSON.Object o
      | Just (JSON.Number fnAddrS) <- HMS.lookup (T.pack "address") o
      , Just fnAddr <- DS.toBoundedInteger fnAddrS
      , Just fnName <- HMS.lookup fnAddr addrSymMap ->
        let fd = PH.FunctionDescriptor { PH.functionSymbol = fnName
                                       , PH.functionAddress = fnAddr
                                       , PH.functionArguments = []
                                       , PH.functionEnd = Nothing
                                       }
        in ((fnName, fd) : fnSpecs, errs)
    _ -> (fnSpecs, UnexpectedTopLevel "Function" v : errs)

-- | Return the size corresponding to an Anvill type spec
--
-- FIXME: This currently assumes that pointers are 4 bytes; we need to pass down
-- the architecture to compute this properly
anvillTypeSize :: T.Text -> Maybe Word32
anvillTypeSize t =
  case T.unpack t of
    "?" -> Just 1
    "b" -> Just 1
    "B" -> Just 1
    "h" -> Just 2
    "H" -> Just 2
    "i" -> Just 4
    "I" -> Just 4
    "l" -> Just 8
    "L" -> Just 8
    "o" -> Just 16
    "O" -> Just 16
    "e" -> Just 2
    "f" -> Just 4
    "d" -> Just 8
    "M" -> Just 8
    "Q" -> Just 16
    '*':_ -> Just 4
    _ -> Nothing

-- | Compute an extent from a type descriptor and address
--
-- Note that the type descriptors are currently treated unsafely and actually
-- need to be considered with both the architecture and OS to be really correct
anvillExtent :: T.Text -> T.Text -> Word64 -> Maybe (T.Text, PH.SymbolExtent)
anvillExtent varName tyStr addr = do
  sz <- anvillTypeSize tyStr
  let ext = PH.SymbolExtent { PH.symbolLocation = addr
                            , PH.symbolSize = sz
                            }
  return (varName, ext)

collectAnvillVars :: HMS.HashMap Word64 T.Text
                  -> ([(T.Text, PH.SymbolExtent)], [JSONError])
                  -> JSON.Value
                  -> ([(T.Text, PH.SymbolExtent)], [JSONError])
collectAnvillVars addrSymMap (extents, errs) v =
  case v of
    JSON.Object o
      | Just (JSON.String tyStr) <- HMS.lookup (T.pack "type") o
      , Just (JSON.Number addr) <- HMS.lookup (T.pack "address") o ->
        case DS.toBoundedInteger addr of
          Nothing -> (extents, MalformedAnvillVariableAddress [JSON.Number addr] : errs)
          Just addrw
            | Just name <- HMS.lookup addrw addrSymMap
            , Just ext <- anvillExtent name tyStr addrw -> (ext : extents, errs)
            | otherwise -> (extents, UnknownTypeSize tyStr addrw : errs)
    _ -> (extents, UnexpectedTopLevel "Variable" v : errs)

indexSymbolAddresses :: HMS.HashMap Word64 T.Text
                     -> JSON.Value
                     -> HMS.HashMap Word64 T.Text
indexSymbolAddresses m v =
  case v of
    JSON.Array (F.toList -> [JSON.Number (DS.toBoundedInteger -> Just addr), JSON.String name]) ->
      HMS.insert addr name m
    _ -> m

-- | Parse Anvill JSON files, which encode specifications of machine code functions
--
-- These come from the Trail of Bits Anvill tool.  The format is specified here:
--
-- https://github.com/lifting-bits/anvill/blob/master/docs/SpecificationFormat.md
parseAnvillSpecHints :: BSL.ByteString -> (PH.VerificationHints, [JSONError])
parseAnvillSpecHints bs =
  case JSON.eitherDecode' bs of
    Left err -> (mempty, [JSONParseError err])
    Right val ->
      case val of
        JSON.Object o -> fromMaybe (mempty, [UnexpectedTopLevel "Missing 'symbols', 'variables', or 'functions' array" val]) $ do
          JSON.Array syms <- HMS.lookup (T.pack "symbols") o
          JSON.Array vars <- HMS.lookup (T.pack "variables") o
          JSON.Array fns <- HMS.lookup (T.pack "functions") o
          let symAddrMap = F.foldl' indexSymbolAddresses HMS.empty syms
          let (funAddrs, funErrs) = F.foldl' (collectAnvillFunctions symAddrMap) ([], []) fns
          let (varExtents, varErrs) = F.foldl' (collectAnvillVars symAddrMap) ([], []) vars
          return (mempty { PH.functionEntries = funAddrs
                         , PH.dataSymbols = varExtents
                         }, funErrs ++ varErrs)
        _ -> (mempty, [UnexpectedTopLevel "Spec" val])
