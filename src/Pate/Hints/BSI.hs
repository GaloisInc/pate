{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Pate.Hints.BSI (
  JSONError(..),
  parseSymbolSpecHints
  ) where

import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HMS
import           Data.Maybe ( fromMaybe )
import qualified Data.Scientific as DS
import qualified Data.Text as T

import qualified Pate.Hints as PH
import Control.Applicative ((<|>))

data JSONError = JSONParseError String
               | UnexpectedTopLevel String JSON.Value
  deriving (Show, Eq)

parseSymbolSpecHints :: BSL.ByteString -> (PH.VerificationHints, [JSONError])
parseSymbolSpecHints bs =
  case JSON.eitherDecode' bs of
    Left err -> (mempty, [JSONParseError err])
    Right val -> readSymbolMap val

readSymbolMap :: JSON.Value -> (PH.VerificationHints, [JSONError])
readSymbolMap val = case val of
  JSON.Object o -> fromMaybe (mempty, [UnexpectedTopLevel "Missing 'functions' or 'global_variables'" val]) $ do
    JSON.Array fns <- HMS.lookup (T.pack "functions") o
    JSON.Array vars <- HMS.lookup (T.pack "global_variables") o
    let (funAddrs, funErrs) = F.foldl' collectFunctions ([], []) fns
    let (varExtents, varErrs) = F.foldl' collectGlobals ([], []) vars
    return (mempty { PH.functionEntries = funAddrs
                   , PH.dataSymbols = varExtents
                   }, funErrs ++ varErrs)
  _ -> (mempty, [UnexpectedTopLevel "Missing Toplevel" val])
-- TODO: we aren't collecting the clobbered or argument
-- registers here, but it would certainly be a good idea
-- as it would make our stubs more accurate

readSourceMatch ::
  String ->
  JSON.Object -> 
  Maybe T.Text
readSourceMatch elemNm o = do
  (JSON.String fnName) <- HMS.lookup (T.pack elemNm) o
  case fnName of
    "BSI_UNASSIGNED" -> fail ""
    _ -> return fnName

collectFunctions :: ([(T.Text, PH.FunctionDescriptor)], [JSONError])
                 -> JSON.Value
                 -> ([(T.Text, PH.FunctionDescriptor)], [JSONError])
collectFunctions (fnSpecs, errs) v =
  case v of
    JSON.Object o
      | Just (JSON.Number fnAddrS) <- HMS.lookup (T.pack "address") o
      , Just fnAddr <- DS.toBoundedInteger fnAddrS
      , Just fnName <- (readSourceMatch "source_match" o 
                       <|> readSourceMatch "candidate_source_match" o) ->
        let
          fd = PH.FunctionDescriptor { PH.functionSymbol = fnName
                                     , PH.functionAddress = fnAddr
                                     , PH.functionArguments = []
                                     -- FIXME: BSI format has function endings
                                     , PH.functionEnd = Nothing
                                     }
        in ((fnName, fd) : fnSpecs, errs)
    JSON.Object o | Just _ <- (HMS.lookup (T.pack "source_match") o <|> HMS.lookup (T.pack "candidate_source_match") o) ->
      (fnSpecs, errs)
    _ -> (fnSpecs, UnexpectedTopLevel "Function" v : errs)

collectGlobals :: ([(T.Text, PH.SymbolExtent)], [JSONError])
               -> JSON.Value
               -> ([(T.Text, PH.SymbolExtent)], [JSONError])
collectGlobals (varSpecs, errs) v =
  case v of
    JSON.Object o
      | Just (JSON.String varNm) <- HMS.lookup (T.pack "name") o
      , Just (JSON.Object strg) <- HMS.lookup (T.pack "storage") o
      , Just (JSON.String "global") <- HMS.lookup (T.pack "type") strg
      , Just (JSON.Number varAddrS) <- HMS.lookup (T.pack "location") strg
      , Just varAddr <- DS.toBoundedInteger varAddrS ->
        let se = PH.SymbolExtent { PH.symbolLocation = varAddr
                                 -- FIXME: metadata does not include this
                                  , PH.symbolSize = 0
                                  }
        in ((varNm, se) : varSpecs, errs)
    _ -> (varSpecs, UnexpectedTopLevel "Global" v : errs)
