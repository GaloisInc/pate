module Pate.Hints.CSV (
  parseFunctionHints,
  CSVParseError(..)
  ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.Csv as CSV
import qualified Data.Foldable as F
import qualified Data.Text as T
import           Data.Word( Word64 )
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPCL

import qualified Pate.Hints as PH

data CSVParseError = CSVParseError String
                   | UnexpectedRowShape [T.Text]
                   | AddressParseError T.Text
  deriving (Show, Eq)

-- | Parse an address of the form @code:<hexaddr>@ into a 'Word64'
parseAddress :: T.Text -> Maybe Word64
parseAddress = MP.parseMaybe parseCodeHex
  where
    parseCodeHex :: MP.Parsec () T.Text Word64
    parseCodeHex = do
      _ <- MPC.space
      _ <- MPC.string (T.pack "code:")
      MPCL.hexadecimal



parseFunctionEntry
  :: ([(T.Text, PH.FunctionDescriptor)], [CSVParseError])
  -> [T.Text]
  -> ([(T.Text, PH.FunctionDescriptor)], [CSVParseError])
parseFunctionEntry (items, errs) row =
  case row of
    (name : addr : row') ->
      case parseAddress addr of
        Nothing -> (items, AddressParseError addr : errs)
        Just a ->
          let addrEnd = case row' of
                [addrEnd_] -> parseAddress addrEnd_
                _ -> Nothing 
              fd = PH.FunctionDescriptor { PH.functionSymbol = name
                                         , PH.functionAddress = a
                                         , PH.functionArguments = []
                                         , PH.functionEnd = addrEnd
                                         }
          in ((name, fd) : items, errs)
    _ -> (items, UnexpectedRowShape row : errs)

-- | Parse a CSV file that provides a mapping from function names to addresses
--
-- The file is assumed to have two fields: @name, address@
--
-- Addresses have the form @code:<hexaddr>@
--
-- This function will always return hints (which may be empty).  Data errors
-- will be collected into a warning return.
parseFunctionHints :: BSL.ByteString -> (PH.VerificationHints, [CSVParseError])
parseFunctionHints bs =
  case CSV.decode CSV.NoHeader bs of
    Left err -> (mempty, [CSVParseError err])
    Right rows ->
      let (entries, warnings) = F.foldl' parseFunctionEntry ([], []) rows
      in (mempty { PH.functionEntries = entries }, warnings)
