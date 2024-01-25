{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}

module Pate.Script (
    readScript
  , Script(..)
  , ScriptParseError(..)
  , runScript
) where

import           Control.Monad (void)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec ((<|>))

import           Pate.TraceTree
import Data.Void


data Script = Script [NodeQuery]
  deriving (Eq, Ord, Show)

type Parser a =  P.Parsec Void T.Text a

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

int :: Parser Int
int = lexeme L.decimal

sc :: Parser ()
sc = L.space
  (void $ P.some (P.char ' ' <|> P.char '\t'))        
  (L.skipLineComment "//")
  P.empty

scn :: Parser ()
scn = L.space
  P.space1   
  (L.skipLineComment "//")
  (L.skipBlockComment "/*" "*/")

parsePick :: Parser ()
parsePick = void $ P.string "pick"

parsePickInt :: Parser ()
parsePickInt = void $ P.string "pickInt"

parseUntilNewline :: Parser String
parseUntilNewline = P.some (P.notFollowedBy (P.newline) >> L.charLiteral)

parseIdentQuery :: Parser NodeIdentQuery
parseIdentQuery = 
  (QueryInt <$> (P.string "goto" >> sc >> int))
  <|> (P.notFollowedBy parsePick >> (QueryString <$> parseUntilNewline))

parseIdentQueryPick :: Parser NodeIdentQuery
parseIdentQueryPick =
      QueryInt <$> (parsePickInt >> sc >> int)
  <|> QueryString <$> (parsePick >> sc >> parseUntilNewline)

parseQuery :: Parser NodeQuery
parseQuery = do
  body <- P.manyTill (parseIdentQuery >>= \q -> scn >> return q) (P.lookAhead parsePick)
  fin <- parseIdentQueryPick
  return $ NodeQuery $ body ++ [fin]

parseScript :: Parser Script
parseScript = Script <$> parseQuery `P.sepBy` scn

newtype ScriptParseError = ScriptParseError String
  deriving Show

readScript :: FilePath -> IO (Either ScriptParseError Script)
readScript fp = do
  content <- T.readFile fp
  case P.parse parseScript fp content of
    Left err -> return $ Left $ ScriptParseError (P.errorBundlePretty err)
    Right a -> return $ Right a

runScript :: forall l (k :: l). Script -> TraceTree k -> IO ()
runScript (Script []) _ = return ()
runScript (Script (q:qs)) t = resolveQuery q t >>= \case
  Just node | Just mkChoice <- asChoice node -> mkChoice >> runScript (Script qs) t
  -- since 'resolveQuery' blocks until the tree has been fully resolved,
  -- this error won't get raised until the finalization step has completed
  _ -> putStrLn $ "Script failed: " ++ show q



