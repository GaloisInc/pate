{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}

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
import qualified System.IO as IO
import Control.Concurrent (threadDelay)


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

data ScriptStep =
   ScriptBlock [NodeIdentQuery] [ScriptStep]
 | ScriptTerminal NodeIdentQuery

-- Collect prefix of steps with no body
stripSteps :: [ScriptStep] -> ([NodeIdentQuery], [ScriptStep])
stripSteps [] = ([],[])
stripSteps ((ScriptBlock qs []):xs) = let
  (qs',xs') = stripSteps xs
  in (qs ++ qs', xs')
stripSteps xs = ([],xs)

parseScriptStep :: Parser ScriptStep
parseScriptStep = term <|> do
  (beg,blks) <- L.indentBlock scn p
  let (body, blks') = stripSteps blks
  return $ ScriptBlock (QueryString beg:body) blks'

  where
    term = (ScriptTerminal . QueryString) <$> ("> " >> parseUntilNewline)

    p = do
      header <- parseUntilNewline
      return (L.IndentSome Nothing (return . (header, )) parseScriptStep)

parseScriptSteps :: Parser [ScriptStep]
parseScriptSteps = parseScriptStep `P.sepBy` scn


newtype ScriptParseError = ScriptParseError String
  deriving Show

stepToQueries :: ScriptStep -> [[NodeIdentQuery]]
stepToQueries (ScriptBlock qs []) = return $ qs
stepToQueries (ScriptBlock qs s) = do
  s' <- s
  qs' <- stepToQueries s'
  return $ qs ++ qs'
stepToQueries (ScriptTerminal q) = return $ [q]

stepsToScript :: [ScriptStep] -> Script
stepsToScript ss = Script $ concat $ map (\s -> map NodeQuery (stepToQueries s)) ss

readScript :: FilePath -> IO (Either ScriptParseError Script)
readScript fp = do
  content <- T.readFile fp
  case P.parse parseScriptSteps fp content of
    Left err -> return $ Left $ ScriptParseError (P.errorBundlePretty err)
    Right a -> return $ Right (stepsToScript a)

runScript :: forall l (k :: l). Script -> TraceTree k -> IO ()
runScript (Script s) t = do
  IO.putStrLn $ "Running script:" ++ (show s)
  go s
  where
    go [] = return ()
    go (q:qs)  = do
      IO.putStrLn $ "Running query:" ++ (show q)
      result <- resolveQuery q t $ \node ->
        case asChoice node of
          Just (SomeChoice c) -> choiceChosen c >>= \case
            True -> return Nothing
            False -> choiceReady (choiceHeader c) >>= \case
              True -> return Nothing
              False -> return $ Just (choicePick c)
          Nothing -> return Nothing
      IO.putStrLn $ "Query succeeded:" ++ (show q)
      case result of
        Nothing -> putStrLn $ "Query failed: " ++ show q
        Just f -> f >> go qs