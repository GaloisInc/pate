{-|
Module           : Pate.Script
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Parser for providing scripted inputs to 'Pate.TraceTree'. Format is as follows:

ToplevelNode T
  SubNode A
  SubNode B
    SubNode C
    > ChoiceNode E   /* T, A, B, C, > E */

    SubNode F
    ? SubNode G      /* T, A, B, F, > G */
  SubNode H
    ...
    > ChoiceNode I   /* T, H, ..., > I */
  :N SubNode J
    ? :M             /* T, :N J, ? :M */

ToplevelNode K
  ? SubNode L        /* K, > L */

This expands to a collection of queries which can be attached to a 'SomeTraceTree'
using 'attachToTraceTree'. Each query is executed in order, waiting for the specified
node to become available and optionally selects an interactive choice.

Each terminal query line (prefixed by '?' or '>') is desugared into a full
query according to its nesting structure (full queries are shown with inline comments above).
Queries terminating in '>' indicate that the specified node must be an interactive choice,
which is selected when the query resolves. Otherwise, a query terminating in '?' has no effect,
other than blocking execution until that node becomes available in the tree.
(TODO: likely these should emit logs somewhere). Additionally, any chain of empty blocks
is added to the prefix of the first non-empty block. e.g:

A
B
  C
  > D

Is the same as

A
  B
    C
      > D


A query line has one of the following forms:
   * N: - matches the Nth node at this level
   * N: S - matches the Nth node at this level only if it also has the prefix S when printed
   * S - matches a node that has the prefix S when printed
   * ... - wildcard (matches any node at this level)

Notably nodes are printed according to their 'Simplified' printer when matching against strings.

A query line may match multiple subnodes in a given TraceTree (i.e. for string or wildcard matches).
In this case, the node that is matched is the first node (in order) that successfully matches
the rest of the query.

-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}

module Pate.Script (
    readScript
  , Script
  , ScriptParseError
  , parseScript
  , attachToTraceTree
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
import Data.Maybe (fromMaybe)
-- import qualified System.IO as IO

data Script = Script [NodeQuery]

instance Show Script where
  show (Script s) = unlines $ map show s

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

parseUntilNewline :: Parser String
parseUntilNewline = P.some (P.notFollowedBy (P.newline) >> L.charLiteral)


data ScriptStep =
   ScriptBlock NodeIdentQuery [ScriptStep]
 | ScriptTerminal NodeIdentQuery NodeFinalAction

pickChoiceAct :: NodeFinalAction
pickChoiceAct = NodeFinalAction $ \node -> case asChoice node of
  Just (SomeChoice c) -> choiceChosen c >>= \case
    True -> return False
    False -> choiceReady (choiceHeader c) >>= \case
      True -> return False
      False -> choicePick c >> return True
  Nothing -> return False

matchAnyAct :: NodeFinalAction
matchAnyAct = NodeFinalAction $ \_ -> return True

parseIdentQuery :: Parser NodeIdentQuery
parseIdentQuery =
  (do
    i <- int
    _ <- ":"
    s <- P.many (P.notFollowedBy (P.newline) >> L.charLiteral)
    case s of
      "" ->  return $ QueryInt (fromIntegral i)
      _ -> return $ QueryStringInt (fromIntegral i) (dropWhile ((==) ' ') s)
    ) <|> ("..." >> return QueryAny) <|> (QueryString <$> parseUntilNewline)

parseScriptStep :: Parser ScriptStep
parseScriptStep = term <|> do
  (q,blks) <- L.indentBlock scn p
  return $ ScriptBlock q blks

  where
    term =
          ("> " >> parseIdentQuery >>= \q -> return $ ScriptTerminal q pickChoiceAct)
      <|> ("? " >> parseIdentQuery >>= \q -> return $ ScriptTerminal q matchAnyAct)

    p = do
      header <- parseIdentQuery
      return (L.IndentMany Nothing (return . (header, )) parseScriptStep)

parseScriptSteps :: Parser [ScriptStep]
parseScriptSteps = parseScriptStep `P.sepBy` scn


newtype ScriptParseError = ScriptParseError String
  deriving Show

-- This collects prefixes of "empty" script blocks and adds them as a prefix to
-- the first non-empty script block.
-- e.g.:
-- A
--  B
--  C
--    D
--    E
--  F
-- turns into
-- [[A,B,C,D],[A,B,C,E], [A,F]]
stepsToQueries :: [ScriptStep] -> [([NodeIdentQuery], Maybe NodeFinalAction)]
stepsToQueries s_outer = go [] s_outer
  where
    go :: [NodeIdentQuery] -> [ScriptStep] -> [([NodeIdentQuery], Maybe NodeFinalAction)]
    go [] [] = []
    go acc (ScriptBlock q []:xs) = go (q:acc) xs
    go acc (ScriptBlock q s:xs) = (do
      (qs,fin) <- go [] s
      return (reverse acc ++ (q:qs), fin)) ++ go [] xs
    go acc (ScriptTerminal q fin:xs) = (reverse acc ++ [q], Just fin):(go [] xs)
    go acc [] = [(acc, Nothing)]

mkNodeQuery :: ([NodeIdentQuery], Maybe NodeFinalAction) -> NodeQuery
mkNodeQuery (qs, fin) = NodeQuery qs (fromMaybe matchAnyAct fin)

stepsToScript :: [ScriptStep] -> Script
stepsToScript ss = Script $ map mkNodeQuery (stepsToQueries ss)

parseScript :: Parser Script
parseScript = do
  steps <- parseScriptSteps
  return $ stepsToScript steps

readScript :: FilePath -> IO (Either ScriptParseError Script)
readScript fp = do
  content <- T.readFile fp
  case P.parse parseScript fp content of
    Left err -> return $ Left $ ScriptParseError (P.errorBundlePretty err)
    Right a -> return $ Right a

-- TODO: Add the script itself to the TraceTree in order to track progress,
-- rather than just printing here.
runScript :: forall l (k :: l). Script -> TraceTree k -> IO ()
runScript _ss@(Script s) t = do
  -- IO.putStrLn $ "Running script:" ++ (show ss)
  go s
  where
    go [] = return ()
    go (q:qs)  = do
      -- IO.putStrLn $ "Running query:" ++ (show q)
      result <- resolveQuery q t
      case result of
        Nothing -> putStrLn $ "Query failed: " ++ show q
        (Just (QueryResult _path _)) -> do
          -- IO.putStrLn $ "Query succeeded:" ++ (show path)
          go qs

attachToTraceTree :: Script -> SomeTraceTree k -> IO (SomeTraceTree k)
attachToTraceTree scr t = forkTraceTreeHook (runScript scr) t