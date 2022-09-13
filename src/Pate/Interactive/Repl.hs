{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Pate.Interactive.Repl where


import qualified Options.Applicative as OA
import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import           Data.Maybe ( mapMaybe )
import           Control.Monad ( foldM )
import           Control.Monad.Reader ( MonadReader, ReaderT, ask, asks, runReaderT )
import qualified Control.Monad.IO.Class as IO

import           Data.Parameterized.Some

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter.Render.Terminal as PPRT

import           Data.Parameterized.SymbolRepr ( SymbolRepr, knownSymbol, symbolRepr )


import qualified Pate.Arch as PA
import qualified Pate.Solver as PS
import qualified Pate.Binary as PBi
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Event as PE
import qualified Pate.Loader as PL
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification as PV
import qualified Pate.Equivalence.Error as PEE

import           Pate.TraceTree

import qualified Main as PM

data LoadedTraceTreeNode sym arch where
  LoadedTraceTreeNode :: (PA.ValidArch arch, PS.ValidSym sym, IsTraceNode '(sym,arch) nm) => SymbolRepr nm -> TraceNodeLabel nm -> TraceNodeType '(sym,arch) nm -> IO (TraceTree '(sym, arch)) -> LoadedTraceTreeNode sym arch

newtype NodeList = NodeList (forall sym arch. [LoadedTraceTreeNode sym arch])

instance IsTraceNode (k :: l) "toplevel" where
  type TraceNodeType k "toplevel" = ()
  prettyNode () () = "<Toplevel>"

data ReplEnv sym arch where
  ReplEnv :: forall nm sym arch. IsTraceNode '(sym, arch) nm =>
    { replTree :: TraceTree '(sym, arch)
    , replSymRepr :: SymbolRepr nm
    , replLabel :: TraceNodeLabel nm
    , replValue :: TraceNodeType '(sym,arch) nm
    , replTags :: [TraceTag]
    , replNext :: [LoadedTraceTreeNode sym arch]
    } -> ReplEnv sym arch

newtype ReplM_ sym arch a = ReplM_ { unReplM :: (ReaderT (ReplEnv sym arch) IO a) }
  deriving ( Functor, Applicative, Monad, MonadReader (ReplEnv sym arch), IO.MonadIO )

type ReplM sym arch a = (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a

runReplM :: forall a. (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a) -> IO (Maybe a)
runReplM f = do
  t <- IO.readIORef ref
  case t of
    NodeList ((LoadedTraceTreeNode repr lbl v (lt :: IO (TraceTree '(sym, arch)))):_) -> do
      lt' <- lt
      Just <$> runReaderT (unReplM @sym @arch f) (ReplEnv lt' repr lbl v [Summary])
    NodeList [] -> return Nothing

execReplM :: (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch ()) -> IO ()
execReplM f = runReplM @() f >>= \case
  Just _ -> return ()
  Nothing -> IO.putStrLn "No tree loaded" >> return ()

-- | The current trace tree stack. Navigating to subtrees pushes elements onto the stack
--   while going "back" pops elements off.
ref :: IO.IORef NodeList
ref = IO.unsafePerformIO (IO.newIORef (NodeList []))

-- | Representation of the current options for loading the next tree
nextRefs :: IO.IORef NodeList
nextRefs = IO.unsafePerformIO (IO.newIORef (NodeList []))

promptFn :: [String] -> Int -> IO String
promptFn _modules _promptNumber = execReplM printToplevel >> return "\n> "

run ::
  String -> IO ()
run rawOpts = do
  opts <- OA.handleParseResult (OA.execParserPure OA.defaultPrefs PM.cliOptions (words rawOpts))
  result <- PM.runMain opts
  case result of
    (_, PV.SomeTraceTree tree) -> do
      IO.putStrLn "Loaded tree"
      IO.writeIORef ref (NodeList [(LoadedTraceTreeNode (knownSymbol @"toplevel") () () (return tree))])
    (err, _) -> do
      IO.writeIORef ref (NodeList [])
      fail (show err)

printPretty :: PP.Doc PPRT.AnsiStyle -> ReplM sym arch ()
printPretty p = do
  let s = PP.layoutPretty PP.defaultLayoutOptions p
  IO.liftIO $ PPRT.renderIO IO.stdout s  

printTreeSummary :: ReplM sym arch ()
printTreeSummary = do
  t <- asks replTree
  let p = ppFullTraceTree [Summary] t
  printPretty p

prettySomeNode ::
  forall nm sym arch a.
  (Int, [PP.Doc a], [LoadedTraceTreeNode sym arch]) ->
  TraceTreeNode '(sym, arch) nm ->
  ReplM sym arch (Int, [PP.Doc a], [LoadedTraceTreeNode sym arch])
prettySomeNode (idx, prevpp, nextTrees) node = isTraceNode node $ do
  tags <- asks replTags
  contents <- IO.liftIO $ viewTraceTreeNode  node
  let shownContents =
        mapMaybe (\((v, lbl), subtree) -> case prettyNodeAt @'(sym, arch) @nm tags lbl v of
               Just pp -> Just (pp, (LoadedTraceTreeNode (knownSymbol @nm) lbl v subtree))
               Nothing -> Nothing) contents
  let pp = (map (\(idx' :: Int,(p, _)) -> PP.pretty idx' <> ":" <+> p) (zip [idx..] shownContents))
 
  return (idx + length shownContents, prevpp ++ pp, nextTrees ++ map snd shownContents)

printToplevel :: forall sym arch. ReplM sym arch ()
printToplevel = do
  t <- asks replTree
  nodes <- viewTraceTree t
  case nodes of
    [] -> withValue $ \(_ :: SymbolRepr nm) lbl v -> do
      let pp = prettyNode @_ @'(sym, arch) @nm lbl v
      printPretty pp
      IO.liftIO $ IO.writeIORef nextRefs []  
    _ -> do
      (_, pp, nextTrees) <- foldM (\idx (Some node) -> prettySomeNode idx node) (0,[],[]) nodes
      printPretty (PP.vsep pp)
      IO.liftIO $ IO.writeIORef nextRefs nextTrees 

withValue ::
  (forall nm.  IsTraceNode '(sym,arch) nm => SymbolRepr nm -> TraceNodeLabel nm -> TraceNodeType '(sym,arch) nm -> ReplM sym arch a) ->
  ReplM sym arch a
withValue f = do
  ReplEnv _ repr lbl v _ <- ask
  f repr lbl v

back :: IO ()
back = do
  trees <- IO.readIORef ref
  case trees of
    [] -> IO.putStrLn "No tree loaded"
    [_] -> IO.putStrLn "At top level"
    (_:trees') -> IO.writeIORef ref trees'


goto' :: Int -> ReplM sym arch (LoadedTraceTreeNode sym arch)
goto' idx = do
  nextTrees <- IO.readIORef nextRefs
  case idx < length nextTrees of
    True -> do
      let nextTree = nextTrees !! idx
      IO.modifyIORef' ref (\t -> nextTree : t)
      return $ Just nextTree
    False -> return Nothing

goto :: Int -> IO ()
goto idx = goto' idx >>= \case
  Just _ -> return ()
  Nothing -> IO.putStrLn "No such option"

gotoIndex :: forall sym arch. Integer -> ReplM sym arch String
gotoIndex idx = (IO.liftIO $ goto' (fromIntegral idx)) >>= \case
  Just (LoadedTraceTreeNode (nm :: SymbolRepr nm) lbl v _) -> do
    tags <- asks replTags
    let pp = prettyNodeAt @'(sym, arch) @nm tags lbl v
    return $ show pp
  Nothing -> return "No such option"

gotoIndexPure :: Integer -> String
gotoIndexPure idx = IO.unsafePerformIO $ 
  runReplM (gotoIndex idx) >>= \case
    Just s -> return s
    Nothing -> return "No tree loaded"

-- Hack to allow navigating by entering numbers into the repl
newtype GotoIndex = GotoIndex Integer

instance Num GotoIndex where
  fromInteger = GotoIndex

instance Show GotoIndex where
  show (GotoIndex i) = gotoIndexPure i


