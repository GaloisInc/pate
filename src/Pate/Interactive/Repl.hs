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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Pate.Interactive.Repl where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Ppr as TH

import qualified Options.Applicative as OA
import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import           Data.Maybe ( mapMaybe )
import           Control.Monad ( foldM )
import           Control.Monad.State ( MonadState, StateT, modify, get, gets, runStateT )
import qualified Control.Monad.IO.Class as IO

import           Data.Parameterized.Some
import           Data.Parameterized.Classes

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter.Render.Terminal as PPRT

import           Data.Parameterized.SymbolRepr ( SymbolRepr, KnownSymbol, knownSymbol, symbolRepr )


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
import qualified Pate.Interactive.ReplHelper as PIRH

import           Pate.TraceTree

import Unsafe.Coerce(unsafeCoerce)

import qualified Main as PM

-- | Defining a 'Show' instance for a type which depends on 'PS.ValidSym'
--   and 'PA.ValidArch'.
class ShowIfValid a where
  showIfValid :: Maybe (ValidSymArchRepr Sym Arch Sym Arch) -> a -> String

instance ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => ShowIfValid a where
  showIfValid repr a = case repr of
    Just ValidSymArchRepr -> show a
    Nothing -> "<<No Binary Loaded>>"

printFn :: ShowIfValid a => a -> IO ()
printFn a = runReplM @(ValidSymArchRepr Sym Arch Sym Arch) getValidRepr >>= \x ->
  IO.putStrLn (showIfValid x a)

promptFn :: [String] -> Int -> IO String
promptFn _ _ = execReplM printToplevel >> return "\n> "


instance IsTraceNode (k :: l) "toplevel" where
  type TraceNodeType k "toplevel" = ()
  prettyNode () () = "<Toplevel>"

data TraceNode sym arch nm where
  TraceNode :: forall nm sym arch. (PS.ValidSym sym, PA.ValidArch arch, IsTraceNode '(sym, arch) nm) => TraceNodeLabel nm -> (TraceNodeType '(sym, arch) nm) -> IO (TraceTree '(sym, arch)) -> TraceNode sym arch nm

data ReplState sym arch where
  ReplState :: 
    { replTree :: TraceTree '(sym, arch)
    , replNode :: Some (TraceNode sym arch)
    , replTags :: [TraceTag]
    -- path used to navigate to this tree node
    , replPrev :: [Some (TraceNode sym arch)]
    -- tags used to collect the 'next' results
    , replNextTags :: [TraceTag]
    , replNext :: [Some (TraceNode sym arch)]
    , replValidRepr :: ValidSymArchRepr sym arch sym arch
    } -> ReplState sym arch

data ValidSymArchRepr sym arch symExt archExt where
  ValidSymArchRepr :: (sym ~ symExt, arch ~ archExt, PA.ValidArch arch, PS.ValidSym sym) => ValidSymArchRepr sym arch symExt archExt

data ReplIOStore =
    NoTreeLoaded
  | forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => SomeReplState (ReplState sym arch)

newtype ReplM_ sym arch a = ReplM_ { unReplM :: (StateT (ReplState sym arch) IO a) }
  deriving ( Functor, Applicative, Monad, MonadState (ReplState sym arch), IO.MonadIO )

type ReplM sym arch a = (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a

runReplM :: forall a. (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a) -> IO (Maybe a)
runReplM f = do
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> return Nothing
    SomeReplState (st :: ReplState sym arch) -> do
      (a, st') <- runStateT (unReplM @sym @arch f) st
      IO.writeIORef ref (SomeReplState st')
      return $ Just a

execReplM :: (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch ()) -> IO ()
execReplM f = runReplM @() f >>= \case
  Just _ -> return ()
  Nothing -> IO.putStrLn "No tree loaded" >> return ()


ref :: IO.IORef ReplIOStore
ref = IO.unsafePerformIO (IO.newIORef NoTreeLoaded)

run :: String -> IO ()
run rawOpts = do
  PIRH.setLastRunCmd rawOpts
  opts <- OA.handleParseResult (OA.execParserPure OA.defaultPrefs PM.cliOptions (words rawOpts))
  result <- PM.runMain opts
  case result of
    (_, PV.SomeTraceTree tree) -> do
      IO.putStrLn "Loaded tree"
      let st = ReplState
            { replTree = tree
            , replNode = Some (TraceNode @"toplevel" () () (return tree))
            , replTags = [Summary]
            , replPrev = []
            , replNextTags = [Summary]
            , replNext = []
            , replValidRepr = ValidSymArchRepr
            }
      IO.writeIORef ref (SomeReplState st)
      execReplM updateNextNodes
    (err, _) -> do
      IO.writeIORef ref NoTreeLoaded
      IO.putStrLn $ "Verifier run failed:\n" ++ (show err)

rerun :: IO ()
rerun = do
  PIRH.getLastRunCmd >>= \case
    Just rawOpts -> do
      IO.putStrLn $ "run \"" ++ rawOpts ++ "\""
      run rawOpts
    Nothing -> IO.putStrLn "No previous run found"

printPretty :: PP.Doc PPRT.AnsiStyle -> ReplM sym arch ()
printPretty p = do
  let s = PP.layoutPretty PP.defaultLayoutOptions p
  IO.liftIO $ PPRT.renderIO IO.stdout s  

printTreeSummary :: ReplM sym arch ()
printTreeSummary = do
  t <- gets replTree
  let p = ppFullTraceTree [Summary] t
  printPretty p

addNextNodes ::
  forall nm sym arch.
  TraceTreeNode '(sym, arch) nm ->
  ReplM sym arch ()
addNextNodes node = isTraceNode node $ do
  tags <- gets replNextTags
  contents <- IO.liftIO $ viewTraceTreeNode node
  case nodeShownAt @'(sym,arch) @nm tags of
    True -> do
      let nextTrees = map (\((v, lbl), subtree) -> Some (TraceNode @nm lbl v subtree)) contents
      modify (\st -> st { replNext = (replNext st) ++ nextTrees })
    False -> return ()

updateNextNodes ::
  ReplM sym arch ()
updateNextNodes = do
  tags <- gets replTags
  t <- gets replTree
  nodes <- viewTraceTree t
  modify (\st -> st { replNext = [ ], replNextTags = tags })
  mapM_ (\(Some node) -> addNextNodes node) nodes
   

prettyNextNodes ::
  forall sym arch a.
  ReplM sym arch (PP.Doc a)
prettyNextNodes = do
  tags <- gets replNextTags
  nextNodes <- gets replNext
  
  let ppContents =
        map (\(Some ((TraceNode lbl v subtree) :: TraceNode sym arch nm)) ->
               case prettyNodeAt @'(sym, arch) @nm tags lbl v of
                 Just pp -> pp <+> "(" <> PP.pretty (show (knownSymbol @nm)) <> ")"
                 Nothing -> "<ERROR: Unexpected missing printer>"
            ) nextNodes
  return $ PP.vsep (map (\((idx :: Int), pp) -> PP.pretty idx <> ":" <+> pp) (zip [0..] ppContents))

printToplevel :: forall sym arch. ReplM sym arch ()
printToplevel = do
  nextNodes <- gets replNext
  pp <- case nextNodes of
    [] -> return "<No Subtrees>"
    _ -> prettyNextNodes
  printPretty pp


up :: IO ()
up = execReplM $ do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> IO.liftIO $ IO.putStrLn "At top level"
    (Some popped:prevNodes') -> do
      loadTraceNode popped
      modify $ \st -> st { replPrev = prevNodes' }

currentNode :: ReplM_ sym arch (Some (TraceNode sym arch))
currentNode = gets replNode

withCurrentNode :: (forall nm. IsTraceNode '(sym,arch) nm => TraceNode sym arch nm -> ReplM sym arch a) -> ReplM_ sym arch a
withCurrentNode f = do
  Some (node@TraceNode{}) <- currentNode
  f node


loadTraceNode :: TraceNode sym arch nm -> ReplM sym arch ()
loadTraceNode (node@(TraceNode lbl v nextTreeFn)) = do
  nextTree <- IO.liftIO nextTreeFn
  modify $ \st -> st
    { replTree = nextTree
    , replNode = Some node
    , replTags = replTags st
    , replPrev = replPrev st
    , replNextTags = []
    , replNext = []
    }
  updateNextNodes

goto' :: Int -> ReplM sym arch (Maybe (Some (TraceNode sym arch)))
goto' idx = do
  nextNodes <- gets replNext
  case idx < length nextNodes of
    True -> do
      Some nextNode <- return $ nextNodes !! idx
      lastNode <- currentNode
      loadTraceNode nextNode
      modify $ \st -> st { replPrev = lastNode : (replPrev st) }
      return $ Just (Some nextNode)
    False -> return Nothing

goto :: Int -> IO ()
goto idx = execReplM $ do
  goto' idx >>= \case
    Just _ -> return ()
    Nothing -> IO.liftIO $ IO.putStrLn "No such option"

gotoIndex :: forall sym arch. Integer -> ReplM sym arch String
gotoIndex idx = (goto' (fromIntegral idx)) >>= \case
  Just (Some ((TraceNode lbl v _) :: TraceNode sym arch nm)) ->
    return $ show (prettyNode @_ @'(sym, arch) @nm lbl v)
  Nothing -> return "No such option"

gotoIndexPure :: Integer -> String
gotoIndexPure idx = IO.unsafePerformIO $ 
  runReplM (gotoIndex idx) >>= \case
    Just s -> return s
    Nothing -> return "No tree loaded"
-- Hacks to export the arch and sym parameters to the toplevel

data Arch
data Sym

coerceValidRepr ::
  ValidSymArchRepr sym arch sym arch -> ValidSymArchRepr sym arch Sym Arch
coerceValidRepr repr = unsafeCoerce repr


coerceTraceNode :: ReplM_ sym arch (Some (TraceNode Sym Arch))
coerceTraceNode = do
  Some ((TraceNode lbl v subtree) :: TraceNode sym arch nm) <- currentNode
  repr <- gets replValidRepr
  ValidSymArchRepr <- return $ coerceValidRepr repr
  return $ Some (TraceNode @nm lbl v subtree)


getSomeNode :: IO (Some (TraceNode Sym Arch))
getSomeNode = runReplM @(Some (TraceNode Sym Arch)) coerceTraceNode >>= \case
  Just v -> return v
  Nothing -> fail "getSomeNode"

getValidRepr :: ReplM_ sym arch (ValidSymArchRepr Sym Arch Sym Arch)
getValidRepr = do
  repr <- gets replValidRepr
  ValidSymArchRepr <- return $ coerceValidRepr repr
  return $ ValidSymArchRepr

validRepr :: IO (ValidSymArchRepr Sym Arch Sym Arch)
validRepr = runReplM @(ValidSymArchRepr Sym Arch Sym Arch) getValidRepr >>= \case
  Just repr -> return repr
  Nothing -> fail "validRepr"

getNode :: forall nm. KnownSymbol nm => IO (TraceNode Sym Arch nm)
getNode = do
  Some (node@(TraceNode{}) :: TraceNode Sym Arch nm') <- getSomeNode
  case testEquality (knownSymbol @nm) (knownSymbol @nm') of
    Just Refl -> return node
    Nothing -> fail "getNode"


this :: TH.ExpQ
this = do
  node <- IO.liftIO getSomeNode
  tpName <- case node of
    Some (TraceNode{} :: TraceNode Sym Arch nm) -> return $ (TH.LitT (TH.StrTyLit (show (knownSymbol @nm))))
  [| IO.unsafePerformIO (getV @($( return tpName ))) |]

getV :: forall nm. KnownSymbol nm => IO (TraceNodeType '(Sym,Arch) nm)
getV = do
  Some ((TraceNode lbl v _) :: TraceNode Sym Arch nm') <- getSomeNode
  case testEquality (knownSymbol @nm) (knownSymbol @nm') of
    Just Refl -> return v
    Nothing -> fail "getV"

-- Hack to allow navigating by entering numbers into the repl
newtype GotoIndex = GotoIndex Integer

instance Num GotoIndex where
  fromInteger = GotoIndex

instance Show GotoIndex where
  show (GotoIndex i) = gotoIndexPure i

