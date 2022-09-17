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


module Repl where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Ppr as TH

import qualified Options.Applicative as OA
import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import qualified Control.Concurrent as IO
import           Data.Maybe ( mapMaybe )
import           Control.Monad ( foldM )
import           Control.Monad.State ( MonadState, StateT, modify, get, gets, runStateT )
import qualified Control.Monad.IO.Class as IO
import           Data.Kind ( Type )

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
import qualified Pate.Monad.Environment as PME
import qualified Pate.Loader as PL
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Verification as PV
import qualified Pate.Equivalence.Error as PEE
import qualified ReplHelper as PIRH

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
promptFn _ _ = execReplM (updateNextNodes >> printToplevel) >> return ""


data TraceNode sym arch nm where
  TraceNode :: forall nm sym arch. (PS.ValidSym sym, PA.ValidArch arch, IsTraceNode '(sym, arch) nm) => TraceNodeLabel nm -> (TraceNodeType '(sym, arch) nm) -> TraceTree '(sym, arch) -> TraceNode sym arch nm

data ReplState sym arch where
  ReplState :: 
    { replNode :: Some (TraceNode sym arch)
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
  -- main thread has started but hasn't yet produced a tree
  | WaitingForToplevel IO.ThreadId SomeTraceTree
  -- we've started navigating the resulting tree
  | forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => SomeReplState (ReplState sym arch)


newtype ReplM_ sym arch a = ReplM_ { unReplM :: (StateT (ReplState sym arch) IO a) }
  deriving ( Functor, Applicative, Monad, MonadState (ReplState sym arch), IO.MonadIO )

type ReplM sym arch a = (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a

runReplM :: forall a. (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a) -> IO (Maybe a)
runReplM f = do
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> IO.putStrLn "No tree loaded" >> return Nothing
    WaitingForToplevel _ tree -> loadSomeTree tree >>= \case
      True -> runReplM f
      False -> IO.putStrLn "Waiting for verifier.." >> return Nothing
    SomeReplState (st :: ReplState sym arch) -> do
      (a, st') <- runStateT (unReplM @sym @arch f) st
      IO.writeIORef ref (SomeReplState st')
      return $ Just a

execReplM :: (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch ()) -> IO ()
execReplM f = runReplM @() f >> return ()


ref :: IO.IORef ReplIOStore
ref = IO.unsafePerformIO (IO.newIORef NoTreeLoaded)

loadSomeTree ::
  SomeTraceTree -> IO Bool
loadSomeTree topTraceTree = do
  let doFail = IO.putStrLn "Unexpected tree structure" >> return False
  -- we assume that root entry of the tree contains evidence that the
  -- trace tree parameter (as determined during runtime) satisfies the
  -- necessary validity constraints to form a 'ReplState'
  viewSomeTraceTree topTraceTree (return False) $ \(toptree :: TraceTree k) -> do
      (IO.liftIO $ viewTraceTree toptree) >>= \case
        [(Some (node :: TraceTreeNode k nm))] -> isTraceNode node $ do
          case testEquality (knownSymbol @nm) (knownSymbol @"toplevel") of
            Nothing -> doFail
            Just Refl -> viewTraceTreeNode node >>= \case
              [((toplevel@PME.ValidRepr,_), tree)] -> do
                IO.putStrLn "Loaded tree"
                let st = ReplState
                      { replNode = Some (TraceNode @"toplevel" () toplevel tree)
                      , replTags = [Summary]
                      , replPrev = []
                      , replNextTags = [Summary]
                      , replNext = []
                      , replValidRepr = ValidSymArchRepr
                      }
                IO.writeIORef ref (SomeReplState st)
                execReplM updateNextNodes
                return True
              _ -> doFail
        _ -> doFail  

run :: String -> IO ()
run rawOpts = do
  PIRH.setLastRunCmd rawOpts
  opts <- OA.handleParseResult (OA.execParserPure OA.defaultPrefs PM.cliOptions (words rawOpts))
  topTraceTree <- someTraceTree
  tid <- IO.forkFinally (PM.runMain topTraceTree opts) $ \case
    Left err -> IO.putStrLn $ "Verifier failed: " ++ show err
    Right _a -> return ()
  IO.writeIORef ref (WaitingForToplevel tid topTraceTree)

rerun :: IO ()
rerun = do
  PIRH.getLastRunCmd >>= \case
    Just rawOpts -> do
      IO.putStrLn $ ":run \"" ++ rawOpts ++ "\""
      run rawOpts
    Nothing -> IO.putStrLn "No previous run found"

printPretty :: PP.Doc PPRT.AnsiStyle -> ReplM sym arch ()
printPretty p = do
  let s = PP.layoutPretty PP.defaultLayoutOptions p
  IO.liftIO $ PPRT.renderIO IO.stdout s  


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
  (Some (TraceNode _ _ t))  <- gets replNode
  nodes <- IO.liftIO $ viewTraceTree t
  modify (\st -> st { replNext = [ ], replNextTags = tags })
  mapM_ (\(Some node) -> addNextNodes node) nodes

addStatusTag :: NodeStatus -> PP.Doc a -> PP.Doc a
addStatusTag st p = case ppStatusTag st of
  Just pst -> p <+> "(" <> pst <> ")"
  Nothing -> p

ppStatusTag :: NodeStatus -> Maybe (PP.Doc a)
ppStatusTag st = case st of
  NodeStatus False -> Just "*"
  NodeError _ False -> Just "*x"
  NodeError _ True -> Just "x"
  _ -> Nothing

prettyNextNodes ::
  forall sym arch a.
  ReplM sym arch (PP.Doc a)
prettyNextNodes = do
  tags <- gets replNextTags
  nextNodes <- gets replNext
  
  ppContents <- 
       mapM (\(Some ((TraceNode lbl v subtree) :: TraceNode sym arch nm)) ->
               case prettyNodeAt @'(sym, arch) @nm tags lbl v of
                 Just pp -> do
                   b <- IO.liftIO $ getTreeStatus subtree
                   return $ addStatusTag b $ pp <+> "(" <> PP.pretty (show (knownSymbol @nm)) <> ")"
                 Nothing -> return "<ERROR: Unexpected missing printer>"
            ) nextNodes
  return $ PP.vsep (map (\((idx :: Int), pp) -> PP.pretty idx <> ":" <+> pp) (zip [0..] ppContents))

printToplevel :: forall sym arch. ReplM sym arch ()
printToplevel = do
  nextNodes <- gets replNext
  (Some (TraceNode _ _ t))  <- gets replNode
  st <- IO.liftIO $ getTreeStatus t
  let prompt = case ppStatusTag st of
        Just pst -> (pst <+> ">")
        Nothing -> ">"
    
  pp <- case nextNodes of
    [] -> return $ PP.vsep [ "<<No Subtrees>>", prompt ]
    _ -> do
      p <- prettyNextNodes
      return $ PP.vsep [ p, prompt ]

  printPretty pp


up :: IO ()
up = execReplM $ do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> IO.liftIO $ IO.putStrLn "<<At top level>>"
    (Some popped:prevNodes') -> do
      loadTraceNode popped
      modify $ \st -> st { replPrev = prevNodes' }

top :: IO ()
top = execReplM $ do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> IO.liftIO $ IO.putStrLn "<<At top level>>"
    _ -> do
      Some init <- return $ last prevNodes
      loadTraceNode init
      modify $ \st -> st { replPrev = [] }

status :: IO ()
status = execReplM $ do
  (Some (TraceNode _ _ t))  <- gets replNode
  st <- IO.liftIO $ getTreeStatus t
  let msg = case st of
        NodeStatus False -> "Unfinished"
        NodeStatus True -> "Success"
        NodeError msg _ -> "Error: " ++ msg
  IO.liftIO $ IO.putStrLn msg


showTag :: TraceTag -> IO ()
showTag tag = execReplM $ do
  modify $ \st -> st { replTags = tag:(replTags st) }

hideTag :: TraceTag -> IO ()
hideTag tag = execReplM $ do
  modify $ \st -> st { replTags = [ t | t <- (replTags st), t /= tag] }

currentNode :: ReplM_ sym arch (Some (TraceNode sym arch))
currentNode = gets replNode

fetchNode :: Int -> ReplM_ sym arch (Maybe (Some (TraceNode sym arch)))
fetchNode i = do
  nextNodes <- gets replNext
  case 0 <= i && i < length nextNodes of
    True -> return $ Just (nextNodes !! i)
    False -> return Nothing

withCurrentNode :: (forall nm. IsTraceNode '(sym,arch) nm => TraceNode sym arch nm -> ReplM sym arch a) -> ReplM_ sym arch a
withCurrentNode f = do
  Some (node@TraceNode{}) <- currentNode
  f node


loadTraceNode :: TraceNode sym arch nm -> ReplM sym arch ()
loadTraceNode node = do
  modify $ \st -> st
    { replNode = Some node
    , replNextTags = []
    , replNext = []
    }
  updateNextNodes

goto' :: Int -> ReplM sym arch (Maybe (Some (TraceNode sym arch)))
goto' idx = do
  fetchNode idx >>= \case
    Just (Some nextNode) -> do
      lastNode <- currentNode
      loadTraceNode nextNode
      modify $ \st -> st { replPrev = lastNode : (replPrev st) }
      return $ Just (Some nextNode)
    Nothing -> return Nothing
      
wait :: Int -> IO ()
wait idx = execReplM $ do
    updateNextNodes
    goto' idx >>= \case
      Just _ -> return ()
      Nothing -> do
        Some (TraceNode _ _ t) <- gets replNode
        st <- IO.liftIO $ getTreeStatus t
        case isFinished st of
          True -> IO.liftIO $ IO.putStrLn "No such option" >> return ()
          False -> do
            nextNodes <- gets replNext
            IO.liftIO (IO.putStrLn $ (show (length nextNodes)) ++ "/" ++ show idx)
            IO.liftIO $ (IO.threadDelay 1000000 >> wait idx)

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


coerceTraceNode :: forall nm sym arch. TraceNode sym arch nm -> ReplM_ sym arch (TraceNode Sym Arch nm)
coerceTraceNode (TraceNode lbl v subtree) = do
  repr <- gets replValidRepr
  ValidSymArchRepr <- return $ coerceValidRepr repr
  return $ TraceNode @nm lbl v subtree

fetchSomeNode :: Maybe Int -> IO (Some (TraceNode Sym Arch))
fetchSomeNode mi = do
  r <- runReplM @(Maybe (Some (TraceNode Sym Arch))) $ do
    case mi of
      Just i -> fetchNode i >>= \case
        Just (Some tr) -> (Just . Some) <$> coerceTraceNode tr
        Nothing -> return Nothing
      Nothing -> do
        Some tr <- currentNode
        (Just . Some) <$> coerceTraceNode tr
  case r of
    Just (Just v) -> return v
    _ | Just i <- mi -> fail $ "No such node: " ++ show i
    _ -> fail "fetchSomeNode"

getValidRepr :: ReplM_ sym arch (ValidSymArchRepr Sym Arch Sym Arch)
getValidRepr = do
  repr <- gets replValidRepr
  ValidSymArchRepr <- return $ coerceValidRepr repr
  return $ ValidSymArchRepr

validRepr :: IO (ValidSymArchRepr Sym Arch Sym Arch)
validRepr = runReplM @(ValidSymArchRepr Sym Arch Sym Arch) getValidRepr >>= \case
  Just repr -> return repr
  Nothing -> fail "validRepr"

this :: TH.ExpQ
this = fetch' Nothing

fetch :: Int -> TH.ExpQ
fetch i = fetch' (Just i)

fetch' :: Maybe Int -> TH.ExpQ
fetch' mi = do
  node <- IO.liftIO $ fetchSomeNode mi
  tpName <- case node of
    Some (TraceNode{} :: TraceNode Sym Arch nm) -> return $ (TH.LitT (TH.StrTyLit (show (knownSymbol @nm))))
  [| IO.unsafePerformIO (fetchV @($( return tpName )) mi) |]  

fetchV :: forall nm. Maybe Int -> KnownSymbol nm => IO (TraceNodeType '(Sym,Arch) nm)
fetchV mi = do
  Some ((TraceNode _lbl v _) :: TraceNode Sym Arch nm') <- fetchSomeNode mi
  case testEquality (knownSymbol @nm) (knownSymbol @nm') of
    Just Refl -> return v
    Nothing -> fail "fetchV"

-- Hack to allow navigating by entering numbers into the repl
newtype GotoIndex = GotoIndex Integer

instance Num GotoIndex where
  fromInteger = GotoIndex

instance Show GotoIndex where
  show (GotoIndex i) = gotoIndexPure i

