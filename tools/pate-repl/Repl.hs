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

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Repl where

import qualified Language.Haskell.TH as TH

import qualified System.Console.ANSI as ANSI
import qualified Options.Applicative as OA
import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import qualified Control.Concurrent as IO
import           Control.Monad ( forM )
import           Control.Monad.State ( MonadState, StateT, modify, gets, runStateT, get, put )
import qualified Control.Monad.IO.Class as IO
import           Data.Proxy
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import qualified Data.Text.Lazy as TextL
import           Text.Read (readMaybe)
import           System.Exit
import           System.Environment

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.List.Split (splitOn)
import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter.Render.Terminal as PPRT
import qualified Prettyprinter.Render.Text as PPText

import           Data.Parameterized.SymbolRepr ( KnownSymbol, knownSymbol, SymbolRepr, symbolRepr )


import qualified Pate.Arch as PA
import qualified Pate.ArchLoader as PAL
import qualified Pate.Config as PC
import qualified Pate.Solver as PS
import qualified Pate.Script as PSc
import qualified Pate.Equivalence as PEq
import qualified Pate.CLI as CLI
import qualified Pate.Loader as PL
import qualified ReplHelper as PIRH
import qualified ReplBase
import           ReplBase ( Sym, Arch )

import           Pate.TraceTree hiding (asChoice)
import           What4.Expr.Builder as W4B

import Unsafe.Coerce(unsafeCoerce)

import qualified Output as PO

maxSubEntries :: Int
maxSubEntries = 5

initFns :: IO ()
initFns = do
  IO.writeIORef ReplBase.printFnRef (ReplBase.SomePrintFn printFn)
  IO.writeIORef ReplBase.promptFnRef promptFn

-- | Defining a 'Show' instance for a type which depends on 'PS.ValidSym'
--   and 'PA.ValidArch'.
printFn :: ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => a -> IO ()
printFn a = do
  r <- runReplM $ do
    ValidSymArchRepr{} <- getValidRepr
    let str = show a
    case readMaybe @Integer str of
      Just i -> goto' (fromIntegral i) >>= \case
        Just{} -> return ()
        Nothing -> PO.printErrLn "No such option"
      Nothing -> PO.printBreak
  case r of
    Just () -> return ()
    Nothing -> PO.printMsgLn "<<No Binary Loaded>>"

valid :: ((PS.ValidSym Sym, PA.ValidArch Arch) => IO a) -> IO a
valid f = do
  ValidSymArchRepr{} <- validRepr
  f

sym :: Sym
sym = IO.unsafePerformIO $ do
  ValidSymArchRepr sym _ <- validRepr
  return sym


arch :: Proxy Arch
arch = IO.unsafePerformIO $ do
  ValidSymArchRepr _ (_arch :: PA.SomeValidArch arch) <- validRepr
  return $ Proxy @arch

promptFn :: [String] -> Int -> IO String
promptFn _ _ = do
  tryKillWaitThread
  IO.readIORef waitThread >>= \case
    WaitThread _ gas | gas <= 0 -> execReplM updateNextNodes >> getPrompt
    WaitThread _ _gas -> return ""

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
    , replNext :: [(Int, Some (TraceNode sym arch))]
    , replValidRepr :: ValidSymArchRepr sym arch sym arch
    , replLastOptsPrinted :: String
    , replNesting :: Int
    , replSubTreeNodes :: [Text.Text]
    -- which nodes are considered "subtrees" and should have
    -- their contents displayed by default
    } -> ReplState sym arch

data ValidSymArchRepr sym arch symExt archExt where
  ValidSymArchRepr :: (sym ~ symExt, arch ~ archExt, PA.ValidArch arch, PS.ValidSym sym) => sym -> PA.SomeValidArch arch -> ValidSymArchRepr sym arch symExt archExt

data ReplIOStore =
    NoTreeLoaded
  -- main thread has started but hasn't yet produced a tree
  | WaitingForToplevel IO.ThreadId (SomeTraceTree PA.ValidRepr) LoadOpts
  -- we've started navigating the resulting tree
  | forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => SomeReplState IO.ThreadId (ReplState sym arch)

data LoadOpts = LoadOpts { loadJSONMode :: Bool }

newtype ReplM_ sym arch a = ReplM_ { unReplM :: (StateT (ReplState sym arch) IO a) }
  deriving ( Functor, Applicative, Monad, MonadState (ReplState sym arch), IO.MonadIO )

type ReplM sym arch a = (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a

runReplM :: forall a. (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a) -> IO (Maybe a)
runReplM f = do
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> return Nothing
    WaitingForToplevel tid tree opts -> loadSomeTree tid tree opts >>= \case
      True -> runReplM f
      False -> return Nothing
    SomeReplState tid (st :: ReplState sym arch) -> do
      (a, st') <- runStateT (unReplM @sym @arch f) st
      IO.writeIORef ref (SomeReplState tid st')
      return $ Just a

execReplM :: (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch ()) -> IO ()
execReplM f = runReplM @() f >> return ()


retrieveOldRef :: IO ()
retrieveOldRef = IO.readIORef PIRH.anyRef >>= \case
  Nothing -> PO.printErr "No old ref"
  Just x -> IO.writeIORef ref (PIRH.fromAnything x)

stashThisRef :: IO ()
stashThisRef = do
  x <- IO.readIORef ref
  IO.writeIORef PIRH.anyRef (Just (PIRH.Anything x))

ref :: IO.IORef ReplIOStore
ref = IO.unsafePerformIO (IO.newIORef NoTreeLoaded)

data WaitThread = WaitThread (Maybe IO.ThreadId) Int

decrementWait :: WaitThread -> WaitThread
decrementWait (WaitThread mtid gas) = WaitThread mtid (gas - 1)

waitThread :: IO.IORef WaitThread
waitThread = IO.unsafePerformIO (IO.newIORef (WaitThread Nothing 0))


finalResult :: IO.IORef (Maybe (Either String PEq.EquivalenceStatus))
finalResult = IO.unsafePerformIO (IO.newIORef Nothing)

defaultSubTreeNodes :: [Text.Text]
defaultSubTreeNodes = ["subtree", "choiceTree", "function_name", "debug_tree"]

isSubTreeNode ::
  forall sym arch nm.
  TraceNode sym arch nm ->
  ReplM sym arch Bool
isSubTreeNode (TraceNode{}) = do
  strees <- gets replSubTreeNodes
  return $ symbolRepr (knownSymbol @nm) `elem` strees

loadSomeTree ::
  IO.ThreadId -> SomeTraceTree PA.ValidRepr -> LoadOpts -> IO Bool
loadSomeTree tid topTraceTree opts = do
  viewSomeTraceTree topTraceTree (return False) $ \(PA.ValidRepr sym arch) (toptree :: TraceTree k) -> do
      let st = ReplState
            { replNode = Some (TraceNode @"toplevel" () () toptree)
            , replTags = dtags
            , replPrev = []
            , replNextTags = dtags
            , replNext = []
            , replValidRepr = ValidSymArchRepr sym arch
            , replLastOptsPrinted = ""
            , replNesting = 0
            , replSubTreeNodes = strees
            }
          strees = defaultSubTreeNodes
          dtags = [Simplified]
      IO.writeIORef ref (SomeReplState tid st)
      execReplM updateNextNodes
      return True

instance IsTraceNode k "toplevel" where
  type TraceNodeType k "toplevel" = ()
  prettyNode () () = "<Toplevel>"
  nodeTags = mkTags @k @"toplevel" [Simplified,Summary]

scriptAddToplevel :: PSc.Script -> PSc.Script
scriptAddToplevel (PSc.Script sc) = PSc.Script (map go sc)
  where
    go :: NodeQuery -> NodeQuery
    go (NodeQuery qs) = NodeQuery ((QueryString "<Toplevel>"):qs)

run :: String -> IO ()
run rawOpts = do
  PIRH.setLastRunCmd rawOpts
  let optsList = filter (\s -> s /= "") $ map (concat . map (\case '\\' -> []; x -> [x])) (splitOn "\\n" rawOpts)
  case OA.execParserPure OA.defaultPrefs CLI.cliOptions optsList of
    OA.Success opts -> do
      setJSONMode $ CLI.jsonToplevel opts
      topTraceTree' <- someTraceTree
      let cfg' = CLI.mkRunConfig PAL.archLoader opts
      cfgE <- case PC.cfgScriptPath (PL.verificationCfg cfg') of
        Nothing -> return $ Right $ PL.setTraceTree topTraceTree' cfg'
        Just fp -> PSc.readScript fp >>= \case
          Left err -> return $ Left err
          Right sc' -> do
            let sc = scriptAddToplevel sc'
            tt' <- forkTraceTreeHook (PSc.runScript sc) topTraceTree'
            return $ Right $ PL.setTraceTree tt' cfg'
      case cfgE of
        Left err -> PO.printErrLn (PP.viaShow err)
        Right cfg -> do
          let topTraceTree = PC.cfgTraceTree (PL.verificationCfg cfg) 
          tid <- IO.forkFinally (PL.runEquivConfig cfg) $ \case
            Left err -> do
              killWaitThread
              let msg = show err
              case msg of
                "thread killed" -> return ()
                _ -> do
                  IO.writeIORef ref NoTreeLoaded
                  IO.hPutStrLn IO.stderr (show err)
                  exitFailure
              IO.writeIORef finalResult (Just (Left msg))
            Right a -> IO.writeIORef finalResult (Just (Right a))
          IO.writeIORef ref (WaitingForToplevel tid topTraceTree (LoadOpts (CLI.jsonToplevel opts)))
          -- give some time for the verifier to start
          IO.threadDelay 100000
          wait_initial
    OA.Failure failure -> do
      progn <- getProgName
      let (msg, exit) = OA.renderFailure failure progn
      case exit of
        ExitSuccess -> PO.printMsgLn (PP.pretty msg)
        _           -> PO.printErrLn (PP.pretty msg)
    _ -> return ()

-- exit if no tree is loaded
checkAlive :: IO String
checkAlive = do
  IO.readIORef ref >>= \case
    NoTreeLoaded -> return ":! kill -6 $PPID\n"
    _ -> return "" -- IO.hPutStrLn IO.stdin "\"asdf\"" >> return ""

rerun :: IO ()
rerun = do
  PIRH.getLastRunCmd >>= \case
    Just rawOpts -> do
      PO.printMsgLn $ ":run \"" <> PP.pretty rawOpts <> "\""
      run rawOpts
    Nothing -> PO.printMsgLn "No previous run found"



truncateSubNodes :: [(Int, Some (TraceNode sym arch))] -> ReplM sym arch [(Int, Some (TraceNode sym arch))]
truncateSubNodes next = do
  let (shown,hidden) = splitAt (maxSubEntries-1) next
  case hidden of
    ((idx,n):_) -> return $ (shown ++ [((-1) * idx,n)])
    _ -> return shown

addNextNodes ::
  forall nm sym arch.
  TraceTreeNode '(sym, arch) nm ->
  ReplM sym arch ()
addNextNodes node = isTraceNode node $ do
  tags <- gets replNextTags
  contents <- IO.liftIO $ viewTraceTreeNode node
  nesting <- gets replNesting
  let nextTrees' = map (\((v, lbl), subtree) -> (nesting, Some (TraceNode @nm lbl v subtree))) contents

  nextTrees <- case nesting > 0 of
    True -> truncateSubNodes nextTrees'
    False -> return $ nextTrees'
  (IO.liftIO $ nodeShownAt tags node) >>= \case
    True -> do
      nextSubs <- fmap concat $ forM nextTrees $ \(n, Some nextNode) -> do
        prevNodes <- gets replPrev
        next <- maybeSubNodes nextNode (return []) (gets replNext)
        issub <- isSubTreeNode nextNode
        case (issub, next) of

          (True, []) -> return []
          _ -> return $ [(n, Some nextNode)] ++ next
      modify (\st -> st { replNext = (replNext st) ++ nextSubs })
    False -> return ()

-- | Run the sub-computation as if the given node is the current node,
--   restoring the state afterwards
withNode ::
  TraceNode sym arch nm ->
  ReplM sym arch a ->
  ReplM sym arch a
withNode nd f = do
  oldst <- get
  modify $ \st -> st {replNesting = (replNesting st) + 1}
  loadTraceNode nd
  a <- f
  put oldst
  return a

updateNextNodes ::
  ReplM sym arch ()
updateNextNodes = do
  tags <- gets replTags
  (Some (TraceNode _ _ t))  <- gets replNode
  nodes <- IO.liftIO $ viewTraceTree t
  modify (\st -> st { replNext = [ ], replNextTags = tags })
  mapM_ (\(Some node) -> addNextNodes node) nodes

mkStatusTag :: NodeStatus -> Maybe (PP.Doc a)
mkStatusTag st = case ppStatusTag st of
  Just pst -> Just $ "(" <> pst <> ")"
  Nothing -> Nothing

ppSuffix :: Int -> NodeStatus -> SymbolRepr nm -> ReplM sym arch (Maybe (PP.Doc a))
ppSuffix nesting s nm = do
  tags <- gets replTags
  case tags of
    [Simplified] -> return $ mkStatusTag s
    _ | Just s' <- mkStatusTag s -> return $ Just $ s' <+> "(" <> PP.pretty (show nm) <> ")"
    _ -> return $ Just $ "(" <> PP.pretty (show nm) <> ")"
  {-
  case nesting < 0 of
    True -> return $ pp' <> PP.line <> "... <more results>"
    False -> return pp'
  -}

ppStatusTag :: NodeStatus -> Maybe (PP.Doc a)
ppStatusTag st = case st of
  _ | isBlockedStatus st -> Just "?"
  NodeStatus StatusSuccess False _ -> Just "*"
  NodeStatus (StatusWarning _) False _ -> Just "!*"
  NodeStatus (StatusWarning _) True _ -> Just "!"
  NodeStatus (StatusError _) False _ -> Just "*x"
  NodeStatus (StatusError _) True _ -> Just "x"
  NodeStatus StatusSuccess True _ -> Nothing

maybeSubNodes ::
  forall sym arch nm a.
  TraceNode sym arch nm ->
  ReplM sym arch a ->
  ReplM sym arch a ->
  ReplM sym arch a
maybeSubNodes nd@(TraceNode lbl v subtree) g f = do
  prevNodes <- gets replPrev
  isSubTreeNode nd >>= \case
    True -> withNode nd $ f
    False -> do
      mr <- withNode nd $ do
        nextNodes <- gets replNext
        case length nextNodes == 1 of
          True | (not (null prevNodes)) -> Just <$> f
          _ -> return Nothing
      case mr of
        Just a -> return a
        Nothing -> g






prettyNextNodes ::
  forall sym arch.
  Int ->
  Bool ->
  ReplM sym arch PO.Output
prettyNextNodes startAt onlyFinished = do
  tags <- gets replNextTags
  nextNodes <- gets replNext
  
  ppContents' <- 
       mapM (\(nesting, Some (nd@(TraceNode lbl v subtree) :: TraceNode sym arch nm)) -> do
                b <- IO.liftIO $ getTreeStatus subtree
                case prettyNodeAt @'(sym, arch) @nm tags lbl v of
                  Just pp -> do
                    suf <- ppSuffix nesting b (knownSymbol @nm)
                    let indent = abs(nesting)*2
                    return $ PO.OutputElem 
                      { PO.outIdx = 0
                      , PO.outIndent = indent
                      , PO.outPP = pp
                      , PO.outFinished = isFinished b
                      , PO.outSuffix = suf
                      , PO.outMoreResults = nesting < 0
                      , PO.outJSON = jsonNode @_ @'(sym, arch) @nm lbl v
                      }
                    {-
                    maybeSubNodes nd ()) $ do
                      subpp <- prettyNextNodes 0 onlyFinished
                      return $ (isFinished b, PP.vsep [pp', PP.indent 2 subpp])
                    -}
                  Nothing -> return $ PO.OutputElem 
                      { PO.outIdx = 0
                      , PO.outIndent = 0
                      , PO.outPP = "<ERROR: Unexpected missing printer>"
                      , PO.outFinished = isFinished b
                      , PO.outSuffix = Nothing
                      , PO.outMoreResults = nesting < 0
                      , PO.outJSON = jsonNode @_ @'(sym, arch) @nm lbl v
                      }
              ) nextNodes

  let ppContents = case onlyFinished of
        True -> takeWhile PO.outFinished ppContents'
        False -> ppContents'
  return $ PO.outputList (drop startAt (map (\(idx,e) -> e { PO.outIdx = idx }) (zip [0..] ppContents)))
  -- return $ PP.vsep (drop startAt (map (\((idx :: Int), pp) -> PP.pretty idx <> ":" <+> pp) (zip [0..] ppContents)))

getPrompt :: IO String
getPrompt = PO.hasStdOut >>= \case
  True -> do
    mst <- runReplM $ do
      (Some (TraceNode _ _ t))  <- gets replNode
      IO.liftIO $ getTreeStatus t
    case mst of
      Just st | Just pst <- ppStatusTag st -> return $ (show (pst <> ">"))
      _ -> return ">"
  False -> return ""

ls' :: forall sym arch. ReplM sym arch ()
ls' = do
  updateNextNodes
  p <- prettyNextNodes 0 False
  (Some ((TraceNode lbl v _) :: TraceNode sym arch nm)) <- gets replNode
  tags <- gets replTags
  let thisPretty = prettyDetailAt @'(sym, arch) @nm tags lbl v
  let p' = PO.tagOutput (Just thisPretty) (Just (symbolRepr (knownSymbol @nm))) p
  PO.printOutput p'
  PO.printBreak

ls :: IO ()
ls = execReplM ls'

stop :: IO ()
stop = do
  IO.readIORef ref >>= \case
    NoTreeLoaded -> return ()
    WaitingForToplevel tid _ _ -> IO.killThread tid
    SomeReplState tid _ -> IO.killThread tid

up :: IO ()
up = execReplM $ (up' >> ls')

up' :: ReplM sym arch ()
up' = do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> PO.printMsgLn "<<At top level>>"
    (Some popped:prevNodes') -> do
      loadTraceNode popped
      modify $ \st -> st { replPrev = prevNodes' }

top :: IO ()
top = execReplM $ (top' >> ls')

top' :: ReplM sym arch ()
top' = do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> PO.printMsgLn "<<At top level>>"
    _ -> do
      Some init <- return $ last prevNodes
      loadTraceNode init
      modify $ \st -> st { replPrev = [] }

status' :: Maybe Int -> IO ()
status' mlimit = do
  tr <- IO.readIORef ref
  case tr of
    NoTreeLoaded -> PO.printMsgLn "No tree loaded"
    WaitingForToplevel{} -> do
      fin <- IO.liftIO $ IO.readIORef finalResult
      case fin of
        Just r -> PO.printMsgLn (PP.pretty (show r))
        _ -> PO.printMsgLn "Waiting for verifier..."
    SomeReplState {} -> execReplM $ do
      (Some (TraceNode _ _ t))  <- gets replNode
      st <- IO.liftIO $ getTreeStatus t
      case st of
        _ | isBlockedStatus st -> PO.printMsgLn $ "Waiting for input.."
        NodeStatus (StatusWarning e) _ _ -> PO.printMsgLn $ "Warning: \n" <> (PP.pretty (chopMsg mlimit (show e)))
        NodeStatus (StatusError e) _ _ ->  PO.printMsgLn $ "Error: \n" <> (PP.pretty (chopMsg mlimit (show e)))
        NodeStatus StatusSuccess False _ ->  PO.printMsgLn $ "In progress.."
        NodeStatus StatusSuccess True _ -> PO.printMsgLn $ "Finalized"
      prevNodes <- gets replPrev
      fin <- IO.liftIO $ IO.readIORef finalResult
      case (prevNodes, fin) of
        ([], Just r) -> PO.printMsgLn (PP.viaShow r)
        _ -> return ()

full_status :: IO ()
full_status = status' Nothing

status :: IO ()
status = status' (Just 2000)

chopMsg :: Maybe Int -> String -> String
chopMsg Nothing msg = msg
chopMsg (Just limit) msg = take limit msg

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
    True -> return $ Just (snd $ nextNodes !! i)
    False -> return Nothing

withCurrentNode :: (forall nm. IsTraceNode '(sym,arch) nm => TraceNode sym arch nm -> ReplM sym arch a) -> ReplM_ sym arch a
withCurrentNode f = do
  Some (node@TraceNode{}) <- currentNode
  f node

loadTraceNode :: forall sym arch nm. TraceNode sym arch nm -> ReplM sym arch ()
loadTraceNode node = do
  modify $ \st -> st
    { replNode = Some node
    , replNextTags = []
    , replNext = []
    , replLastOptsPrinted = ""
    }
  updateNextNodes

isBlocked :: forall sym arch. ReplM sym arch Bool
isBlocked = do
  (Some (node@(TraceNode _ _ subtree))) <- gets replNode
  st <- IO.liftIO $ getTreeStatus subtree
  return $ isBlockedStatus st

asChoice :: forall sym arch nm. TraceNode sym arch nm -> ReplM sym arch (Maybe (SomeChoice '(sym,arch)))
asChoice (node@(TraceNode _ v _)) = case testEquality (knownSymbol @nm) (knownSymbol @"choice")  of
  Just Refl -> return $ Just v
  Nothing -> return Nothing

asChoiceTree :: forall sym arch nm. TraceNode sym arch nm -> ReplM sym arch (Maybe (SomeChoiceHeader '(sym,arch)))
asChoiceTree (node@(TraceNode _ v _)) = case testEquality (knownSymbol @nm) (knownSymbol @"choiceTree")  of
  Just Refl -> return $ Just v
  Nothing -> return Nothing

goto_status'' :: (NodeStatus -> Bool) -> [Some (TraceNode sym arch)] -> ReplM sym arch ()
goto_status'' f (Some node@(TraceNode _ _ subtree) : xs) = do
  st <- IO.liftIO $ getTreeStatus subtree
  case f st of
    True -> do

      goto_node' node >> (goto_status' f)
    False -> goto_status'' f xs
goto_status'' f [] = return ()

goto_status' :: (NodeStatus -> Bool) -> ReplM sym arch ()
goto_status' f = do
  updateNextNodes
  nextNodes <- gets replNext
  goto_status'' f (map snd $ reverse nextNodes)

isErrStatus :: NodeStatus -> Bool
isErrStatus = \case
  NodeStatus StatusSuccess True _ -> False
  NodeStatus _ False _ -> False
  _ -> True

goto_err :: IO ()
goto_err = execReplM (goto_status' isErrStatus >> ls')

goto_prompt :: IO ()
goto_prompt = execReplM (goto_status' isBlockedStatus >> ls')

next :: IO ()
next = execReplM $ do
  nextNodes <- gets replNext
  goto' (length nextNodes - 1)
  return ()

goto_node' :: TraceNode sym arch nm -> ReplM sym arch ()
goto_node' nextNode = do
  lastNode <- currentNode
  loadTraceNode nextNode
  modify $ \st -> st { replPrev = lastNode : (replPrev st) }

goto' :: Int -> ReplM sym arch (Maybe (Some (TraceNode sym arch)))
goto' idx = do
  fetchNode idx >>= \case
    Just (Some nextNode) -> asChoice nextNode >>= \case
      Just (SomeChoice c) -> do
        IO.liftIO $ choicePick c
        (IO.liftIO $ IO.threadDelay 100)
        Some curNode <- currentNode
        top'
        IO.liftIO $ wait
        (Just <$> currentNode)
      Nothing -> do
        goto_node' nextNode
        ls'
        return $ Just (Some nextNode)
    Nothing -> return Nothing

finishedPrefix :: ReplM sym arch (Int)
finishedPrefix = do
  nextNodes <- gets replNext
  nextStatuses <- mapM (\(_, Some (TraceNode _ _ t)) -> (IO.liftIO $ getTreeStatus t)) nextNodes
  return $ length (takeWhile isFinished nextStatuses)

waitRepl :: Int -> ReplM sym arch ()
waitRepl lastShown = do
    updateNextNodes
    (Some (TraceNode _ _ t))  <- gets replNode
    st <- IO.liftIO $ getTreeStatus t
    case isFinished st of
      True | lastShown == -1 -> return ()
      True -> do
        PO.printBreak
        prettyNextNodes lastShown False >>= PO.printOutputLn   
      False -> do
        Some (node@(TraceNode _ _ t)) <- gets replNode
        st <- IO.liftIO $ getTreeStatus t
        case isFinished st of
          True -> PO.printErrLn "No such option" >> return ()
          False -> do
            n <- case lastShown >= 0 of
              True -> finishedPrefix
              False -> return lastShown
            if n > lastShown && lastShown >= 0 then do
              PO.printBreak
              prettyNextNodes lastShown True >>= PO.printOutput
            else
              PO.printHeartbeat
            isBlocked >>= \case
              True -> PO.printBreak >> goto_status' isBlockedStatus >> ls'
              False -> ((IO.liftIO $ IO.threadDelay 1000000) >> waitRepl n)

tryKillWaitThread :: IO ()
tryKillWaitThread = do
  wt <- IO.atomicModifyIORef' waitThread (\wt -> (decrementWait wt, decrementWait wt))
  case wt of
    WaitThread (Just (tid)) n | n <= 0 -> IO.killThread tid
    _ -> return ()

killWaitThread :: IO ()
killWaitThread = do
  mtid <- IO.atomicModifyIORef' waitThread (\(WaitThread tid _gas) -> (WaitThread Nothing 0, tid))
  case mtid of
    Just tid -> IO.killThread tid
    Nothing -> return ()

waitIO :: Bool -> IO ()
waitIO verbose = do
  let n :: Int = if verbose then 0 else (-1)
  execReplM (return ())
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> return ()
    WaitingForToplevel{} -> do
      IO.readIORef finalResult >>= \case
        Just (Left msg) -> PO.printMsgLn ("Error:\n" <> PP.pretty msg) >> return ()
        Just (Right r) -> PO.printMsgLn (PP.pretty (show r))
        Nothing -> do
          PO.printMsgLn "Verifier is starting..."
          IO.threadDelay 1000000 >> (waitIO verbose)
    SomeReplState{} -> execReplM $ waitRepl n

wait :: IO ()
wait = wait_verbosity True

wait_initial :: IO ()
wait_initial = do
  tid <- IO.forkFinally (waitIO False) (\_ -> killWaitThread)
  IO.writeIORef waitThread (WaitThread (Just (tid)) 2)

wait_verbosity :: Bool -> IO ()
wait_verbosity verbose = do
  killWaitThread
  tid <- IO.forkFinally (waitIO verbose) $ \case
    Left _ -> killWaitThread
    Right _ -> (getPrompt >>= PO.printPrompt) >> killWaitThread    
  IO.writeIORef waitThread (WaitThread (Just (tid)) 2)

goto :: Int -> IO ()
goto idx = execReplM $ do
  goto' idx >>= \case
    Just _ -> return ()
    Nothing -> PO.printErrLn "No such option"

gotoIndex :: forall sym arch. Integer -> ReplM sym arch String
gotoIndex idx = (goto' (fromIntegral idx)) >>= \case
  Just (Some ((TraceNode lbl v _) :: TraceNode sym arch nm)) -> do
    tags <- gets replTags
    return $ show (prettyDetailAt @'(sym, arch) @nm tags lbl v)
  Nothing -> return "No such option"

-- Hacks to export the arch and sym parameters to the toplevel

coerceValidRepr ::
  ValidSymArchRepr sym arch sym arch -> ValidSymArchRepr sym arch Sym Arch
coerceValidRepr repr = unsafeCoerce repr


coerceTraceNode :: forall nm sym arch. TraceNode sym arch nm -> ReplM_ sym arch (TraceNode Sym Arch nm)
coerceTraceNode (TraceNode lbl v subtree) = do
  repr <- gets replValidRepr
  ValidSymArchRepr{} <- return $ coerceValidRepr repr
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
  ValidSymArchRepr sym arch <- return $ coerceValidRepr repr
  return $ ValidSymArchRepr sym arch

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

setJSONMode :: Bool -> IO ()
setJSONMode = PO.setJSONMode