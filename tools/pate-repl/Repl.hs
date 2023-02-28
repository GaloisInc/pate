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
import           Control.Monad.State ( MonadState, StateT, modify, gets, runStateT, get, put, forM )
import qualified Control.Monad.IO.Class as IO
import           Data.Proxy
import qualified Data.Text.IO as Text
import qualified Data.Text.Lazy as TextL
import           Text.Read (readMaybe)
import           System.Exit
import           System.Environment

import           Data.Parameterized.Some
import           Data.Parameterized.Classes

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter.Render.Terminal as PPRT
import qualified Prettyprinter.Render.Text as PPText

import           Data.Parameterized.SymbolRepr ( KnownSymbol, knownSymbol, SymbolRepr, symbolRepr )


import qualified Pate.Arch as PA
import qualified Pate.Solver as PS
import qualified Pate.Equivalence as PEq
import qualified ReplHelper as PIRH
import qualified ReplBase
import           ReplBase ( Sym, Arch )

import           Pate.TraceTree

import Unsafe.Coerce(unsafeCoerce)

import qualified Main as PM

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
        Nothing -> IO.liftIO $ IO.putStrLn "No such options"
      Nothing -> IO.liftIO $ IO.putStrLn str
  case r of
    Just () -> return ()
    Nothing -> IO.putStrLn "<<No Binary Loaded>>"

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
    } -> ReplState sym arch

data ValidSymArchRepr sym arch symExt archExt where
  ValidSymArchRepr :: (sym ~ symExt, arch ~ archExt, PA.ValidArch arch, PS.ValidSym sym) => sym -> PA.SomeValidArch arch -> ValidSymArchRepr sym arch symExt archExt

data ReplIOStore =
    NoTreeLoaded
  -- main thread has started but hasn't yet produced a tree
  | WaitingForToplevel IO.ThreadId (SomeTraceTree PA.ValidRepr)
  -- we've started navigating the resulting tree
  | forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => SomeReplState IO.ThreadId (ReplState sym arch)


newtype ReplM_ sym arch a = ReplM_ { unReplM :: (StateT (ReplState sym arch) IO a) }
  deriving ( Functor, Applicative, Monad, MonadState (ReplState sym arch), IO.MonadIO )

type ReplM sym arch a = (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a

runReplM :: forall a. (forall sym arch. (PA.ValidArch arch, PS.ValidSym sym) => ReplM_ sym arch a) -> IO (Maybe a)
runReplM f = do
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> return Nothing
    WaitingForToplevel tid tree -> loadSomeTree tid tree >>= \case
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
  Nothing -> IO.putStrLn "No old ref"
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


loadSomeTree ::
  IO.ThreadId -> SomeTraceTree PA.ValidRepr -> IO Bool
loadSomeTree tid topTraceTree = do
  viewSomeTraceTree topTraceTree (return False) $ \(PA.ValidRepr sym arch) (toptree :: TraceTree k) -> do
      let st = ReplState
            { replNode = Some (TraceNode @"toplevel" () () toptree)
            , replTags = [Simplified]
            , replPrev = []
            , replNextTags = [Simplified]
            , replNext = []
            , replValidRepr = ValidSymArchRepr sym arch
            , replLastOptsPrinted = ""
            , replNesting = 0
            }
      IO.writeIORef ref (SomeReplState tid st)
      execReplM updateNextNodes
      return True

instance IsTraceNode k "toplevel" where
  type TraceNodeType k "toplevel" = ()
  prettyNode () () = "<Toplevel>"

run :: String -> IO ()
run rawOpts = do
  PIRH.setLastRunCmd rawOpts
  case OA.execParserPure OA.defaultPrefs PM.cliOptions (words rawOpts) of
    OA.Success opts -> do
      topTraceTree <- someTraceTree
      tid <- IO.forkFinally (PM.runMain topTraceTree opts) $ \case
        Left err -> do
          killWaitThread
          let msg = show err
          case msg of
            "thread killed" -> return ()
            _ -> IO.putStrLn $ "Verifier failed: " ++ show err
          IO.writeIORef finalResult (Just (Left msg))
        Right a -> IO.writeIORef finalResult (Just (Right a))
      IO.writeIORef ref (WaitingForToplevel tid topTraceTree)
      wait
    OA.Failure failure -> do
      progn <- getProgName
      let (msg, exit) = OA.renderFailure failure progn
      case exit of
        ExitSuccess -> IO.putStrLn msg
        _           -> IO.hPutStrLn IO.stderr msg
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
      IO.putStrLn $ ":run \"" ++ rawOpts ++ "\""
      run rawOpts
    Nothing -> IO.putStrLn "No previous run found"

printPretty :: PP.Doc ann -> ReplM_ sym arch ()
printPretty p = do
  let s = PP.layoutSmart (PP.defaultLayoutOptions { PP.layoutPageWidth = PP.Unbounded }) p
  IO.liftIO $ Text.putStr (PPText.renderStrict s)

printPrettyLn :: PP.Doc ann -> ReplM_ sym arch ()
printPrettyLn p = printPretty (p <> PP.line)

isSubTreeNode ::
  forall sym arch nm.
  TraceNode sym arch nm -> Bool
isSubTreeNode (TraceNode{}) = case symbolRepr (knownSymbol @nm) of
  "subtree" -> True
  "choiceTree" -> True
  "function_name" -> True
  _ -> False

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
        next <- maybeSubNodes nextNode (return []) (gets replNext)
        case (isSubTreeNode nextNode, next) of
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

addStatusTag :: NodeStatus -> PP.Doc a -> PP.Doc a
addStatusTag st p = case ppStatusTag st of
  Just pst -> p <+> "(" <> pst <> ")"
  Nothing -> p

addSuffix :: Int -> PP.Doc a -> NodeStatus -> SymbolRepr nm -> ReplM sym arch (PP.Doc a)
addSuffix nesting pp s nm = do
  tags <- gets replTags
  pp' <- case tags of
    [Simplified] -> return $ addStatusTag s pp
    _ -> return $ addStatusTag s pp <+> "(" <> PP.pretty (show nm) <> ")"
  case nesting < 0 of
    True -> return $ pp' <> PP.line <> "... <more results>"
    False -> return pp'


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
  case isSubTreeNode nd of
    True -> withNode nd $ f
    False -> do
      mr <- withNode nd $ do
        nextNodes <- gets replNext
        case length nextNodes == 1 of
          True -> Just <$> f
          False -> return Nothing
      case mr of
        Just a -> return a
        Nothing -> g

prettyNextNodes ::
  forall sym arch a.
  Int ->
  Bool ->
  ReplM sym arch (PP.Doc a)
prettyNextNodes startAt onlyFinished = do
  tags <- gets replNextTags
  nextNodes <- gets replNext
  
  ppContents' <- 
       mapM (\(nesting, Some (nd@(TraceNode lbl v subtree) :: TraceNode sym arch nm)) -> do
                b <- IO.liftIO $ getTreeStatus subtree
                case prettyNodeAt @'(sym, arch) @nm tags lbl v of
                  Just pp -> do
                    pp' <- addSuffix nesting pp b (knownSymbol @nm)
                    let indent = abs(nesting)*2
                    return $ (isFinished b, PP.indent indent $ pp')
                    {-
                    maybeSubNodes nd ()) $ do
                      subpp <- prettyNextNodes 0 onlyFinished
                      return $ (isFinished b, PP.vsep [pp', PP.indent 2 subpp])
                    -}
                  Nothing -> return (isFinished b, "<ERROR: Unexpected missing printer>")
            ) nextNodes

  let ppContents = case onlyFinished of
        True -> map snd $ takeWhile (\(fin, _) -> fin) ppContents'
        False -> map snd ppContents'
  return $ PP.vsep (drop startAt (map (\((idx :: Int), pp) -> PP.pretty idx <> ":" <+> pp) (zip [0..] ppContents)))


getPrompt :: IO String
getPrompt = do
  mst <- runReplM $ do
    (Some (TraceNode _ _ t))  <- gets replNode
    IO.liftIO $ getTreeStatus t
  case mst of
    Just st | Just pst <- ppStatusTag st -> return $ (show (pst <> ">"))
    _ -> return ">"

ls' :: forall sym arch. ReplM sym arch ()
ls' = do
  updateNextNodes
  p <- prettyNextNodes 0 False
  nextNodes <- gets replNext
  (Some ((TraceNode lbl v _) :: TraceNode sym arch nm)) <- gets replNode
  let thisPretty = prettyNode @_ @'(sym, arch) @nm lbl v
  case nextNodes of
    [] -> printPrettyLn thisPretty
    _ -> printPrettyLn (PP.vsep [thisPretty,p])

ls :: IO ()
ls = execReplM ls'

stop :: IO ()
stop = do
  IO.readIORef ref >>= \case
    NoTreeLoaded -> return ()
    WaitingForToplevel tid _ -> IO.killThread tid
    SomeReplState tid _ -> IO.killThread tid

up :: IO ()
up = execReplM $ (up' >> ls')

up' :: ReplM sym arch ()
up' = do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> IO.liftIO $ IO.putStrLn "<<At top level>>"
    (Some popped:prevNodes') -> do
      loadTraceNode popped
      modify $ \st -> st { replPrev = prevNodes' }

top :: IO ()
top = execReplM $ (top' >> ls')

top' :: ReplM sym arch ()
top' = do
  prevNodes <- gets replPrev
  case prevNodes of
    [] -> IO.liftIO $ IO.putStrLn "<<At top level>>"
    _ -> do
      Some init <- return $ last prevNodes
      loadTraceNode init
      modify $ \st -> st { replPrev = [] }

status' :: Maybe Int -> IO ()
status' mlimit = do
  tr <- IO.readIORef ref
  case tr of
    NoTreeLoaded -> IO.putStrLn "No tree loaded"
    WaitingForToplevel{} -> do
      fin <- IO.liftIO $ IO.readIORef finalResult
      case fin of
        Just r -> IO.putStrLn (show r)
        _ -> IO.putStrLn "Waiting for verifier..."
    SomeReplState {} -> execReplM $ do
      (Some (TraceNode _ _ t))  <- gets replNode
      st <- IO.liftIO $ getTreeStatus t
      case st of
        _ | isBlockedStatus st -> IO.liftIO $ IO.putStrLn $ "Waiting for input.."
        NodeStatus (StatusWarning e) _ _ -> IO.liftIO $  IO.putStrLn $ "Warning: \n" ++ (chopMsg mlimit (show e))
        NodeStatus (StatusError e) _ _ ->  IO.liftIO $  IO.putStrLn $ "Error: \n" ++ (chopMsg mlimit (show e))
        NodeStatus StatusSuccess False _ ->  IO.liftIO $ IO.putStrLn $ "In progress.."
        NodeStatus StatusSuccess True _ -> IO.liftIO $ IO.putStrLn "Finalized"
      prevNodes <- gets replPrev
      fin <- IO.liftIO $ IO.readIORef finalResult
      case (prevNodes, fin) of
        ([], Just r) -> printPrettyLn (PP.viaShow r)
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
    True -> goto_node' node >> (goto_status' f)
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
      True -> do
        IO.liftIO $ IO.putStrLn ""
        prettyNextNodes lastShown False >>= printPrettyLn   
      False -> do
        Some (node@(TraceNode _ _ t)) <- gets replNode
        st <- IO.liftIO $ getTreeStatus t
        case isFinished st of
          True -> IO.liftIO $ IO.putStrLn "No such option" >> return ()
          False -> do
            n <- finishedPrefix            
            if n > lastShown then do
              IO.liftIO $ IO.putStrLn ""
              prettyNextNodes lastShown True >>= printPretty
            else
              IO.liftIO (IO.putStr ".")
            isBlocked >>= \case
              True -> IO.liftIO (IO.putStrLn "") >> goto_status' isBlockedStatus >> ls'
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

waitIO :: IO ()
waitIO = do
  execReplM (return ())
  t <- IO.readIORef ref
  case t of
    NoTreeLoaded -> return ()
    WaitingForToplevel{} -> do
      IO.readIORef finalResult >>= \case
        Just (Left msg) -> IO.putStrLn ("Error:\n" ++ msg) >> return ()
        Just (Right r) -> IO.putStrLn (show r)
        Nothing -> do
          IO.putStrLn "Verifier is starting..."
          IO.threadDelay 1000000 >> waitIO
    SomeReplState{} -> execReplM $ waitRepl 0

wait :: IO ()
wait = do
  killWaitThread
  tid <- IO.forkFinally waitIO $ \case
    Left _ -> killWaitThread
    Right _ -> (getPrompt >>= IO.putStr) >> killWaitThread    
  IO.writeIORef waitThread (WaitThread (Just (tid)) 2)

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
