{-|
Module           : Pate.TraceTree
Copyright        : (c) Galois, Inc 2022
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Defines the 'TraceTree' and 'TraceTreeNode' types used for
representing tracing data collected during verification.

Tree nodes are labeled with type-level symbols, which are
assocated with a type of data via the 'IsTraceNode' class.
New types can be added to the tree by instantiating this
type class with a (distinct) symbol.

-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DefaultSignatures #-}

module Pate.TraceTree (
    TraceTree
  , TraceTreeNode
  , IsTraceNode(..)
  , isTraceNode
  , prettyNodeAt
  , prettyDetailAt
  , nodeShownAt
  , TraceTag(..)
  , viewTraceTreeNode
  , viewTraceTree
  , prettySummary
  , NodeBuilder
  , TreeBuilder
  , startTree
  , startNode
  , singleNode
  , addNode
  , addNodeValue
  , updateTreeStatus
  , updateNodeStatus
  , SomeTraceTree
  , someTraceTree
  , noTraceTree
  , viewSomeTraceTree
  , NodeStatus(..)
  , isBlockedStatus
  , BlockedStatus(..)
  , NodeStatusLevel(..)
  , getNodeStatus
  , getTreeStatus
  , MonadTreeBuilder(..)
  , NoTreeBuilder(..)
  , IsTreeBuilder
  , NodeBuilderT
  , TreeBuilderT
  , startSomeTreeBuilder
  , resetSomeTreeBuilder
  , runTreeBuilderT
  , withSubTraces
  , subTraceLabel
  , subTraceLabel'
  , subTree
  , subTrace
  , emitTraceLabel
  , emitTrace
  , traceAlternatives
  , IsNodeError(..)
  , emitTraceWarning
  , emitTraceError
  , finalizeTree
  , withTracing
  , withTracingLabel
  , withNoTracing
  , mkTags
  , runNodeBuilderT
  , getNodeBuilder
  , noTracing
  , chooseLabel
  , chooseLazy
  , choose
  , chooseBool
  , ChoiceHeader(..)
  , SomeChoiceHeader(..)
  , Choice(..)
  , SomeChoice(..)
  , LazyIOAction(..)
  , nodeToJSON
  , resolveQuery
  , NodeQuery(..)
  , NodeIdentQuery(..)
  , SomeTraceNode(..)
  , asChoice
  , forkTraceTreeHook
  , NodeFinalAction(..)
  , QueryResult(..)
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import           Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.IO.Unlift as IO
import qualified Data.IORef as IO
import           Data.String
import qualified Data.Map as Map
import           Data.Map ( Map )
import           Data.Default
import           Data.List ((!!), find, isPrefixOf)
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.Maybe
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Trans as CMT
import           Control.Monad.Except
import           Control.Monad.Catch
import           Control.Monad (void, unless, forM) -- GHC 9.6
import           Control.Applicative

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.String as PP

import qualified Data.Aeson as JSON
import qualified Compat.Aeson as JSON
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr ( knownSymbol, symbolRepr, SomeSym(..), SymbolRepr )
import Control.Exception (IOException)
import Control.Monad.Trans.Writer
import Control.Concurrent.MVar
import qualified Data.Set as Set
import Data.Set (Set)
import GHC.IO (unsafePerformIO)
import qualified Control.Concurrent as IO
import qualified System.IO as IO
import Data.Maybe (catMaybes)
import Control.Concurrent (threadDelay)
import Control.Monad.State.Strict (StateT (..), MonadState (..))

data TraceTag =
    Summary
  | Full
  | Simplified
  | Simplified_Detail
  | Custom String
  deriving (Eq, Ord)


class Show e => IsNodeError e where
  propagateErr :: e -> Bool

instance IsNodeError IOException where
  propagateErr _ = True

newtype ChoiceIdent = ChoiceIdent Int
  deriving (Eq, Ord, Show)

data BlockedStatus = BlockedStatus { _blockedChoices :: Set ChoiceIdent, _unBlockedChoices :: Set ChoiceIdent }

instance Eq BlockedStatus where
  (BlockedStatus a b) == (BlockedStatus a_ b_) = a == a_ && b == b_

instance Monoid BlockedStatus where
  mempty = BlockedStatus mempty mempty

instance Semigroup BlockedStatus where
  BlockedStatus st1 st2 <> BlockedStatus st1_ st2_ = BlockedStatus (st1 <> st1_) (st2 <> st2_)

isUnblocked' :: BlockedStatus -> Bool
isUnblocked' (BlockedStatus blocked unblocked) = Set.isSubsetOf blocked unblocked

data NodeStatusLevel =
    StatusSuccess
  | forall e. IsNodeError e => StatusWarning e
  | forall e. IsNodeError e => StatusError e

-- TODO: I think this discards errors from blocked siblings
joinStatusLevels ::
  NodeStatusLevel -> NodeStatusLevel -> Maybe NodeStatusLevel
joinStatusLevels lvlHi lvlLo = case (lvlHi, lvlLo) of
  (StatusWarning{}, StatusSuccess) -> Just lvlHi
  (StatusError{}, StatusWarning{}) -> Just lvlHi
  (StatusError{}, StatusSuccess) -> Just lvlHi
  _ -> Nothing

-- TODO: We could expose the error type here with some plumbing
data NodeStatus = NodeStatus { nodeStatusLevel :: NodeStatusLevel, 
  isFinished :: Bool, blockStatus :: BlockedStatus }

-- | A blocked node means that it (or a subnode) is waiting for input
isBlockedStatus :: NodeStatus -> Bool
isBlockedStatus st = not (isUnblocked' (blockStatus st))

shouldPropagate :: NodeStatusLevel -> Bool
shouldPropagate StatusSuccess = False
shouldPropagate (StatusWarning e) = propagateErr e
shouldPropagate (StatusError e) = propagateErr e

instance IsString TraceTag where
  fromString str = Custom str

-- | Allowing for lazy evaluation of trace trees
data IOList' a = IOList' { ioList :: [a], ioListStatus :: NodeStatus }
-- The Mvar is used to signal when updates are made, for clients to
-- block on updates (rather than busy-waiting)
data IOList a = IOList (IO.IORef (IOList' a)) (MVar ())

evalIOList' :: IOList a -> IO (IOList' a)
evalIOList' (IOList ref _) = IO.readIORef ref

evalIOList :: IOList a -> IO [a]
evalIOList l = ioList <$> evalIOList' l

-- Keep re-running the inner computation until it gives a 'Just'
-- result or the list is finalized.
-- The list of 'a' given to the continuation is the full value of the
-- IOList each time it is executed.
-- The result is either the computer 'b' or the final contents of the list
withIOList :: forall a b. IOList a -> ([a] -> IO (Maybe b)) -> IO (Either [a] b)
withIOList (IOList ref mv) f = go
  where
    go :: IO (Either [a] b)
    go = do
      () <- takeMVar mv
      IOList' l st <- IO.readIORef ref
      f l >>= \case
        -- make sure we wake up anyone else waiting for this signal
        -- once we finish
        Just b -> tryPutMVar mv () >> (return $ Right b)
        Nothing | isFinished st -> tryPutMVar mv () >> (return $ Left l)
        Nothing -> threadDelay 10000 >> go

mkStaticIOList :: [a] -> IO (IOList a)
mkStaticIOList xs = do
  ref <- IO.newIORef (IOList' xs (NodeStatus StatusSuccess True mempty))
  mv <- newMVar ()
  return $ IOList ref mv

addIOList :: a -> IOList a -> IO ()
addIOList a (IOList ref mv) = do
  IO.atomicModifyIORef' ref (\(IOList' as st) -> (IOList' (a : as) st,()))
  void $ tryPutMVar mv ()

modifyIOListStatus :: (NodeStatus -> NodeStatus) -> IOList a -> IO ()
modifyIOListStatus f (IOList ref mv) = do
  b <- IO.atomicModifyIORef' ref (\(IOList' as st) -> (IOList' as (f st),isFinished st && (isFinished $ f st)))
  unless b $ void $ tryPutMVar mv ()

propagateIOListStatus :: NodeStatus -> IOList a -> IO ()
propagateIOListStatus st l = modifyIOListStatus (propagateStatus st) l

propagateStatus :: NodeStatus -> NodeStatus -> NodeStatus
propagateStatus stNew stOld = 
  let stNew' = case isFinished stOld of
        True -> stOld 
        False -> case joinStatusLevels (nodeStatusLevel stNew) (nodeStatusLevel stOld) of
          Just stLvlMerged -> stNew { nodeStatusLevel = stLvlMerged }
          Nothing -> stOld { isFinished = isFinished stNew }
  in stNew' { blockStatus = (blockStatus stOld) <> (blockStatus stNew) }

getIOListStatus :: IOList a -> IO NodeStatus
getIOListStatus l = ioListStatus <$> evalIOList' l

emptyIOList :: IO (IOList a)
emptyIOList = do
  r <- IO.liftIO $ IO.newIORef (IOList' [] (NodeStatus StatusSuccess False mempty))
  mv <- newMVar ()
  return $ IOList r mv

resetIOList :: IOList a -> IO ()
resetIOList (IOList r mv) = do
  IO.atomicWriteIORef r (IOList' [] (NodeStatus StatusSuccess False mempty))
  void $ tryPutMVar mv ()
  return ()

data NodeBuilder k nm where
  NodeBuilder ::
    { updateNodeStatus :: NodeStatus -> IO ()
    , startTreeFromNode :: IO (TraceTree k, TreeBuilder k)
    , addNodeValue :: TraceNodeLabel nm -> TraceNodeType k nm -> TraceTree k -> IO ()
    } -> NodeBuilder k nm

data NodeIdentQuery = QueryInt Int | QueryString String | QueryStringInt Int String | QueryAny
  deriving (Eq, Ord)

instance Show NodeIdentQuery where
  show = \case
    QueryInt i -> show i ++ ":"
    QueryString s -> "\"" ++ s ++ "\""
    QueryStringInt i s -> show i ++ ": " ++ "\"" ++ s ++ "\""
    QueryAny -> "..."

data NodeFinalAction = NodeFinalAction
  {
    finalAct :: forall l (k :: l). SomeTraceNode k -> IO Bool
  }

-- context plus final selection
data NodeQuery = NodeQuery [NodeIdentQuery] NodeFinalAction

instance Show NodeQuery where
  show (NodeQuery qs _) = show qs

-- Attempt to resolve a query by traversing the TraceTree to the
-- referenced node.
-- This will block if the node traversal can't be completed due to
-- pending results (i.e. the search ended on a node that has not been finalized),
-- waiting until the node is completed before either terminating

-- blocks until either the requested node becomes available, returning true
-- returns false if the requested node could not be found, after the relevant
-- subtree has finished

data SomeTraceNode k = forall nm. IsTraceNode k nm => SomeTraceNode (SymbolRepr nm) (TraceNodeLabel nm) (TraceNodeType k nm)

instance Show (SomeTraceNode k) where
  show (SomeTraceNode (nm :: SymbolRepr nm) lbl v) = show nm ++ ": " ++ show (prettyNode @_ @k @nm lbl v)

asChoice :: forall k. SomeTraceNode k -> Maybe (SomeChoice k)
asChoice (SomeTraceNode nm _ v) |
    Just Refl <- testEquality nm (knownSymbol @"choice")
  = Just v
asChoice _ = Nothing

data QueryResult k = QueryResult [NodeIdentQuery] (SomeTraceNode k)

resolveQuery :: forall k.
 NodeQuery ->
 TraceTree k ->
 IO (Maybe (QueryResult k))
resolveQuery (NodeQuery [] _) _ = return Nothing
resolveQuery (NodeQuery (q_outer:qs_outer) fin_outer) t_outer =
  go [] q_outer (NodeQuery qs_outer fin_outer) t_outer
  where

    go :: [NodeIdentQuery]-> NodeIdentQuery -> NodeQuery -> TraceTree k -> IO (Maybe (QueryResult k))
    go acc q (NodeQuery qs fin) (TraceTree t) = do
      -- IO.putStrLn $ "go 1:" ++ show q
      result <- withIOList t $ \nodes -> do
        -- IO.putStrLn "go 2"
        matches <- get_matches q nodes
        check_matches acc (NodeQuery qs fin) matches
      case result of
        Left{} -> return Nothing
        Right a -> return $ Just a

    check_matches :: [NodeIdentQuery] -> NodeQuery -> [(NodeIdentQuery, SomeTraceNode k, TraceTree k)] -> IO (Maybe (QueryResult k))
    check_matches acc (NodeQuery [] fin) ((q, x,_):xs) = finalAct fin x >>= \case
      True -> return $ Just (QueryResult (reverse (q:acc)) x)
      False -> check_matches acc (NodeQuery [] fin) xs
    check_matches _ _ [] = return Nothing
    check_matches acc (NodeQuery (q:qs) fin) ((matched_q, _,t):xs) = go (matched_q:acc) q (NodeQuery qs fin) t >>= \case
      Just result -> return $ Just result
      Nothing -> check_matches acc (NodeQuery (q:qs) fin) xs

    get_matches :: NodeIdentQuery -> [Some (TraceTreeNode k)] -> IO [(NodeIdentQuery, SomeTraceNode k, TraceTree k)]
    get_matches q  nodes = do
      nodes' <- fmap concat $ forM nodes $ \(Some ((TraceTreeNode l) :: TraceTreeNode k nm)) ->
        case getNodePrinter @k @nm [Simplified] of
          Nothing -> return []
          Just _pp -> map (\((v,lbl),t) -> (SomeTraceNode @k (knownSymbol @nm) lbl v,t)) <$> evalIOList l
      -- NB: nodes are stored in the tree in reverse order (latest trace entry is the first element of the list),
      -- we need to reverse it here so the indices match up
      fmap catMaybes $ forM (zip [0..] (reverse nodes')) $ \(i,(SomeTraceNode (nm :: SymbolRepr nm) lbl v, t)) -> do
        Just pp <- return $ getNodePrinter @k @nm [Simplified]
        let as_string = PP.renderString $ PP.layoutPretty (PP.defaultLayoutOptions { PP.layoutPageWidth = PP.Unbounded }) (pp lbl v)
        let matched = case q of
              QueryInt i' -> i == i'
              QueryString s -> isPrefixOf s as_string
              QueryStringInt i' s -> i == i' && isPrefixOf s as_string
              QueryAny -> True
        case matched of
          True -> return $ Just $ (QueryStringInt i as_string, SomeTraceNode nm lbl v,t)
          False -> return Nothing

data InteractionMode =
    Interactive (IO ChoiceIdent)
  | DefaultChoice

data TreeBuilder k where
  TreeBuilder ::
    { updateTreeStatus :: NodeStatus -> IO ()
    , startNode :: forall nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
    , addNode :: forall nm. TraceTreeNode k nm -> IO ()
    , interactionMode :: InteractionMode
    -- ^ true if this treeBuilder can supply choices
    } -> TreeBuilder k

asBlockedStatus :: NodeStatus -> NodeStatus
asBlockedStatus st = NodeStatus StatusSuccess False (blockStatus st)

addNodeDependency :: NodeBuilder k nm -> TreeBuilder k -> TreeBuilder k
addNodeDependency nodeBuilder treeBuilder =
  let finish st = case shouldPropagate (nodeStatusLevel st) of
        -- importantly, we don't propagate regular status updates to ancestors,
        -- otherwise finalizing a child would cause all parents to finalize
        True -> updateNodeStatus nodeBuilder st >> updateTreeStatus treeBuilder st
        False -> updateNodeStatus nodeBuilder (asBlockedStatus st) >> updateTreeStatus treeBuilder st
        -- _ -> updateTreeStatus treeBuilder st
  in treeBuilder { updateTreeStatus = finish } 

addTreeDependency :: TreeBuilder k -> NodeBuilder k nm -> NodeBuilder k nm
addTreeDependency treeBuilder nodeBuilder =
  let finish st = case shouldPropagate (nodeStatusLevel st) of
        True -> updateTreeStatus treeBuilder st >> updateNodeStatus nodeBuilder st
        False -> updateTreeStatus treeBuilder (asBlockedStatus st) >> updateNodeStatus nodeBuilder st
        -- _ -> updateNodeStatus nodeBuilder st
  in nodeBuilder { updateNodeStatus = finish }


globalChoiceNonce :: MVar ChoiceIdent
globalChoiceNonce = unsafePerformIO (newMVar (ChoiceIdent 0))

startTree :: forall k. IO (TraceTree k, TreeBuilder k)
startTree  = do
  l <- emptyIOList
  let nextChoice = modifyMVar globalChoiceNonce (\(ChoiceIdent i) -> return (ChoiceIdent (i + 1), ChoiceIdent i))
  let builder = TreeBuilder (\st -> propagateIOListStatus st l) (startNode' @k) (\node -> addIOList (Some node) l) (Interactive nextChoice) 
  return (TraceTree l, builder)

startNode' :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
startNode' = do
  l <- emptyIOList
  let builder = NodeBuilder (\st -> propagateIOListStatus st l) startTree $ \lbl v subtree ->
        addIOList ((v, lbl), subtree) l
  return (TraceTreeNode l, builder)

singleNode ::
  forall k nm.
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  IO (TraceTreeNode k nm)
singleNode lbl v = do
  t <- mkStaticIOList []
  l <- mkStaticIOList [((v,lbl), TraceTree t)]
  return $ TraceTreeNode l

-- | A labeled node in a 'TraceTree' that contains a list of sub-trees
--   annotated with values according to the 'IsTraceNode' class instance
--   for the given symbol.
--   The 'k' type parameter is used to provide additional parameters
--   to the type represented by 'nm' via the 'IsTraceNode' class
data TraceTreeNode (k :: l) nm where
  TraceTreeNode :: IsTraceNode k nm =>
    IOList ((TraceNodeType k nm, TraceNodeLabel nm), TraceTree k) ->
    TraceTreeNode k nm


-- | A heterogenous list of 'TraceTreeNode' elements, representing
--   all of the tracing context that was emitted at this level
newtype TraceTree k = TraceTree (IOList (Some (TraceTreeNode k)))

isTraceNode :: TraceTreeNode k nm -> (IsTraceNode k nm => a) -> a
isTraceNode TraceTreeNode{} a = a

-- | A somewhat clunky way to allow the 'k' parameter to specify
--   the type of additional input parameters for json serialization
--   (specifically needed to support passing in the expression builder
--    when serializing what4 terms)
type family TraceNodeCore (k :: l) :: Type
type instance TraceNodeCore '(a,b) = a

class (KnownSymbol nm, Eq (TraceNodeLabel nm)) => IsTraceNode (k :: l) (nm :: Symbol)  where
  -- TODO: these types often have extra parameters where we need to wrap them
  -- in a 'Some' to get them down to a 'Type'.
  -- In general we could have this class take an extra 'Ctx' used to
  -- hold the extra type parameters that should be extenstially quantified
  -- in the tree
  type TraceNodeType k nm :: Type

  -- | Labels can be used to distinguish nodes that share the same symbol in a
  --   'TraceTree'
  type TraceNodeLabel nm :: Type
  type TraceNodeLabel nm = ()
 
  -- | Pretty print the full contents of this node.
  --   This is the default printer when examining the node with
  --   respect to the 'Full' tag
  prettyNode :: TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a

  jsonNode :: TraceNodeCore k -> TraceNodeLabel nm -> TraceNodeType k nm -> IO JSON.Value
  jsonNode _ _ _ = return $ case symbolRepr (knownSymbol @nm) of
    "()" -> JSON.Null
    x -> JSON.object ["node_kind" JSON..= x ]

  -- | Mapping from tracing tags to pretty-printers, allowing the contents
  --   of this node to be presented differently (or not at all) depending
  --   on what kind of printing is requested.
  nodeTags :: [(TraceTag, TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)]
  nodeTags = [(Summary, prettyNode @l @k @nm)]

nodeToJSON :: forall k nm. (IsTraceNode k nm, JSON.ToJSON (TraceNodeType k nm), JSON.ToJSON (TraceNodeLabel nm))
           => TraceNodeLabel nm 
           -> TraceNodeType k nm 
           -> IO JSON.Value
nodeToJSON lbl v =
  let i1 = case JSON.toJSON lbl of
        JSON.String "" -> [] 
        JSON.Null -> []
        x -> ["tag" JSON..= x]
      i2 = case JSON.toJSON v of
        JSON.Null -> []
        x -> [ "trace_node" JSON..= x ]
  in return $ JSON.object $ i1 ++ i2 ++ [ "trace_node_kind" JSON..= symbolRepr (knownSymbol @nm) ]

mkTags :: forall k nm a. IsTraceNode k nm => [TraceTag] -> [(TraceTag, TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)]
mkTags tags = map (\tag -> (tag, prettyNode @_ @k @nm)) tags

prettySummary ::
  forall k nm a.
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  Maybe (PP.Doc a)
prettySummary lbl v = prettyNodeAt @k @nm [Summary] lbl v

prettyDetailAt ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  PP.Doc a
prettyDetailAt tags lbl v = case elem Simplified tags of
  True -> case getNodePrinter @k @nm [Simplified_Detail] of
    Just pp -> pp lbl v
    Nothing -> prettyNode @_ @k @nm lbl v
  False -> prettyNode @_ @k @nm lbl v

prettyNodeAt ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  Maybe (PP.Doc a)
prettyNodeAt tags lbl v = case getNodePrinter @k @nm tags of
  Just pp -> Just (pp lbl v)
  Nothing -> Nothing

{-
prettyNodeAtIO ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  IO (Maybe (PP.Doc a))
prettyNodeAtIO tags lbl v = case getNodePrinter @k @nm tags of
  Just pp -> case testEquality (knownSymbol @"choice") (knownSymbol @nm) of
    Just Refl -> do
      b <- case v of
        SomeChoice choice -> choiceReady (choiceHeader choice) >>= \case
          True -> choiceChosen choice
          False -> return True
      case b of
        True -> return $ Just (pp lbl v)
        False -> return Nothing
    Nothing -> return $ Just (pp lbl v)
  Nothing -> return Nothing
-}

nodeKindShownAt ::
  forall k nm.
  IsTraceNode k nm =>
  [TraceTag] ->
  Bool
nodeKindShownAt tags = isJust (getNodePrinter @k @nm tags)

nodeShownAt ::
  forall k nm.
  [TraceTag] ->
  TraceTreeNode k nm ->
  IO Bool
nodeShownAt tags node@(TraceTreeNode{}) = case nodeKindShownAt @k @nm tags of
  True -> case testEquality (knownSymbol @"choiceTree") (knownSymbol @nm) of
    Just Refl -> viewTraceTreeNode node >>= \case
      [((SomeChoiceHeader header, _), _)] -> choiceReady header >>= \case
        -- once a choice has been made, don't display the tree, unless
        -- there are more decisions to be made
        True -> do
          st <- getNodeStatus node
          return $ isBlockedStatus st
        -- if the choice has been made, we need to display the
        -- tree so a decision can be made
        False -> return True
      _ -> return True
    Nothing -> return True
  False -> return False


tagsMap ::
  forall k nm a.
  IsTraceNode k nm =>
  Map TraceTag (TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)
tagsMap = Map.fromList (nodeTags @_ @k @nm)

getNodePrinter ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  Maybe (TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)
getNodePrinter [] = Nothing
getNodePrinter (Full : _) = case Map.lookup Simplified_Detail (tagsMap @k @nm) of
  Just f -> Just f
  Nothing -> Just (prettyNode @_ @k @nm)
getNodePrinter (t : tags) = case Map.lookup t (tagsMap @k @nm) of
  Just f -> Just f
  Nothing -> getNodePrinter @k @nm tags

-- | Inspect one level of a 'TraceTreeNode', returning the
--   contents in the order that they were added.
viewTraceTreeNode ::
  forall k nm.
  TraceTreeNode k nm ->
  IO [((TraceNodeType k nm, TraceNodeLabel nm), TraceTree k)]
viewTraceTreeNode (TraceTreeNode subtrees) = reverse <$> evalIOList subtrees

getNodeStatus ::
  forall k nm.
  TraceTreeNode k nm ->
  IO NodeStatus
getNodeStatus (TraceTreeNode subtrees) = getIOListStatus subtrees

-- | Retrieve the top-level list of nodes for a 'TraceTree' in
--   the order that they were added.
viewTraceTree ::
  TraceTree k ->
  IO [(Some (TraceTreeNode k))]
viewTraceTree (TraceTree ls) = reverse <$> evalIOList ls

getTreeStatus ::
  forall k.
  TraceTree k ->
  IO NodeStatus
getTreeStatus (TraceTree ls) = getIOListStatus ls


data SomeTraceTree' (tp :: l -> Type) =
    StartTree
  -- ^ a trace tree that we intend to build but hasn't been initialized yet
  | forall (k :: l). SomeTraceTree' (tp k) (TreeBuilder k) (TraceTree k)

-- The 'tp' parameter stands for the type of a singleton value that any
-- valid tree should have (i.e. a witness to the validity of the tree)
-- We could make this fully polymorphic (i.e. make tp :: forall l. l -> Type), to
-- account for cases where the kind of the type parameters to the tree isn't
-- statically known, but this seem excessive for most use cases.
data SomeTraceTree (tp :: l -> Type) =
    SomeTraceTree (IO.IORef (SomeTraceTree' tp)) (forall (k :: l). TraceTree k -> IO ())
  -- a reference to the underlying tracetree, either pending to start or
  -- the current state
  -- also a hook that is executed once the trace tree is started (or restarted)
  | NoTreeBuild

forkTraceTreeHook :: forall l (tp :: l -> Type).
  (forall (k :: l). TraceTree k -> IO ()) ->
  SomeTraceTree tp ->
  IO (SomeTraceTree tp)
forkTraceTreeHook f NoTreeBuild = do
  stt <- someTraceTree
  forkTraceTreeHook f stt
forkTraceTreeHook f (SomeTraceTree ref g) = do
  (mv :: MVar (Some TraceTree)) <- newEmptyMVar
  let go = do
        Some t <- takeMVar mv
        f t

  _ <- IO.forkIO go
  return $ SomeTraceTree ref (\t -> g t >> putMVar mv (Some t))

someTraceTree :: forall tp. IO (SomeTraceTree tp)
someTraceTree = do
  ref <- IO.newIORef StartTree
  return $ SomeTraceTree ref (\_ -> return ())

noTraceTree :: forall tp. SomeTraceTree tp
noTraceTree = NoTreeBuild

noTreeBuilder :: TreeBuilder k
noTreeBuilder = TreeBuilder (\_ -> return ()) noNodeBuilder (\_ -> return ()) DefaultChoice

noNodeBuilder :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
noNodeBuilder = do
  -- todo: add constructor for IOList that is always empty?
  l <- mkStaticIOList []
  let noStart = do
        t <- TraceTree <$> mkStaticIOList []
        return (t, noTreeBuilder)
  let builder = NodeBuilder (\_ -> return ()) noStart (\_ _ _ -> return ())
  return $ (TraceTreeNode l, builder)

viewSomeTraceTree ::
  forall tp a.
  SomeTraceTree tp ->
  (IO a) {- ^ action for when no tree is loaded -} ->
  (forall k. tp k -> TraceTree k -> IO a) ->
  IO a
viewSomeTraceTree NoTreeBuild noTreeFn _ = noTreeFn
viewSomeTraceTree (SomeTraceTree ref _) noTreeFn f = do
  t <- IO.readIORef ref
  case t of
    SomeTraceTree' validRepr _ (t' :: TraceTree k) -> f @k validRepr t'
    StartTree -> noTreeFn

newtype SomeSymRepr = SomeSymRepr (SomeSym SymbolRepr)

instance Eq SomeSymRepr where
  (SomeSymRepr (SomeSym s1)) == (SomeSymRepr (SomeSym s2)) = case testEquality s1 s2 of
    Just Refl -> True
    Nothing -> False

-- named subtrees
instance IsTraceNode k "subtree" where
  type TraceNodeType k "subtree" = String
  type TraceNodeLabel "subtree" = SomeSymRepr
  prettyNode lbl nm = prettyTree lbl nm
  nodeTags = [(Summary, prettyTree),
              (Simplified_Detail, \_ nm -> PP.pretty nm),
              (Simplified, \_ nm -> PP.pretty nm)
              ]
  jsonNode _ (SomeSymRepr (SomeSym r)) nm = return $
    JSON.object [ "subtree_kind" JSON..=  (show (symbolRepr r))
                , "message" JSON..= nm
                ]

prettyTree ::
  SomeSymRepr ->
  String ->
  PP.Doc a
prettyTree (SomeSymRepr (SomeSym lbl)) nm = PP.pretty nm <> "::[" <> PP.pretty (symbolRepr lbl) <> "]"

-- ad-hoc messages
instance IsTraceNode k "message" where
  type TraceNodeType k "message" = String
  prettyNode () msg = PP.pretty msg
  nodeTags = mkTags @k @"message" [Summary, Simplified]

instance IsTraceNode k "debug" where
  type TraceNodeType k "debug" = String
  type TraceNodeLabel "debug"= String
  prettyNode lbl msg = case lbl of
    "" -> PP.pretty msg
    _ -> PP.vsep [PP.pretty lbl, PP.pretty msg]
  nodeTags = [("debug", \lbl msg -> case lbl of {"" -> PP.pretty msg; _ -> PP.pretty lbl})]

instance IsTraceNode k "debug_tree" where
  type TraceNodeType k "debug_tree" = String
  prettyNode () msg = PP.pretty msg
  nodeTags = mkTags @k @"debug_tree" ["debug"]


instance IsTraceNode k "bool" where
  type TraceNodeType k "bool" = Bool
  type TraceNodeLabel "bool" = String
  prettyNode msg b = PP.pretty msg <> ":" PP.<+> PP.pretty b

-- | Dummy trace node to hold the final result of the analysis
instance IsTraceNode k "final_result" where
  type TraceNodeType k "final_result" = ()
  prettyNode _lbl _msg = "Final Result"
  nodeTags = mkTags @k @"final_result" [Summary, Simplified]

data ChoiceHeader k (nm_choice :: Symbol) a = 
  (IsTraceNode k nm_choice) =>
    ChoiceHeader { choiceType :: SymbolRepr nm_choice
                 , choiceSelected :: IO ()
                 -- ^ run to unblock the ready check
                 , waitForChoice :: IO ()
                 -- ^ blocks until some choice has been made
                 , choiceReady :: IO Bool
                 -- ^ true if a choice has been made
                 } 

data SomeChoiceHeader k = forall nm_choice nm_ret. SomeChoiceHeader (ChoiceHeader k nm_choice nm_ret)

instance IsTraceNode k "choiceTree" where
  type TraceNodeType k "choiceTree" = SomeChoiceHeader k
  type TraceNodeLabel "choiceTree" = String
  prettyNode lbl (SomeChoiceHeader (ChoiceHeader nm_choice _ _ _)) = prettyTree (SomeSymRepr (SomeSym nm_choice)) lbl
  nodeTags = 
    [(Summary, \lbl ((SomeChoiceHeader (ChoiceHeader nm_choice _ _ _))) -> prettyTree (SomeSymRepr (SomeSym nm_choice)) lbl)
    ,(Simplified_Detail, \nm _ -> PP.pretty nm)
    ,(Simplified, \nm _ -> PP.pretty nm)
    ]

data Choice k (nm_choice :: Symbol) a = 
  Choice { choiceHeader :: ChoiceHeader k nm_choice a
         , choiceLabel :: TraceNodeLabel nm_choice
         , choiceLabelValue ::  TraceNodeType k nm_choice
         , choiceValue :: IO (a)
         , choicePick :: IO ()
         -- ^ executed by some interactive client to indicate
         -- this is the desired choice
         , choiceChosen :: IO Bool
         -- ^ returns True if this is the desired choice
         }

data SomeChoice k = forall nm_choice nm_ret. 
  IsTraceNode k nm_choice => 
    SomeChoice (Choice k nm_choice nm_ret)


prettyChoice :: forall k nm_choice nm_ret a. Choice k nm_choice nm_ret -> PP.Doc a
prettyChoice c = (\(ChoiceHeader{}) -> 
  prettyNode @_ @k @nm_choice (choiceLabel c) (choiceLabelValue c)) (choiceHeader c)

instance IsTraceNode k "choice" where
  type TraceNodeType k "choice" = SomeChoice k
  type TraceNodeLabel "choice" = String
  prettyNode nm (SomeChoice c) = case nm of
    "" -> prettyChoice c
    _ -> PP.pretty nm PP.<+> prettyChoice c
  nodeTags = mkTags @k @"choice" [Summary, Simplified]
  jsonNode core _ (SomeChoice (c :: Choice k nm_choice nm_ret))= jsonNode @_ @k @nm_choice core (choiceLabel c) (choiceLabelValue c)

instance IsTraceNode k "()" where
  type TraceNodeType k "()" = ()
  type TraceNodeLabel "()" = ()
  prettyNode () () = PP.emptyDoc
  nodeTags = mkTags @k @"()" [Summary, Simplified]

-- | Returns the unblocking action
setBlockedStatus ::
  IsTreeBuilder k e m =>
  m (IO ())
setBlockedStatus = do
  builder <- getTreeBuilder
  case interactionMode builder of
    Interactive nextChoiceIdent -> do
      newChoiceIdent <- liftIO $ nextChoiceIdent
      let status = NodeStatus StatusSuccess False (BlockedStatus (Set.singleton newChoiceIdent) Set.empty)
      liftIO $ updateTreeStatus builder status
      let statusFinal = NodeStatus StatusSuccess True (BlockedStatus Set.empty (Set.singleton newChoiceIdent))
      return $ updateTreeStatus builder statusFinal
    DefaultChoice -> return (return ())

addStatusBlocker ::
  IsTreeBuilder k e m =>
  ChoiceHeader k nm_choice a ->
  m (ChoiceHeader k nm_choice a)
addStatusBlocker header = do
  unblock <- setBlockedStatus
  return $ header { choiceSelected = choiceSelected header >> unblock }

chooseHeader ::
  forall nm_choice a k m e.
  IsTreeBuilder k e m =>
  IsTraceNode k nm_choice =>
  Bool ->
  String ->
  (ChoiceHeader k nm_choice a -> NodeBuilderT k "choice" m ()) ->
  m (ChoiceHeader k nm_choice a)
chooseHeader blocking treenm f = do
  builder <- getTreeBuilder
  (header :: ChoiceHeader k nm_choice a) <- case interactionMode builder of
    Interactive _ -> do
      c <- liftIO $ newEmptyMVar
      let isReady = not <$> isEmptyMVar c
      return $ ChoiceHeader knownSymbol (tryPutMVar c () >> return ()) (readMVar c) isReady
    DefaultChoice -> return $ ChoiceHeader knownSymbol (return ()) (return ()) (return True)
  withSubTraces $
    subTraceLabel @"choiceTree" @k @m treenm (SomeChoiceHeader header) $ do
      header' <- if blocking then addStatusBlocker header else return header
      withSubTraces @"choice" @k (f header' >> return header')

mkChoice ::
  forall nm_choice a k m.
  MonadTreeBuilder k m =>
  IO.MonadUnliftIO m =>
  ChoiceHeader k nm_choice a ->
  TraceNodeLabel nm_choice ->
  TraceNodeType k nm_choice ->
  m a ->
  m (Choice k nm_choice a)
mkChoice header label labelV f = do
  builder <- getTreeBuilder
  case interactionMode builder of
    Interactive _ -> do
      inIO <- IO.askRunInIO
      c <- liftIO $ newMVar False
      return $ Choice header label labelV (inIO f) (swapMVar c True >> choiceSelected header) (readMVar c)
    DefaultChoice -> do
      inIO <- IO.askRunInIO
      return $ Choice header label labelV (inIO f) (choiceSelected header >> return ()) (return True)

choice_ ::
  forall nm_choice a k m e.
  IO.MonadUnliftIO m =>
  IsTreeBuilder k e m =>
  IsTraceNode k nm_choice =>
  ChoiceHeader k nm_choice a ->
  String ->
  TraceNodeLabel nm_choice ->
  TraceNodeType k nm_choice ->
  m a ->
  NodeBuilderT k "choice" (WriterT [Choice k nm_choice a] m) ()
choice_ header name label v f = do
  c <- lift $ lift $ mkChoice header label v f
  subTraceLabel name (SomeChoice c) (return ())
  lift $ tell [c]
  return ()

getChoice ::
  forall k m nm_choice a.
  MonadIO m =>
  --IsTreeBuilder k e m =>
  [Choice k nm_choice a] ->
  m (Maybe a)
getChoice choices = go choices
  where
    go :: [Choice k nm_choice a] -> m (Maybe a)
    go [] = return Nothing
    go (c : choices') = (liftIO $ choiceChosen c) >>= \case
      True  -> Just <$> (liftIO $ choiceValue c)
      False -> go choices'

-- | Interactively select one result from a list of choices
chooseLabel ::
  forall nm_choice a k m e.
  IsTreeBuilder k e m =>
  IO.MonadUnliftIO m =>
  IsTraceNode k nm_choice =>
  String ->
  (forall m'. Monad m' => (String -> TraceNodeLabel nm_choice -> TraceNodeType k nm_choice -> m a -> m' ()) ->
    m' ()) ->
  m a
chooseLabel treenm f = do
  (header, choices) <- runWriterT (chooseHeader @nm_choice @a @k True treenm (\header -> f (choice_ header)))
  case null choices of
    True -> liftIO $ fail $ "choose: at least one option required (" ++ treenm ++ ")"
    False -> do
      builder <- getTreeBuilder
      case interactionMode builder of
        Interactive _ -> do
          () <- liftIO $ waitForChoice header
          getChoice choices >>= \case
            Just a -> return a
            Nothing -> liftIO $ fail $ "choose: no value available (" ++ treenm ++ ")"
        -- default choice is simply the first one
        DefaultChoice -> do
          (liftIO $ choiceValue (head choices))

data LazyIOAction b a = LazyIOAction { lazyActionReady :: IO Bool, runLazyAction :: b -> IO (Maybe a) }

-- | A non-blocking variant of 'choose', that instead lets the caller decide
--   how to handle a choice being made.
--   TODO: Once we have a result we're currently re-running the corresponding action
--   each time this is queried, so it's up to the caller to discard the continuation
--   once it has a result.
chooseLazy ::
  forall nm_choice a b k m e.
  IsTreeBuilder k e m =>
  IsTraceNode k nm_choice =>
  IO.MonadUnliftIO m =>
  Default (TraceNodeLabel nm_choice) =>
  String ->
  (forall m'. Monad m' => (String -> TraceNodeType k nm_choice -> (b -> IO a) -> m' ()) ->
    m' ()) ->
  m (LazyIOAction b a)
chooseLazy treenm f = do
  builder <- getTreeBuilder
  -- TODO: this is a bit gross, but easiest to implement
  -- in general maybe choices should always take input
  inputVar <- liftIO $ newEmptyMVar
  case interactionMode builder of
    Interactive{} -> do
      (header, choices) <- runWriterT (chooseHeader @nm_choice @a @k False treenm (\header -> f (\nm v g -> choice_ header nm def v (liftIO $ (readMVar inputVar) >>= g))))
      return $ LazyIOAction (liftIO $ choiceReady header) $ \inputVal -> do
        (liftIO $ choiceReady header) >>= \case
          True -> do
            liftIO $ putMVar inputVar inputVal
            getChoice choices
          False -> return Nothing
    DefaultChoice -> return $ LazyIOAction (return False) (\_ -> return Nothing)

choose ::
  forall nm_choice a k m e.
  IsTreeBuilder k e m =>
  IO.MonadUnliftIO m =>
  IsTraceNode k nm_choice =>
  Default (TraceNodeLabel nm_choice) =>
  String ->
  (forall m'. Monad m' => (String -> TraceNodeType k nm_choice -> m a -> m' ()) ->
    m' ()) ->
  m a
choose treenm f = chooseLabel @nm_choice treenm (\choice -> f (\nm v g -> choice nm def v g))

chooseBool ::
  forall k m e.
  IsTreeBuilder k e m =>
  IO.MonadUnliftIO m =>
  String ->
  m Bool
chooseBool treenm = choose @"bool" treenm $ \choice -> do
  choice "" True $ return True
  choice "" False $ return False

class Monad m => MonadTreeBuilder k m | m -> k where
  getTreeBuilder :: m (TreeBuilder k)
  withTreeBuilder :: forall a. TreeBuilder k -> m a -> m a

newtype NoTreeBuilder k m a = NoTreeBuilder (m a)
  deriving (Applicative, Functor, Monad, MonadIO, MonadThrow)

instance Monad m => MonadTreeBuilder k (NoTreeBuilder k m) where
  getTreeBuilder = return $ noTreeBuilder
  withTreeBuilder _ = id

instance MonadTreeBuilder k m => MonadTreeBuilder k (StateT s m) where
  getTreeBuilder = lift $ getTreeBuilder
  withTreeBuilder tb f = do
    s <- get
    (a,s') <- lift $ withTreeBuilder tb (runStateT f s)
    put s'
    return a

noTracing :: NoTreeBuilder k m a -> m a
noTracing (NoTreeBuilder f) = f

instance MonadError e m => MonadError e (NoTreeBuilder k m) where
  throwError e = NoTreeBuilder $ throwError e
  catchError (NoTreeBuilder f) g = NoTreeBuilder $ catchError f (\e -> noTracing (g e))

resetSomeTreeBuilder ::
  forall m tp.
  IO.MonadIO m =>
  SomeTraceTree tp ->
  m ()
resetSomeTreeBuilder NoTreeBuild = return ()
resetSomeTreeBuilder (SomeTraceTree ref f) = (IO.liftIO $ IO.readIORef ref) >>= \case
  StartTree -> return ()
  SomeTraceTree' _ _ tt@(TraceTree l) -> liftIO $ do
    resetIOList l
    f tt

startSomeTreeBuilder ::
  forall k m tp.
  IO.MonadIO m =>
  tp k ->
  SomeTraceTree tp ->
  m (TreeBuilder k)
startSomeTreeBuilder _ NoTreeBuild = return noTreeBuilder
startSomeTreeBuilder validRepr someTree@(SomeTraceTree ref f) = (IO.liftIO $ IO.readIORef ref) >>= \case
  StartTree -> do
    (tree, builder) <- IO.liftIO $ startTree @k
    IO.liftIO $ IO.writeIORef ref (SomeTraceTree' validRepr builder tree)
    -- IO.liftIO $ IO.putStrLn "Starting tree hook.."
    IO.liftIO $ f tree
    -- IO.liftIO $ IO.putStrLn "Started!"
    return builder
  -- If a tree has already started we need to just throw it away and start again
  SomeTraceTree'{} -> do
    IO.liftIO $ IO.writeIORef ref StartTree
    startSomeTreeBuilder validRepr someTree

liftTreeBuilder :: forall k nm m a.
  MonadTreeBuilder k m =>
  TreeBuilder k ->
  m a ->
  NodeBuilderT k nm m a
liftTreeBuilder treeBuilder f = CMR.lift (withTreeBuilder treeBuilder f)


newtype TreeBuilderT k m a = TreeBuilderT (CMR.ReaderT (TreeBuilder k) m a)
  deriving (Functor, Applicative, Monad, CMT.MonadTrans, IO.MonadIO, MonadThrow, MonadCatch, MonadMask)

instance CMR.MonadReader r m => CMR.MonadReader r (TreeBuilderT k m) where
  ask = TreeBuilderT $ lift CMR.ask
  local f g = TreeBuilderT $ do
    treeBuilder <- CMR.ask
    lift $ CMR.local f (runTreeBuilderT g treeBuilder)

instance Monad m => MonadTreeBuilder k (TreeBuilderT k m) where
  getTreeBuilder = TreeBuilderT CMR.ask
  withTreeBuilder treeBuilder (TreeBuilderT f) = TreeBuilderT $ CMR.local (\_ -> treeBuilder) f


instance MonadTreeBuilder k m => MonadTreeBuilder k (MaybeT m) where
  getTreeBuilder = CMT.lift getTreeBuilder
  withTreeBuilder treeBuilder (MaybeT f) =
    MaybeT $ withTreeBuilder treeBuilder f

instance (MonadTreeBuilder k m, Monoid w) => MonadTreeBuilder k (WriterT w m) where
  getTreeBuilder = CMT.lift getTreeBuilder
  withTreeBuilder treeBuilder (WriterT f) =
    WriterT $ withTreeBuilder treeBuilder f

instance (MonadTreeBuilder k m) => MonadTreeBuilder k (ExceptT e m) where
  getTreeBuilder = CMT.lift getTreeBuilder
  withTreeBuilder treeBuilder f = ExceptT $ withTreeBuilder treeBuilder (runExceptT f)

instance (MonadError e m, MonadTreeBuilder k m) => MonadTreeBuilder k (AltT e m) where
  getTreeBuilder = CMT.lift getTreeBuilder
  withTreeBuilder treeBuilder (AltT f) = AltT $ withTreeBuilder treeBuilder f

runTreeBuilderT :: TreeBuilderT k m a -> TreeBuilder k -> m a
runTreeBuilderT (TreeBuilderT f) treeBuilder  = CMR.runReaderT f treeBuilder

deriving instance MonadError e m => MonadError e (TreeBuilderT k m)

newtype NodeBuilderT k nm m a = NodeBuilderT (CMR.ReaderT (NodeBuilder k nm) m a)
  deriving (Functor, Applicative, Monad, IO.MonadIO, CMR.MonadTrans, CMR.MonadReader (NodeBuilder k nm))

deriving instance Alternative m => Alternative (NodeBuilderT k nm m)


instance IO.MonadUnliftIO m => IO.MonadUnliftIO (NodeBuilderT k nm m) where
  withRunInIO f = do
    nodeBuilder <- getNodeBuilder
    lift $ IO.withRunInIO $ \inIO ->
      f (\x -> inIO (runNodeBuilderT x nodeBuilder))

-- Running alternative executions in a context where failure raises
-- a special exception, so it can be captured by the subtrace handlers

data AltErr e =
    AltErr
  | InnerErr e

instance Show e => Show (AltErr e) where
  show = \case
    AltErr -> "Alternative not taken"
    InnerErr e -> show e

instance IsNodeError e => IsNodeError (AltErr e) where
  propagateErr = \case
    AltErr -> False
    InnerErr e -> propagateErr e

newtype AltT e m a = AltT (ExceptT (AltErr e) m a)
  deriving (Functor, Applicative, Monad, IO.MonadIO, CMT.MonadTrans, MonadError (AltErr e))

runAltT :: MonadError e m => AltT e m a -> m (Maybe a)
runAltT (AltT f) = runExceptT f >>= \case
  Left AltErr -> return Nothing
  Left (InnerErr e) -> throwError e
  Right r -> return $ Just r


maybeToAlt :: MonadError e m => MaybeT m a -> AltT e m a
maybeToAlt f = (lift $ runMaybeT f) >>= \case
  Just r -> return r
  Nothing -> empty


instance Monad m => Alternative (AltT e m) where
  empty = AltT (throwError AltErr)
  (AltT f) <|> (AltT g) = AltT $ catchError f $ \e -> case e of
    AltErr -> g
    InnerErr{} -> throwError e

deriving instance MonadError e m => MonadError e (NodeBuilderT k nm m)
   

runNodeBuilderT :: NodeBuilderT k nm m a -> NodeBuilder k nm -> m a
runNodeBuilderT (NodeBuilderT f) nodeBuilder = CMR.runReaderT f nodeBuilder

getNodeBuilder :: forall k nm m. Monad m => NodeBuilderT k nm m (NodeBuilder k nm)
getNodeBuilder = NodeBuilderT $ CMR.ask

type IsTreeBuilder k e m =
  (IO.MonadIO m, MonadError e m, IsNodeError e, MonadTreeBuilder k m)

withSubTraces ::
  forall nm k m e a.
  IsTreeBuilder k e m =>
  IsTraceNode k nm =>
  NodeBuilderT k nm m a ->
  m a
withSubTraces f = do
  treeBuilder <- getTreeBuilder
  (node, nodeBuilder') <- IO.liftIO ((startNode treeBuilder) @nm )
  let nodeBuilder = addTreeDependency treeBuilder nodeBuilder'
  IO.liftIO $ addNode treeBuilder node  
  r <- catchError
        (runNodeBuilderT f nodeBuilder >>= \r -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeStatus StatusSuccess True mempty)) >> return r)
        (\e -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeStatus (StatusError e) True mempty)) >> throwError e)
  return r

subTraceLabel' ::
  forall nm k m e a.
  IsTreeBuilder k e m =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  ((forall b. NodeBuilderT k nm m b -> m b) -> m a) ->
  NodeBuilderT k nm m a
subTraceLabel' lbl v f = do
  nodeBuilder <- getNodeBuilder @k @nm @m
  (subtree, treeBuilder') <- IO.liftIO $ startTreeFromNode nodeBuilder
  let treeBuilder = addNodeDependency nodeBuilder treeBuilder'
  IO.liftIO $ addNodeValue nodeBuilder lbl v subtree
  r <- catchError
        (liftTreeBuilder treeBuilder (f (\g -> runNodeBuilderT g nodeBuilder))
          >>= \r -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus StatusSuccess True mempty)) >> return r)
        (\e -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusError e) True mempty)) >> throwError e)
  return r

subTraceLabel ::
  forall nm k m e a.
  IsTreeBuilder k e m =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  m a ->
  NodeBuilderT k nm m a
subTraceLabel lbl v f = subTraceLabel' lbl v (\_ -> f)

-- | Tag the current sub-computation as having raised a warning
emitTraceWarning ::
  forall k m e.
  IsTreeBuilder k e m =>
  e ->
  m ()
emitTraceWarning e = do
  treeBuilder <- getTreeBuilder
  IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusWarning e) False mempty)

-- | Tag the current sub-computation as having raised an error
emitTraceError ::
  forall k m e.
  IsTreeBuilder k e m =>
  e ->
  m ()
emitTraceError e = do
  treeBuilder <- getTreeBuilder
  IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusError e) False mempty)

finalizeTree ::
  TreeBuilder k ->
  IO ()
finalizeTree treeBuilder = updateTreeStatus treeBuilder (NodeStatus StatusSuccess True mempty)

traceAlternatives' ::
  IsTreeBuilder k e m =>
  [(String, MaybeT m a)] ->
  NodeBuilderT k "function_name" (AltT e m) a
traceAlternatives' [] = lift $ empty
traceAlternatives' ((nm, f) : alts) =
  (subTrace @"function_name" nm (maybeToAlt f)) <|> traceAlternatives' alts

instance IsTraceNode (k :: l) "function_name" where
  type TraceNodeType k "function_name" = String
  prettyNode () st = PP.pretty st
  nodeTags = [(Summary, \() -> PP.pretty)
             , (Simplified, \() _ -> "------")
             ]

traceAlternatives ::
  IsTreeBuilder k e m =>
  [(String, MaybeT m a)] ->
  MaybeT m a
traceAlternatives [] = fail ""
traceAlternatives alts = MaybeT $ runAltT $ withSubTraces (traceAlternatives' alts)


subTrace ::
  forall nm k m e a.
  IsTreeBuilder k e m =>
  IsTraceNode k nm =>
  Default (TraceNodeLabel nm) =>
  TraceNodeType k nm ->
  m a ->
  NodeBuilderT k nm m a
subTrace v f = subTraceLabel def v f

subTree ::
  forall nm k m e a.
  IsTreeBuilder k e m =>
  IsTraceNode k nm =>
  String ->
  NodeBuilderT k nm m a ->
  m a 
subTree treenm f = withSubTraces $ 
  subTraceLabel @"subtree" @k @m (SomeSymRepr (SomeSym (knownSymbol @nm))) treenm 
    $ withSubTraces @nm @k f


emitTraceLabel ::
  forall nm k m.
  IO.MonadIO m =>
  MonadTreeBuilder k m =>
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  m ()
emitTraceLabel lbl v = do
  treeBuilder <- getTreeBuilder
  node <- IO.liftIO $ singleNode @k @nm lbl v
  IO.liftIO $ addNode treeBuilder node

withTracingLabel ::
  forall nm k e m a.
  IsTreeBuilder k e m =>
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  m a ->
  m a
withTracingLabel lbl v f = withSubTraces @nm @k $ subTraceLabel lbl v f

withTracing ::
  forall nm k e m a.
  IsTreeBuilder k e m =>
  IsTraceNode k nm =>
  Default (TraceNodeLabel nm) =>
  TraceNodeType k nm ->
  m a ->
  m a
withTracing v f = withTracingLabel @nm @k def v f


emitTrace ::
  forall nm k m.
  IO.MonadIO m =>
  MonadTreeBuilder k m =>
  Default (TraceNodeLabel nm) =>
  IsTraceNode k nm =>
  TraceNodeType k nm ->
  m ()
emitTrace v = emitTraceLabel @nm def v

-- | Squelch tracing in this subcomputation
withNoTracing ::
  forall k e m a.
  IsTreeBuilder k e m =>
  m a ->
  m a
withNoTracing f = withTreeBuilder noTreeBuilder f
