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

module Pate.TraceTree (
    TraceTree
  , TraceTreeNode
  , IsTraceNode(..)
  , isTraceNode
  , prettyNodeAt
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
  , startSomeTraceTree
  , viewSomeTraceTree
  , NodeStatus(..)
  , getNodeStatus
  , getTreeStatus
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import qualified Control.Monad.IO.Class as IO
import qualified Data.IORef as IO
import           Data.String
import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr ( knownSymbol, symbolRepr )

data TraceTag =
    Summary
  | Full
  | Custom String
  deriving (Eq, Ord)

data NodeStatus =
    NodeStatus { isFinished :: Bool }
  | NodeError { nodeError :: String, isFinished :: Bool }


instance IsString TraceTag where
  fromString str = Custom str

-- | Allowing for lazy evaluation of trace trees
data IOList' a = IOList' { ioList :: [a], ioListStatus :: NodeStatus }
newtype IOList a = IOList (IO.IORef (IOList' a))

evalIOList' :: IOList a -> IO (IOList' a)
evalIOList' (IOList ref) = do
  IO.liftIO $ IO.readIORef ref

evalIOList :: IOList a -> IO [a]
evalIOList l = ioList <$> evalIOList' l

addIOList :: a -> IOList a -> IO ()
addIOList a (IOList ref) =
  IO.modifyIORef ref (\(IOList' as st) -> (IOList' (a : as) st))

modifyIOListStatus :: (NodeStatus -> NodeStatus) -> IOList a -> IO ()
modifyIOListStatus f (IOList ref) = IO.modifyIORef ref (\(IOList' as st) -> IOList' as (f st))

propagateIOListStatus :: NodeStatus -> IOList a -> IO ()
propagateIOListStatus st l = modifyIOListStatus (propagateStatus st) l


propagateStatus :: NodeStatus -> NodeStatus -> NodeStatus
propagateStatus stNew stOld = case isFinished stOld of
  True -> stOld
  False -> case (stNew, stOld) of
   (NodeError _newErr newFin, NodeError oldErr _) -> NodeError oldErr newFin
   (NodeError newErr newFin, NodeStatus _) -> NodeError newErr newFin
   (NodeStatus True, _) -> stNew
   _ -> stOld

getIOListStatus :: IOList a -> IO NodeStatus
getIOListStatus l = ioListStatus <$> evalIOList' l

emptyIOList :: IO (IOList a)
emptyIOList = do
  r <- IO.liftIO $ IO.newIORef (IOList' [] (NodeStatus False))
  return $ IOList r

data NodeBuilder k nm where
  NodeBuilder ::
    { updateNodeStatus :: NodeStatus -> IO ()
    , addNodeValue :: TraceNodeLabel nm -> TraceNodeType k nm -> TraceTree k -> IO ()
    } -> NodeBuilder k nm

data TreeBuilder k where
  TreeBuilder ::
    { updateTreeStatus :: NodeStatus -> IO ()
    , startNode :: forall nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
    , addNode :: forall nm. TraceTreeNode k nm -> IO ()
    } -> TreeBuilder k

addNodeDependency :: NodeBuilder k nm -> TreeBuilder k -> TreeBuilder k
addNodeDependency nodeBuilder treeBuilder =
  let finish st = case st of
        -- importantly, we don't propagate regular status updates to ancestors,
        -- otherwise finalizing a child would cause all parents to finalize
        NodeStatus _ -> updateTreeStatus treeBuilder st
        _ -> updateNodeStatus nodeBuilder st >> updateTreeStatus treeBuilder st
  in treeBuilder { updateTreeStatus = finish } 

addTreeDependency :: TreeBuilder k -> NodeBuilder k nm -> NodeBuilder k nm
addTreeDependency treeBuilder nodeBuilder =
  let finish st = case st of
        NodeStatus _ -> updateNodeStatus nodeBuilder st
        _ -> updateTreeStatus treeBuilder st >> updateNodeStatus nodeBuilder st
  in nodeBuilder { updateNodeStatus = finish }

startTree :: forall k nm. IO (TraceTree k, TreeBuilder k)
startTree  = do
  l <- emptyIOList
  let builder = TreeBuilder (\st -> propagateIOListStatus st l) (startNode' @k) (\node -> addIOList (Some node) l) 
  return (TraceTree l, builder)

startNode' :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
startNode' = do
  l <- emptyIOList
  let builder = NodeBuilder (\st -> propagateIOListStatus st l) $ \lbl v subtree ->
        addIOList ((v, lbl), subtree) l
  return (TraceTreeNode l, builder)

singleNode ::
  forall k nm.
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  IO (TraceTreeNode k nm)
singleNode lbl v = do
  l <- emptyIOList
  t <- emptyIOList
  modifyIOListStatus (\_ -> NodeStatus True) t
  addIOList ((v, lbl), TraceTree t) l
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

class (KnownSymbol nm, Eq (TraceNodeLabel nm)) => IsTraceNode (k :: l) (nm :: Symbol)  where
  type TraceNodeType k nm :: Type

  -- | Labels can be used to distinguish nodes that share the same symbol in a
  --   'TraceTree'
  type TraceNodeLabel nm :: Type
  type TraceNodeLabel nm = ()
 
  -- | Pretty print the full contents of this node.
  --   This is the default printer when examining the node with
  --   respect to the 'Full' tag
  prettyNode :: TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a

  -- | Mapping from tracing tags to pretty-printers, allowing the contents
  --   of this node to be presented differently (or not at all) depending
  --   on what kind of printing is requested.
  nodeTags :: [(TraceTag, TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)]
  nodeTags = [(Summary, prettyNode @l @k @nm)]

prettySummary ::
  forall k nm a.
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceNodeType k nm ->
  Maybe (PP.Doc a)
prettySummary lbl v = prettyNodeAt @k @nm [Summary] lbl v

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

nodeShownAt ::
  forall k nm.
  IsTraceNode k nm =>
  [TraceTag] ->
  Bool
nodeShownAt tags = isJust (getNodePrinter @k @nm tags)

tagsMap ::
  forall k nm a.
  IsTraceNode k nm =>
  Map TraceTag (TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)
tagsMap = Map.fromList ((Full, prettyNode @_ @k @nm):nodeTags @_ @k @nm)

getNodePrinter ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  Maybe (TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)
getNodePrinter [] = Nothing
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

data SomeTraceTree' =
    StartTree
  -- ^ a trace tree that we intend to build but hasn't been initialized yet
  | forall k. SomeTraceTree' (TraceTree k)

data SomeTraceTree =
    SomeTraceTree (IO.IORef (SomeTraceTree'))
  | NoTreeBuild

someTraceTree :: IO (SomeTraceTree)
someTraceTree = do
  ref <- IO.newIORef StartTree
  return $ SomeTraceTree ref

noTraceTree :: SomeTraceTree
noTraceTree = NoTreeBuild

noTreeBuilder :: TreeBuilder k
noTreeBuilder = TreeBuilder (\_ -> return ()) noNodeBuilder (\_ -> return ())

noNodeBuilder :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
noNodeBuilder = do
  -- todo: add constructor for IOList that is always empty?
  l <- emptyIOList
  let builder = NodeBuilder (\_ -> return ()) (\_ _ _ -> return ())
  return $ (TraceTreeNode l, builder)

startSomeTraceTree :: forall k. SomeTraceTree -> IO (TreeBuilder k)
startSomeTraceTree NoTreeBuild = return $ noTreeBuilder
startSomeTraceTree (SomeTraceTree ref) = do
  (tree, builder) <- startTree @k
  IO.writeIORef ref (SomeTraceTree' tree)
  return builder

viewSomeTraceTree ::
  forall a.
  SomeTraceTree ->
  (IO a) {- ^ action for when no tree is loaded -} ->
  (forall l (k :: l). TraceTree k -> IO a) ->
  IO a
viewSomeTraceTree NoTreeBuild noTreeFn _ = noTreeFn
viewSomeTraceTree (SomeTraceTree ref) noTreeFn f = do
  t <- IO.readIORef ref
  case t of
    SomeTraceTree' (t' :: TraceTree k) -> f @_ @k t'
    StartTree -> noTreeFn
