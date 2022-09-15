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
  , finalizeNode
  , finalizeTree
  , SomeTraceTree
  , someTraceTree
  , noTraceTree
  , startSomeTraceTree
  , viewSomeTraceTree
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import qualified Control.Monad.IO.Class as IO
import qualified Data.IORef as IO
import           Data.String
import           Data.Maybe ( mapMaybe, fromJust )
import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr ( SymbolRepr, knownSymbol, symbolRepr )

data TraceTag =
    Summary
  | Full
  | Custom String
  deriving (Eq, Ord)

instance IsString TraceTag where
  fromString str = Custom str

-- | Allowing for lazy evaluation of trace trees

data IOList' a = IOList' { ioList :: [a], ioListFinal :: Bool }
newtype IOList a = IOList (IO.IORef (IOList' a))

evalIOList' :: IOList a -> IO (IOList' a)
evalIOList' (IOList ref) = do
  IO.liftIO $ IO.readIORef ref

evalIOList :: IOList a -> IO [a]
evalIOList l = ioList <$> evalIOList' l

addIOList :: a -> IOList a -> IO ()
addIOList a (IOList ref) =
  IO.modifyIORef ref (\(IOList' as isFinal) -> (IOList' (a : as) isFinal))

finalizeIOList :: IOList a -> IO ()
finalizeIOList (IOList ref) = IO.modifyIORef ref (\(IOList' as _) -> IOList' as True)

isFinalIOList :: IOList a -> IO Bool
isFinalIOList l = ioListFinal <$> evalIOList' l

emptyIOList :: IO (IOList a)
emptyIOList = do
  r <- IO.liftIO $ IO.newIORef (IOList' [] False)
  return $ IOList r

data NodeBuilder k nm where
  NodeBuilder ::
    { finalizeNode :: IO ()
    , addNodeValue :: TraceNodeLabel nm -> TraceNodeType k nm -> TraceTree k -> IO ()
    } -> NodeBuilder k nm

data TreeBuilder k where
  TreeBuilder ::
    { finalizeTree :: IO ()
    , startNode :: forall nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
    , addNode :: forall nm. TraceTreeNode k nm -> IO ()
    } -> TreeBuilder k

startTree :: forall k. IO (TraceTree k, TreeBuilder k)
startTree = do
  l <- emptyIOList
  let builder = TreeBuilder (finalizeIOList l) (startNode' @k) (\node -> addIOList (Some node) l) 
  return (TraceTree l, builder)

startNode' :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
startNode' = do
  l <- emptyIOList
  let builder = NodeBuilder (finalizeIOList l) $ \lbl v subtree ->
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

-- | Retrieve the top-level list of nodes for a 'TraceTree' in
--   the order that they were added.
viewTraceTree ::
  TraceTree k ->
  IO [(Some (TraceTreeNode k))]
viewTraceTree (TraceTree ls) = reverse <$> evalIOList ls

data SomeTraceTree' l =
    StartTree
  -- ^ a trace tree that we intend to build but hasn't been initialized yet
  | forall (k :: l). SomeTraceTree' (TraceTree k)

data SomeTraceTree l =
    SomeTraceTree (IO.IORef (SomeTraceTree' l))
  | NoTreeBuild

someTraceTree :: forall l. IO (SomeTraceTree l)
someTraceTree = do
  ref <- IO.newIORef StartTree
  return $ SomeTraceTree ref

noTraceTree :: SomeTraceTree l
noTraceTree = NoTreeBuild

noTreeBuilder :: TreeBuilder k
noTreeBuilder = TreeBuilder (return ()) noNodeBuilder (\_ -> return ())

noNodeBuilder :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
noNodeBuilder = do
  -- todo: add constructor for IOList that is always empty?
  l <- emptyIOList
  let builder = NodeBuilder (return ()) (\_ _ _ -> return ())
  return $ (TraceTreeNode l, builder)

startSomeTraceTree :: forall l (k :: l). SomeTraceTree l -> IO (TreeBuilder k)
startSomeTraceTree NoTreeBuild = return $ noTreeBuilder
startSomeTraceTree (SomeTraceTree ref) = do
  (tree, builder) <- startTree @k
  IO.writeIORef ref (SomeTraceTree' tree)
  return builder

viewSomeTraceTree ::
  forall l a.
  SomeTraceTree l ->
  (IO a) {- ^ action for when no tree is loaded -} ->
  (forall (k :: l). TraceTree k -> IO a) ->
  IO a
viewSomeTraceTree NoTreeBuild noTreeFn _ = noTreeFn
viewSomeTraceTree (SomeTraceTree ref) noTreeFn f = do
  t <- IO.readIORef ref
  case t of
    SomeTraceTree' (t' :: TraceTree k) -> f @k t'
    StartTree -> noTreeFn
    

{-
-- | Find all nodes in the given 'TraceTree' that match the given Symbol
--   (as implied by the 'nm' type parameter)
findNodes ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceTree k ->
  m [TraceTreeNode k nm]
findNodes (TraceTree xs) = return $ mapMaybe asTreeKind xs

nodeValue' ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  (TraceNodeLabel nm -> Bool) ->
  [TraceTreeNode k nm] ->
  m [TraceNodeType k nm]
nodeValue' lblCheck nodes =
  return $ concat $ map (\(TraceTreeNode xs) -> mapMaybe (\((x,lbl),_) -> if lblCheck lbl then Just x else Nothing) xs) nodes

-- | From the list of nodes, collect all values that have the given
--   label (ignoring subtrees)
nodeValueLabel ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  [TraceTreeNode k nm] ->
  m [TraceNodeType k nm]
nodeValueLabel lbl = nodeValue' (\lbl' -> lbl == lbl')

-- | From the list of nodes, collect all values
nodeValue ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  [TraceTreeNode k nm] ->
  m [TraceNodeType k nm]  
nodeValue = nodeValue' (\_ -> True)

-- | Return a 'Just' result if the given 'TraceTree' matches the given symbol
asTreeKind ::
  forall nm k.
  IsTraceNode k nm =>
  Some (TraceTreeNode k) ->
  Maybe (TraceTreeNode k nm)
asTreeKind (Some node@(TraceTreeNode{} :: TraceTreeNode k nm')) =
  case testEquality (knownSymbol @nm) (knownSymbol @nm') of
    Just Refl -> Just node
    Nothing -> Nothing


-- NOTE: We actually probably don't want to expose
-- pure versions of these printers, but its unclear if
-- it's worth writing the general printers in monadic form
-- or if we should just rely on some frontend to layout the tree
-- (where it will make assumptions about what kinds of nodes will
-- be present)
ppTraceTreeNode ::
  forall k nm a.
  [TraceTag] ->
  (TraceTree k -> Maybe (PP.Doc a)) ->
  TraceTreeNode k nm ->
  Maybe (PP.Doc a)
ppTraceTreeNode tags ppSubTree (TraceTreeNode nodes) =
  case getNodePrinter @k @nm tags of
    Just prettyV -> Just $
      PP.vsep $
       (map (\((v,lbl), subtree) -> case ppSubTree subtree of
                     Just prettyTree -> PP.vsep [prettyV lbl v, PP.indent 2 prettyTree]
                     Nothing -> prettyV lbl v
             ) nodes)      
    Nothing -> Nothing

ppTraceTree ::
  (forall nm. TraceTreeNode k nm -> Maybe (PP.Doc a)) ->
  TraceTree k ->
  PP.Doc a
ppTraceTree ppNode (TraceTree trees) =
  PP.vsep $ mapMaybe (\(Some node) -> ppNode node) trees

ppFullTraceTree ::
  forall k a.
  [TraceTag] ->
  TraceTree k ->
  PP.Doc a  
ppFullTraceTree tags tree_outer =
  let
    ppNode :: forall nm. TraceTreeNode k nm -> Maybe (PP.Doc a)
    ppNode node = ppTraceTreeNode tags ppTree node
    
    ppTree tree = Just (ppTraceTree ppNode tree)
  in fromJust (ppTree tree_outer)

ppFullTraceTreeNode ::
  forall k nm a.
  [TraceTag] ->
  TraceTreeNode k nm ->
  Maybe (PP.Doc a)
ppFullTraceTreeNode tags node_outer =
  let
    ppNode :: forall nm'. TraceTreeNode k nm' -> Maybe (PP.Doc a)
    ppNode node = ppTraceTreeNode tags ppTree node
    
    ppTree tree = Just (ppTraceTree ppNode tree)
  in ppNode node_outer

instance forall k nm. PP.Pretty (TraceTreeNode k nm) where
  -- the 'Full' tag is always defined
  pretty node = fromJust (ppFullTraceTreeNode [Full] node)

instance PP.Pretty (TraceTree k) where
  pretty tree = ppFullTraceTree [Full] tree
-}
