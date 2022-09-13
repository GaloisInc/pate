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
  , TraceTag(..)
  , viewTraceTreeNode
  , viewTraceTree
  , findNodes
  , nodeValue
  , nodeValueLabel
  , asTreeKind
  , mkTraceTreeNode
  , mkTraceTree
  , ppTraceTreeNode
  , ppTraceTree
  , ppFullTraceTree
  , ppFullTraceTreeNode
  , prettySummary
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import qualified Control.Monad.IO.Class as IO
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


-- | A labeled node in a 'TraceTree' that contains a list of sub-trees
--   annotated with values according to the 'IsTraceNode' class instance
--   for the given symbol.
--   The 'k' type parameter is used to provide additional parameters
--   to the type represented by 'nm' via the 'IsTraceNode' class
data TraceTreeNode (k :: l) nm where
  TraceTreeNode :: IsTraceNode k nm =>
    [((TraceNodeType k nm, TraceNodeLabel nm), TraceTree k)] ->
    TraceTreeNode k nm

-- | A heterogenous list of 'TraceTreeNode' elements, representing
--   all of the tracing context that was emitted at this level
newtype TraceTree k = TraceTree [Some (TraceTreeNode k)]
  deriving ( Semigroup, Monoid )

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

--  These functions assume that the IO monad is required to both inspect
--  and construct 'TraceTree' and 'TraceTreeNode' values. 
--  Although the current implementation is pure, this is a
--  forward-compatible interface for a more robust implementation with
--  sharing and snapshots


mkTraceTreeNode ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceNodeType k nm ->
  TraceNodeLabel nm ->
  TraceTree k ->
  m (TraceTreeNode k nm)
mkTraceTreeNode v lbl subtree = return $ TraceTreeNode [((v,lbl), subtree)]

-- | Collect a homogeneous list of nodes into a single 'TraceTreeNode'
--   and return a singleton 'TraceTree'
mkTraceTree ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  [TraceTreeNode k nm] ->
  m (TraceTree k)
mkTraceTree ns =
  let
    contents :: [((TraceNodeType k nm, TraceNodeLabel nm), TraceTree k)]
    contents = concat $ map (\(TraceTreeNode xs) -> xs) ns

    node :: TraceTreeNode k nm
    node = TraceTreeNode contents
  in return $ TraceTree [Some node]

-- | Inspect one level of a 'TraceTreeNode' and defer inspecting subtrees
viewTraceTreeNode ::
  forall k nm m.
  IO.MonadIO m =>
  TraceTreeNode k nm ->
  m [((TraceNodeType k nm, TraceNodeLabel nm), m (TraceTree k))]
viewTraceTreeNode (TraceTreeNode subtrees) = return (map (\(v, t) -> (v, return t)) subtrees)

-- | Retrieve the top-level list of nodes for a 'TraceTree'
viewTraceTree ::
  IO.MonadIO m =>
  TraceTree k ->
  m [(Some (TraceTreeNode k))]
viewTraceTree (TraceTree ls) = return ls

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
