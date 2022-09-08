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
  , TraceTag(..)
  , viewTraceTreeNode
  , viewTraceTree
  , findNode
  , asTreeKind
  , mkTraceTreeNode
  , mkTraceTree
  , ppTraceTreeNode
  , ppTraceTree
  , ppFullTraceTree
  , ppFullTraceTreeNode
  , def
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import qualified Control.Monad.IO.Class as IO
import           Data.String
import           Data.Maybe ( mapMaybe, fromJust )
import qualified Data.Map as Map
import           Data.Map ( Map )
import           Data.Default

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
    TraceNodeLabel nm ->
    [(TraceNodeType k nm, TraceTree k)] ->
    TraceTreeNode k nm

-- | A heterogenous list of 'TraceTreeNode' elements, representing
--   all of the tracing context that was emitted at this level
newtype TraceTree k = TraceTree [Some (TraceTreeNode k)]
  deriving ( Semigroup, Monoid )

class (KnownSymbol nm, Eq (TraceNodeLabel nm), Default (TraceNodeLabel nm)) => IsTraceNode (k :: l) (nm :: Symbol) where
  type TraceNodeType k nm :: Type

  -- | Labels can be used to distinguish nodes that share the same symbol in a
  --   'TraceTree'
  type TraceNodeLabel nm :: Type
  type TraceNodeLabel nm = ()
 
  -- | Pretty print the full contents of this node.
  --   This is the default printer when examining the node with
  --   respect to the 'Full' tag
  prettyNode :: TraceNodeType k nm -> PP.Doc a

  nodeTags :: [(TraceTag, TraceNodeType k nm -> PP.Doc a)]
  nodeTags = [(Summary, prettyNode @l @k @nm)]

tagsMap ::
  forall k nm a.
  IsTraceNode k nm =>
  Map TraceTag (TraceNodeType k nm -> PP.Doc a)
tagsMap = Map.fromList ((Full, prettyNode @_ @k @nm):nodeTags @_ @k @nm)

getNodePrinter ::
  forall k nm a.
  IsTraceNode k nm =>
  [TraceTag] ->
  Maybe (TraceNodeType k nm -> PP.Doc a)
getNodePrinter [] = Nothing
getNodePrinter (t : tags) = case Map.lookup t (tagsMap @k @nm) of
  Just f -> Just f
  Nothing -> getNodePrinter @k @nm tags

instance IsTraceNode k nm => Monoid (TraceTreeNode k nm) where
  mempty = TraceTreeNode def []

instance IsTraceNode k nm => Semigroup (TraceTreeNode k nm) where
  (TraceTreeNode nm subtrees1) <> (TraceTreeNode _ subtrees2) =
    (TraceTreeNode nm (subtrees1 <> subtrees2))

mkTraceTreeNode ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceNodeType k nm ->
  TraceNodeLabel nm ->
  TraceTree k ->
  m (TraceTreeNode k nm)
mkTraceTreeNode v lbl subtree = return $ TraceTreeNode lbl [(v, subtree)]

mkTraceTree ::
  forall nm k m.
  IO.MonadIO m =>
  TraceTreeNode k nm ->
  m (TraceTree k)
mkTraceTree n = return $ TraceTree [(Some n)]

-- | Inspect one level of a 'TraceTreeNode' and defer inspecting subtrees
--   Although the current implementation is pure, this is a
--   forward-compatible interface for a more robust implementation with
--   sharing and snapshots
viewTraceTreeNode ::
  IO.MonadIO m =>
  TraceTreeNode k nm ->
  m [(TraceNodeType k nm, m (TraceTree k))]
viewTraceTreeNode (TraceTreeNode _lbl subtrees) = return (map (\(v, t) -> (v, return t)) subtrees)

nodeLabel ::
  TraceTreeNode k nm -> TraceNodeLabel nm
nodeLabel (TraceTreeNode lbl _) = lbl

-- | Retrieve the top-level list of nodes for a 'TraceTree'
viewTraceTree ::
  IO.MonadIO m =>
  TraceTree k ->
  m [(Some (TraceTreeNode k))]
viewTraceTree (TraceTree ls) = return ls

-- | Find the first node in the top-level of a 'TraceTree'
--   that matches the Symbol constraint, if it exists.
findNode' ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceTree k ->
  (TraceNodeLabel nm -> Bool) ->
  m (Maybe (TraceTreeNode k nm))
findNode' (TraceTree []) _lbl = return Nothing
findNode' (TraceTree (x : xs)) lblCheck = case asTreeKind x of
  Just v | lblCheck (nodeLabel v) -> return (Just v)
  _ -> findNode' (TraceTree xs) lblCheck

findNode ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceTree k ->
  m (Maybe (TraceTreeNode k nm))  
findNode tree = findNode' tree ((==) def)

findNodeLabel ::
  forall nm k m.
  IO.MonadIO m =>
  IsTraceNode k nm =>
  TraceNodeLabel nm ->
  TraceTree k ->
  m (Maybe (TraceTreeNode k nm))    
findNodeLabel lbl tree = findNode' tree ((==) lbl)

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
ppTraceTreeNode tags ppSubTree (TraceTreeNode _ nodes) =
  case getNodePrinter @k @nm tags of
    Just prettyV -> Just $
      PP.vsep $
       (map (\(v, subtree) -> case ppSubTree subtree of
                     Just prettyTree -> PP.vsep [prettyV v, PP.indent 2 prettyTree]
                     Nothing -> prettyV v
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
