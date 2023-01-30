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
  , viewSomeTraceTree
  , NodeStatus(..)
  , NodeStatusLevel(..)
  , getNodeStatus
  , getTreeStatus
  , MonadTreeBuilder(..)
  , NoTreeBuilder(..)
  , IsTreeBuilder
  , NodeBuilderT
  , TreeBuilderT
  , startSomeTreeBuilder
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
  , choose
  , ChoiceHeader(..)
  , SomeChoiceHeader(..)
  , Choice(..)
  , SomeChoice(..)
  ) where

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Data.Kind ( Type )
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.IO.Unlift as IO
import qualified Data.IORef as IO
import           Data.String
import qualified Data.Map as Map
import           Data.Map ( Map )
import           Data.Default
import           Control.Monad.Trans.Maybe
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Trans as CMT
import           Control.Monad.Except
import           Control.Monad.Catch
import           Control.Applicative

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr ( knownSymbol, symbolRepr, SomeSym(..), SymbolRepr )
import Control.Exception (IOException)
import Control.Monad.Trans.Writer
import Control.Concurrent.MVar

data TraceTag =
    Summary
  | Full
  | Simplified
  | Custom String
  deriving (Eq, Ord)


class Show e => IsNodeError e where
  propagateErr :: e -> Bool

instance IsNodeError IOException where
  propagateErr _ = True

data NodeStatusLevel =
    StatusSuccess
  | forall e. IsNodeError e => StatusWarning e
  | forall e. IsNodeError e => StatusError e

isHigherStatusLevel :: NodeStatusLevel -> NodeStatusLevel -> Bool
isHigherStatusLevel (StatusWarning _) StatusSuccess = True
isHigherStatusLevel (StatusError _) (StatusWarning _) = True
isHigherStatusLevel (StatusError _) StatusSuccess = True
isHigherStatusLevel _ _ = False

-- TODO: We could expose the error type here with some plumbing
data NodeStatus = NodeStatus { nodeStatusLevel :: NodeStatusLevel, isFinished :: Bool }

shouldPropagate :: NodeStatusLevel -> Bool
shouldPropagate StatusSuccess = False
shouldPropagate (StatusWarning e) = propagateErr e
shouldPropagate (StatusError e) = propagateErr e

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
  False -> case isHigherStatusLevel (nodeStatusLevel stNew) (nodeStatusLevel stOld) of
    True -> stNew
    False -> stOld { isFinished = isFinished stNew }

getIOListStatus :: IOList a -> IO NodeStatus
getIOListStatus l = ioListStatus <$> evalIOList' l

emptyIOList :: IO (IOList a)
emptyIOList = do
  r <- IO.liftIO $ IO.newIORef (IOList' [] (NodeStatus StatusSuccess False))
  return $ IOList r

data NodeBuilder k nm where
  NodeBuilder ::
    { updateNodeStatus :: NodeStatus -> IO ()
    , addNodeValue :: TraceNodeLabel nm -> TraceNodeType k nm -> TraceTree k -> IO ()
    } -> NodeBuilder k nm

data InteractionMode = 
    Interactive
  | DefaultChoice

data TreeBuilder k where
  TreeBuilder ::
    { updateTreeStatus :: NodeStatus -> IO ()
    , startNode :: forall nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
    , addNode :: forall nm. TraceTreeNode k nm -> IO ()
    , interactionMode :: InteractionMode
    -- ^ true if this treeBuilder can supply choices
    } -> TreeBuilder k

addNodeDependency :: NodeBuilder k nm -> TreeBuilder k -> TreeBuilder k
addNodeDependency nodeBuilder treeBuilder =
  let finish st = case shouldPropagate (nodeStatusLevel st) of
        -- importantly, we don't propagate regular status updates to ancestors,
        -- otherwise finalizing a child would cause all parents to finalize
        True -> updateNodeStatus nodeBuilder st >> updateTreeStatus treeBuilder st
        False -> updateTreeStatus treeBuilder st
  in treeBuilder { updateTreeStatus = finish } 

addTreeDependency :: TreeBuilder k -> NodeBuilder k nm -> NodeBuilder k nm
addTreeDependency treeBuilder nodeBuilder =
  let finish st = case shouldPropagate (nodeStatusLevel st) of
        True -> updateTreeStatus treeBuilder st >> updateNodeStatus nodeBuilder st
        False -> updateNodeStatus nodeBuilder st
  in nodeBuilder { updateNodeStatus = finish }

startTree :: forall k. IO (TraceTree k, TreeBuilder k)
startTree  = do
  l <- emptyIOList
  let builder = TreeBuilder (\st -> propagateIOListStatus st l) (startNode' @k) (\node -> addIOList (Some node) l) Interactive 
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
  modifyIOListStatus (\_ -> NodeStatus StatusSuccess True) t
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

  -- | Mapping from tracing tags to pretty-printers, allowing the contents
  --   of this node to be presented differently (or not at all) depending
  --   on what kind of printing is requested.
  nodeTags :: [(TraceTag, TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)]
  nodeTags = [(Summary, prettyNode @l @k @nm)]

mkTags :: forall k nm a. IsTraceNode k nm => [TraceTag] -> [(TraceTag, TraceNodeLabel nm -> TraceNodeType k nm -> PP.Doc a)]
mkTags tags = map (\tag -> (tag, prettyNode @_ @k @nm)) tags

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
        -- once a choice has been made, don't display the tree
        True -> return False
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


data SomeTraceTree' (tp :: l -> Type) =
    StartTree 
  -- ^ a trace tree that we intend to build but hasn't been initialized yet
  | forall (k :: l). SomeTraceTree' (tp k) (TreeBuilder k) (TraceTree k)

-- The 'tp' parameter stands for the type of a singleton value that any
-- valid tree should have (i.e. a witness to the validity of the tree)
-- We could make this fully polymorphic (i.e. make tp :: forall l. l -> Type), to
-- account for cases where the kind of the type parameters to the tree isn't
-- statically known, but this seem excessive for most use cases.
data SomeTraceTree tp =
    SomeTraceTree (IO.IORef (SomeTraceTree' tp))
  | NoTreeBuild

someTraceTree :: forall tp. IO (SomeTraceTree tp)
someTraceTree = do
  ref <- IO.newIORef StartTree
  return $ SomeTraceTree ref

noTraceTree :: forall tp. SomeTraceTree tp
noTraceTree = NoTreeBuild

noTreeBuilder :: TreeBuilder k
noTreeBuilder = TreeBuilder (\_ -> return ()) noNodeBuilder (\_ -> return ()) DefaultChoice

noNodeBuilder :: forall k nm. IsTraceNode k nm => IO (TraceTreeNode k nm, NodeBuilder k nm)
noNodeBuilder = do
  -- todo: add constructor for IOList that is always empty?
  l <- emptyIOList
  let builder = NodeBuilder (\_ -> return ()) (\_ _ _ -> return ())
  return $ (TraceTreeNode l, builder)

viewSomeTraceTree ::
  forall tp a.
  SomeTraceTree tp ->
  (IO a) {- ^ action for when no tree is loaded -} ->
  (forall k. tp k -> TraceTree k -> IO a) ->
  IO a
viewSomeTraceTree NoTreeBuild noTreeFn _ = noTreeFn
viewSomeTraceTree (SomeTraceTree ref) noTreeFn f = do
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
  nodeTags = [(Summary, prettyTree), (Simplified, \_ nm -> PP.pretty nm) ]

prettyTree ::
  SomeSymRepr ->
  String ->
  PP.Doc a
prettyTree (SomeSymRepr (SomeSym lbl)) nm = PP.pretty nm <> "::[" <> PP.pretty (symbolRepr lbl) <> "]"

-- ad-hoc messages
instance IsTraceNode k "message" where
  type TraceNodeType k "message" = String
  prettyNode () msg = PP.pretty msg
  nodeTags = [("message", \_ msg -> PP.pretty msg)]


instance forall k. IsTraceNode k "simplemessage" where
  type TraceNodeType k "simplemessage" = String
  prettyNode () msg = PP.pretty msg
  nodeTags = mkTags @k @"simplemessage" [Summary, Simplified]

instance IsTraceNode k "bool" where
  type TraceNodeType k "bool" = Bool
  type TraceNodeLabel "bool" = String
  prettyNode msg b = PP.pretty msg <> ":" PP.<+> PP.pretty b

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
    , (Simplified, \nm _ -> PP.pretty nm) ]

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

data SomeChoice k = forall nm_choice nm_ret. SomeChoice (Choice k nm_choice nm_ret)

prettyChoice :: forall k nm_choice nm_ret a. Choice k nm_choice nm_ret -> PP.Doc a
prettyChoice c = (\(ChoiceHeader{}) -> prettyNode @_ @k @nm_choice (choiceLabel c) (choiceLabelValue c)) (choiceHeader c)

instance IsTraceNode k "choice" where
  type TraceNodeType k "choice" = SomeChoice k
  type TraceNodeLabel "choice" = String
  prettyNode nm (SomeChoice c) = case nm of
    "" -> prettyChoice c
    _ -> PP.pretty nm <> ":" PP.<+> prettyChoice c
  nodeTags = mkTags @k @"choice" [Summary, Simplified]

choose_ ::
  forall nm_choice a k m e.
  IsTreeBuilder k e m =>
  IsTraceNode k nm_choice =>
  String ->
  (ChoiceHeader k nm_choice a -> NodeBuilderT k "choice" m ()) ->
  m (ChoiceHeader k nm_choice a)
choose_ treenm f = do
  builder <- getTreeBuilder
  (header :: ChoiceHeader k nm_choice a) <- case interactionMode builder of
    Interactive -> do
      c <- liftIO $ newEmptyMVar
      let isReady = not <$> isEmptyMVar c
      return $ ChoiceHeader knownSymbol (tryPutMVar c () >> return ()) (readMVar c) isReady
    DefaultChoice -> return $ ChoiceHeader knownSymbol (return ()) (return ()) (return True)

  withSubTraces $
    subTraceLabel @"choiceTree" @k @m treenm (SomeChoiceHeader header)
      $ withSubTraces @"choice" @k (f header >> return header)

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
    Interactive -> do
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
  forall k e m nm_choice a.
  IsTreeBuilder k e m =>
  ChoiceHeader k nm_choice a ->
  [Choice k nm_choice a] ->
  m a
getChoice header choices = do
  () <- liftIO $ waitForChoice header
  go choices
  where
    go :: [Choice k nm_choice a] -> m a
    go [] = liftIO $ fail "No choices"
    go (c : choices') = (liftIO $ choiceChosen c) >>= \case
      True  -> (liftIO $ choiceValue c)
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
  (header, choices) <- runWriterT (choose_ @nm_choice @a @k treenm (\header -> f (choice_ header)))
  getChoice header choices

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

class Monad m => MonadTreeBuilder k m | m -> k where
  getTreeBuilder :: m (TreeBuilder k)
  withTreeBuilder :: forall a. TreeBuilder k -> m a -> m a

newtype NoTreeBuilder k m a = NoTreeBuilder (m a)
  deriving (Applicative, Functor, Monad, MonadIO, MonadThrow)

instance Monad m => MonadTreeBuilder k (NoTreeBuilder k m) where
  getTreeBuilder = return $ noTreeBuilder
  withTreeBuilder _ = id

noTracing :: NoTreeBuilder k m a -> m a
noTracing (NoTreeBuilder f) = f

instance MonadError e m => MonadError e (NoTreeBuilder k m) where
  throwError e = NoTreeBuilder $ throwError e
  catchError (NoTreeBuilder f) g = NoTreeBuilder $ catchError f (\e -> noTracing (g e))

startSomeTreeBuilder ::
  forall k m tp.
  IO.MonadIO m =>
  tp k ->
  SomeTraceTree tp ->
  m (TreeBuilder k)
startSomeTreeBuilder _ NoTreeBuild = return noTreeBuilder
startSomeTreeBuilder validRepr someTree@(SomeTraceTree ref) = (IO.liftIO $ IO.readIORef ref) >>= \case
  StartTree -> do
    (tree, builder) <- IO.liftIO $ startTree @k
    IO.liftIO $ IO.writeIORef ref (SomeTraceTree' validRepr builder tree)
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
  deriving (Functor, Applicative, Monad, IO.MonadIO, CMR.MonadTrans)

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
        (runNodeBuilderT f nodeBuilder >>= \r -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeStatus StatusSuccess True)) >> return r)
        (\e -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeStatus (StatusError e) True)) >> throwError e)
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
  (subtree, treeBuilder') <- IO.liftIO $ startTree @k
  let treeBuilder = addNodeDependency nodeBuilder treeBuilder'
  IO.liftIO $ addNodeValue nodeBuilder lbl v subtree
  r <- catchError
        (liftTreeBuilder treeBuilder (f (\g -> runNodeBuilderT g nodeBuilder))
          >>= \r -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus StatusSuccess True)) >> return r)
        (\e -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusError e) True)) >> throwError e)
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
  IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusWarning e) False)

-- | Tag the current sub-computation as having raised an error
emitTraceError ::
  forall k m e.
  IsTreeBuilder k e m =>
  e ->
  m ()
emitTraceError e = do
  treeBuilder <- getTreeBuilder
  IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus (StatusError e) False)

finalizeTree ::
  TreeBuilder k ->
  IO ()
finalizeTree treeBuilder = updateTreeStatus treeBuilder (NodeStatus StatusSuccess True)

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
  nodeTags = [(Summary, \() -> PP.pretty), (Simplified, \() _ -> "------") ]

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
