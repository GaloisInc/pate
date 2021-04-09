{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module Interactive (
  consumeEvents,
  startInterface,
  StateRef,
  newState
  ) where

import qualified Control.Concurrent as CC
import           Control.Lens ( (^.), (%~), (&), (.~) )
import qualified Control.Lens as L
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.ByteString as BS
import qualified Data.FileEmbed as DFE
import qualified Data.IORef as IOR
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Foreign.JavaScript as FJ
import           Graphics.UI.Threepenny ( (#), (#+), (#.) )
import qualified Graphics.UI.Threepenny as TP
import           System.FilePath ( (</>) )
import qualified System.IO as IO
import qualified System.IO.Temp as SIT

import qualified Pate.Arch as PA
import qualified Pate.Event as PE
import qualified Pate.Proof as PPr
import qualified Pate.Types as PT

import qualified Interactive.Render.BlockPairDetail as IRB
import qualified Interactive.Render.Console as IRC
import qualified Interactive.Render.Proof as IRP
import           Interactive.State

-- | Embed the CSS we need into the Haskell to ensure that binaries can be relocatable
cssContent :: BS.ByteString
cssContent = $(DFE.embedFile "tools/pate/static/pate.css")

-- | This is our custom JS with extra functions called via JS FFI
jsContent :: BS.ByteString
jsContent = $(DFE.embedFile "tools/pate/static/pate.js")

-- | This is the full cytoscape library
cytoscape :: BS.ByteString
cytoscape = $(DFE.embedFile "tools/pate/static/cytoscape.js/dist/cytoscape.umd.js")

-- | This is an extension to cytoscape that enables labels to contain arbitrary
-- HTML (which we need for multi-line labels)
cytoscapeHtml :: BS.ByteString
cytoscapeHtml = $(DFE.embedFile "tools/pate/static/cytoscape-node-html-label/dist/cytoscape-node-html-label.js")

-- | The dagre graph layout library
dagre :: BS.ByteString
dagre = $(DFE.embedFile "tools/pate/static/dagre/dist/dagre.js")

-- | An adapter to use dagre as a layout engine in cytoscape
cytoscapeDagre :: BS.ByteString
cytoscapeDagre = $(DFE.embedFile "tools/pate/static/cytoscape.js-dagre/cytoscape-dagre.js")

consumeEvents :: CC.Chan (Maybe (PE.Event arch)) -> StateRef arch -> IO ()
consumeEvents chan r0 = do
  mEvt <- CC.readChan chan
  case mEvt of
    Nothing -> return ()
    Just evt -> do
      case evt of
        PE.LoadedBinaries (oelf, omap) (pelf, pmap) -> do
          IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & originalBinary .~ Just (oelf, omap)
                                                          & patchedBinary .~ Just (pelf, pmap), ())
        PE.ElfLoaderWarnings {} ->
          IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & recentEvents %~ addRecent recentEventCount evt, ())
        PE.CheckedEquivalence bpair@(PT.PatchPair (PE.Blocks blk _) _) res duration -> do
          let
            addr = PT.concreteAddress blk
            et = EquivalenceTest bpair duration
          case res of
            PE.Equivalent ->
              IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & successful %~ Map.insert addr et
                                                              & recentEvents %~ addRecent recentEventCount evt, ())
            PE.Inconclusive ->
              IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & indeterminate %~ Map.insert addr et
                                                              & recentEvents %~ addRecent recentEventCount evt, ())
            PE.Inequivalent model ->
              IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & failure %~ Map.insert addr (Failure model et)
                                                              & recentEvents %~ addRecent recentEventCount evt, ())
        PE.ProofIntermediate blockPair proofNode time ->
          IOR.atomicModifyIORef' (stateRef r0) $ \s -> ( s & recentEvents %~ addRecent recentEventCount evt
                                                           & proofTree %~ addProofTreeNode blockPair proofNode time
                                                       , ()
                                                       )
        PE.ProvenGoal {} ->
          IOR.atomicModifyIORef' (stateRef r0) $ \s -> (s & recentEvents %~ addRecent recentEventCount evt, ())
        _ -> return ()
      -- Notify the UI that we got a new result
      stateChangeEmitter r0 ()
      consumeEvents chan r0

recentEventCount :: Int
recentEventCount = 20

addRecent :: Int -> a -> [a] -> [a]
addRecent n elt elts = elt : take (n - 1) elts

-- | Start a persistent interface for the user to inspect data coming out of the
-- verifier
startInterface :: (PA.ArchConstraints arch) => StateRef arch -> IO ()
startInterface r = SIT.withSystemTempDirectory "pate" $ \tmpDir ->  do
  -- Place the content of all of our static dependencies into the temporary
  -- directory so that it can be served by threepenny
  --
  -- This approach is a bit more manual than the Cabal data files
  -- infrastructure, but allows the verifier to be relocatable easily
  BS.writeFile (tmpDir </> "cytoscape.umd.js") cytoscape
  BS.writeFile (tmpDir </> "cytoscape-node-html-label.js") cytoscapeHtml
  BS.writeFile (tmpDir </> "pate.css") cssContent
  BS.writeFile (tmpDir </> "pate.js") jsContent
  BS.writeFile (tmpDir </> "dagre.js") dagre
  BS.writeFile (tmpDir </> "cytoscape-dagre.js") cytoscapeDagre

  -- Set the port to 5000 to match the Dockerfile
  let uiConf = TP.defaultConfig { TP.jsPort = Just 5000
                                , TP.jsStatic = Just tmpDir
                                }
  TP.startGUI uiConf (uiSetup r)

snapshotProofState
  :: StateRef arch
  -> a
  -> TP.UI ()
snapshotProofState r _ = do
  liftIO $ IOR.modifyIORef' (stateRef r) snapshotProofTree
  liftIO $ proofChangeEmitter r ()

-- | The handler that will be invoked when the user asks for more detail for a
-- node in the proof tree
--
-- This renders all of the details we have into the detail pane (clobbering any
-- previous contents)
--
-- See Note [Proof Graph Interaction] on details of this interaction
onProofNodeClicked
  :: (PA.ArchConstraints arch)
  => StateRef arch
  -> TP.Window
  -- ^ The window object (so that we can get back into the 'TP.UI' monad)
  -> TP.Element
  -- ^ The detail div already in the document to populate
  -> Int
  -- ^ The identifier of the node the user clicked on
  --
  -- This is an 'Int' coming back from JS, but it is actually a nonce.  We can't
  -- convert it back safely, so we maintain the equivalence in the 'ProofTree'
  -- structure as a 'Map.Map'
  -> IO ()
onProofNodeClicked r wd detailDiv ident = do
  st <- IOR.readIORef (stateRef r)
  case st ^. activeProofTree of
    Just (ProofTree (PT.Sym {}) _nodes idx)
      | Just (Some (ProofTreeNode (PT.PatchPair ob pb) (PPr.ProofNonceExpr _ _ papp) tm)) <- Map.lookup ident idx -> TP.runUI wd $ do
          (g, origGraphSetup, patchedGraphSetup) <- IRB.renderBlockPairDetail st ob pb Nothing
          appDetail <- IRP.renderProofApp papp
          content <- TP.column [ return appDetail
                               , TP.string ("Duration: " ++ show tm)
                               , return g
                               ]
          void $ TP.set TP.children [content] (return detailDiv)
          origGraphSetup
          patchedGraphSetup
          TP.flushCallBuffer
    _ -> IO.hPutStrLn IO.stderr ("Error, missing proof node for id=" ++ show ident)

uiSetup :: (PA.ArchConstraints arch) => StateRef arch -> TP.Window -> TP.UI ()
uiSetup r wd = do
  st0 <- liftIO $ IOR.readIORef (stateRef r)
  void $ return wd # TP.set TP.title "PATE Verifier"
  void $ TP.getHead wd #+ [ TP.link # TP.set (TP.attr "rel") "stylesheet" # TP.set (TP.attr "href") "/static/pate.css"
                          ]
  consoleDiv <- TP.div #. "console-output-pane"
  summaryDiv <- TP.div #. "summary-pane"
  detailDiv <- TP.div #. "detail-pane"

  proofDiv <- TP.div #. "proof-pane"
  proofSnapshotButton <- TP.a # TP.set TP.text "[Snapshot]"
                              # TP.set TP.href "#snapshot"
  TP.on TP.click proofSnapshotButton (snapshotProofState r)

  void $ TP.getBody wd #+ [ TP.mkElement "script" # TP.set (TP.attr "src") "/static/cytoscape.umd.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/cytoscape-node-html-label.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/dagre.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/cytoscape-dagre.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/pate.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.h1 #+ [TP.string "Console Output"]
                          , return consoleDiv #+ [IRC.renderConsole r detailDiv]
                          , TP.h1 #+ [TP.string "Summary"]
                          , return summaryDiv #+ [renderSummaryTable st0]
                          , TP.h1 #+ [TP.string "Proof", return proofSnapshotButton]
                          , return proofDiv
                          , TP.h1 #+ [TP.string "Details"]
                          , return detailDiv
                          ]

  -- Set up a way for the UI to call back to Haskell for more details
  --
  -- See Note [Proof Graph Interaction] for details
  jsOnProofNodeClicked <- TP.ffiExport (onProofNodeClicked r wd detailDiv)

  void $ liftIO $ TP.register (stateChangeEvent r) (updateConsole r wd consoleDiv summaryDiv detailDiv)
  void $ liftIO $ TP.register (proofChangeEvent r) (updateProofDisplay r wd proofDiv jsOnProofNodeClicked)
  return ()

updateProofDisplay
  :: StateRef arch
  -> TP.Window
  -> TP.Element
  -> FJ.JSObject
  -> ()
  -> IO ()
updateProofDisplay r wd proofDiv clickCallback () = do
  state <- IOR.readIORef (stateRef r)
  case state ^. activeProofTree of
    Nothing -> return ()
    Just proof -> do
      TP.runUI wd $ do
        let (genProofGraphContent, initAction) = IRP.renderProof clickCallback "proof-canvas" proof
        proofGraphContent <- genProofGraphContent
        void $ TP.set TP.children [proofGraphContent] (return proofDiv)
        initAction
        TP.flushCallBuffer
        return ()

updateConsole :: (PA.ArchConstraints arch)
              => StateRef arch
              -> TP.Window
              -> TP.Element
              -> TP.Element
              -> TP.Element
              -> ()
              -> IO ()
updateConsole r wd consoleDiv summaryDiv detailDiv () = do
  state <- IOR.readIORef (stateRef r)
  TP.runUI wd $ do
    consoleContent <- IRC.renderConsole r detailDiv
    summary <- renderSummaryTable state
    void $ TP.set TP.children [summary] (return summaryDiv)
    void $ TP.set TP.children [consoleContent] (return consoleDiv)
    return ()

renderSummaryTable :: forall arch
                    . State arch
                   -> TP.UI TP.Element
renderSummaryTable st =
  TP.grid [ [ TP.bold #+ [TP.string "# Equivalent"], mapSizeElement successful]
          , [ TP.bold #+ [TP.string "# Inconclusive"], mapSizeElement indeterminate]
          , [ TP.bold #+ [TP.string "# Inequivalent"], mapSizeElement failure]
          ]
  where
    mapSizeElement :: forall k v . L.Getter (State arch) (Map.Map k v) -> TP.UI TP.Element
    mapSizeElement l = TP.string (show (Map.size (st ^. l)))

{- Note [Monitoring Proof Construction and Evaluation]

We want to be able to monitor the construction of the proof object in the
verifier and watch as it is verified.  The verifier currently emits two events
of interest:

#+BEGIN_SRC haskell
  ProofIntermediate :: BlocksPair arch -> PFI.SomeProofSym arch tp -> TM.NominalDiffTime -> Event arch
  ProvenGoal :: BlocksPair arch ->  PFI.SomeProofSym arch PF.ProofBlockSliceType -> TM.NominalDiffTime -> Event arch
#+END_SRC

The first is emitted when an internal proof node is verified.  The second is emitted after the entire proof has completed.

Those events contain two main things:
- A ~BlocksPair~ is a ~PatchPair~ containing the original and patched ~ConcreteBlock~s.
- A handle to the proof frame: ~SomeProofSym~

#+BEGIN_SRC haskell
data SomeProofSym (arch :: DK.Type) tp where
  SomeProofSym :: PA.ValidArch arch
               => PT.Sym sym
               -> ProofSymNonceExpr sym arch tp
               -> SomeProofSym arch tp
#+END_SRC

Chasing this structure, the important part is the ~ProofSymNonceExpr~:

#+BEGIN_SRC haskell
type ProofSymNonceExpr sym arch = PF.ProofNonceExpr (ProofSym sym arch)
#+END_SRC

which is a:

#+BEGIN_SRC haskell
data ProofNonceExpr prf tp where
  ProofNonceExpr ::
    { prfNonce :: ProofNonce prf tp
    , prfParent :: Some (ProofNonce prf)
    , prfNonceBody :: ProofApp prf (ProofNonceExpr prf) tp
    } -> ProofNonceExpr prf tp
#+END_SRC haskell

This exposes the necessary structure for visualizing the structure of the proof:
- We have block addresses from the block pairs
- We have nonces attached to each node pointing to parents


-}

{- Note [Proof Graph Interaction]

We want to be able to show more detail when requested for individual nodes, but
we would like to avoid sending all of that to the client eagerly because it
would just be way too much and slow everything to a crawl.  Instead, we will:

1. Build an FFI callback (via ~ffiExport~ from threepenny-ui) that accepts a node ID
2. We can pass that callback (as a ~JSObject~) to the graph initialization function
3. The raw event handler in JS will invoke that callback when nodes are clicked (passing the node ID)
4. That will call back into Haskell, which will then render the details of that node

Note that node IDs are ints in the JS side, but nonces on the Haskell
side. We'll need to maintain a mapping there

-}
