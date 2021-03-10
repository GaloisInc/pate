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
import qualified Data.Aeson as JSON
import qualified Data.ByteString as BS
import qualified Data.FileEmbed as DFE
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HMS
import qualified Data.IORef as IOR
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import           Data.Proxy ( Proxy(..) )
import qualified Data.String.UTF8 as UTF8
import qualified Data.Text as T
import qualified Data.Vector as DV
import           Graphics.UI.Threepenny ( (#), (#+), (#.) )
import qualified Graphics.UI.Threepenny as TP
import qualified Language.C as LC
import qualified Prettyprinter as PP
import           System.FilePath ( (</>) )
import qualified System.IO.Temp as SIT

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MDS
import qualified Data.Macaw.CFG as MC

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Types as PT
import qualified Pate.CounterExample as PC

import           Interactive.State

-- | Embed the CSS we need into the Haskell to ensure that binaries can be relocatable
cssContent :: BS.ByteString
cssContent = $(DFE.embedFile "tools/pate/static/pate.css")

-- | This is our custom JS with extra functions called via JS FFI
jsContent :: BS.ByteString
jsContent = $(DFE.embedFile "tools/pate/static/pate.js")

-- | This is the full cytoscape library
cytoscape :: BS.ByteString
cytoscape = $(DFE.embedFile "tools/pate/static/cytoscape.umd.js")

-- | This is an extension to cytoscape that enables labels to contain arbitrary
-- HTML (which we need for multi-line labels)
cytoscapeHtml :: BS.ByteString
cytoscapeHtml = $(DFE.embedFile "tools/pate/static/cytoscape-node-html-label.js")

data StateRef arch =
  StateRef { stateRef :: IOR.IORef (State arch)
           , stateChangeEvent :: TP.Event ()
           , stateChangeEmitter :: () -> IO ()
           }

newState :: Maybe (SourcePair LC.CTranslUnit) -> IO (StateRef arch)
newState ms = do
  r <- IOR.newIORef (emptyState ms)
  (evt, emitter) <- TP.newEvent
  return StateRef { stateRef = r
                  , stateChangeEvent = evt
                  , stateChangeEmitter = emitter
                  }

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
        PE.CheckedEquivalence bpair@(PE.BlocksPair (PE.Blocks blk _) _) res duration -> do
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
        -- FIXME: what to do with additional events?
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

  -- Set the port to 5000 to match the Dockerfile
  let uiConf = TP.defaultConfig { TP.jsPort = Just 5000
                                , TP.jsStatic = Just tmpDir
                                }
  TP.startGUI uiConf (uiSetup r)

uiSetup :: (PA.ArchConstraints arch) => StateRef arch -> TP.Window -> TP.UI ()
uiSetup r wd = do
  st0 <- liftIO $ IOR.readIORef (stateRef r)
  void $ return wd # TP.set TP.title "PATE Verifier"
  void $ TP.getHead wd #+ [ TP.link # TP.set (TP.attr "rel") "stylesheet" # TP.set (TP.attr "href") "/static/pate.css"
                          ]
  consoleDiv <- TP.div #. "console-output-pane"
  summaryDiv <- TP.div #. "summary-pane"
  detailDiv <- TP.div #. "detail-pane"
  void $ TP.getBody wd #+ [ TP.mkElement "script" # TP.set (TP.attr "src") "/static/cytoscape.umd.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/cytoscape-node-html-label.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.mkElement "script" # TP.set (TP.attr "src") "/static/pate.js" # TP.set (TP.attr "type") "text/javascript"
                          , TP.h1 #+ [TP.string "Console Output"]
                          , return consoleDiv #+ [renderConsole r detailDiv]
                          , TP.h1 #+ [TP.string "Summary"]
                          , return summaryDiv #+ [renderSummaryTable st0]
                          , TP.h1 #+ [TP.string "Details"]
                          , return detailDiv
                          ]
  void $ liftIO $ TP.register (stateChangeEvent r) (updateConsole r wd consoleDiv summaryDiv detailDiv)
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
    consoleContent <- renderConsole r detailDiv
    summary <- renderSummaryTable state
    void $ TP.set TP.children [summary] (return summaryDiv)
    void $ TP.set TP.children [consoleContent] (return consoleDiv)
    return ()

-- | Render the most recent events
--
-- The most recent event will be on the bottom (as in a normal scrolling
-- terminal), which requires us to reverse the events list
renderConsole :: (PA.ArchConstraints arch)
              => StateRef arch
              -> TP.Element
              -> TP.UI TP.Element
renderConsole r detailDiv = do
  state <- liftIO $ IOR.readIORef (stateRef r)
  TP.ul #+ (map (\evt -> TP.li #+ [renderEvent state detailDiv evt]) (reverse (state ^. recentEvents)))

renderEvent :: (PA.ArchConstraints arch) => State arch -> TP.Element -> PE.Event arch -> TP.UI TP.Element
renderEvent st detailDiv evt =
  case evt of
    PE.LoadedBinaries {} -> TP.string "Loaded original and patched binaries"
    PE.ElfLoaderWarnings pes ->
      TP.ul #+ (map (\w -> TP.li #+ [TP.string (show w)]) pes)
    PE.CheckedEquivalence (PE.BlocksPair ob@(PE.Blocks blkO _) pb@(PE.Blocks blkP _)) res duration -> do
      let
        origAddr = PT.blockMemAddr blkO
        patchedAddr = PT.blockMemAddr blkP
      blockLink <- TP.a # TP.set TP.text (show origAddr)
                        # TP.set TP.href ("#" ++ show origAddr)
      TP.on TP.click blockLink (showBlockPairDetail st detailDiv ob pb res)
      TP.span #+ [ TP.string "Checking original block at "
                 , return blockLink
                 , TP.string " against patched block at "
                 , TP.string (show patchedAddr)
                 , TP.string (" (in " ++ show duration ++ ")")
                 , renderEquivalenceResult res
                 ]
    -- FIXME: handle other events
    _ -> TP.string ""

-- | Show the original block at the given address (as well as its corresponding patched block)
--
-- Note that the totally unconstrained argument is the data payload passed in by
-- the event handler (e.g., click event), which is not used.
showBlockPairDetail :: (PA.ArchConstraints arch)
                    => State arch
                    -> TP.Element
                    -> PE.Blocks arch PT.Original
                    -> PE.Blocks arch PT.Patched
                    -> PE.EquivalenceResult arch
                    -> a
                    -> TP.UI ()
showBlockPairDetail st detailDiv o@(PE.Blocks blkO opbs) p@(PE.Blocks blkP ppbs) res _ = do
  let
    origAddr = PT.blockMemAddr blkO
    patchedAddr = PT.blockMemAddr blkP
    (origGraphDiv, origGraphSetup) = renderSliceGraph "original-slice-graph" o
    (patchedGraphDiv, patchedGraphSetup) = renderSliceGraph "patched-slice-graph" p
  g <- TP.grid [ renderCounterexample res
               , concat [[renderAddr "Original Code" origAddr, renderAddr "Patched Code" patchedAddr], renderFunctionName st origAddr]
               , concat [ [renderCode opbs, renderCode ppbs]
                        , renderSource st originalSource originalBinary origAddr
                        , renderSource st patchedSource patchedBinary patchedAddr
                        ]
               , [origGraphDiv, patchedGraphDiv]
               ]
  void $ return detailDiv # TP.set TP.children [g]

  -- Call the remote functions to set up the graph in the relevant divs
  origGraphSetup
  patchedGraphSetup
  -- Make sure the call to set up the graph is flushed to the client
  TP.flushCallBuffer
  where
    renderAddr label addr = TP.string (label ++ " (" ++ show addr ++ ")")
    renderCode pbs = TP.code #+ [ TP.pre # TP.set TP.text (show (PP.pretty pb)) #. "basic-block"
                                | pb <- pbs
                                ]


-- | Convert a 'MD.ParsedBlock' to the format described in the documentation of
-- 'renderSliceGraph' (adding it to the accumulated map)
blockNode
  :: forall arch ids
   . (PA.ArchConstraints arch)
  => Map.Map (MC.ArchSegmentOff arch) JSON.Value
  -> MD.ParsedBlock arch ids
  -> Map.Map (MC.ArchSegmentOff arch) JSON.Value
blockNode m pb =
  Map.insert (MD.pblockAddr pb) (JSON.Object node) m
  where
    node = HMS.fromList [ (T.pack "data", JSON.Object content)
                        ]
    content = HMS.fromList [ (T.pack "id", JSON.String (addrIdent (Proxy @arch) (MD.pblockAddr pb)))
                           , (T.pack "text", JSON.String (T.pack (show (PP.pretty pb))))
                           ]

blockEdges
  :: forall arch ids v
   . (PA.ArchConstraints arch)
  => Map.Map (MC.ArchSegmentOff arch) v
  -> [[JSON.Value]]
  -> MD.ParsedBlock arch ids
  -> [[JSON.Value]]
blockEdges nodes edges pb =
  [ toEdge (MD.pblockAddr pb) controlFlowSuccessor
  | controlFlowSuccessor <- MDS.parsedTermSucc (MD.pblockTermStmt pb)
  , Map.member controlFlowSuccessor nodes
  ] : edges
  where
    toEdge src dst =
      let srcLabel = addrIdent (Proxy @arch) src
          tgtLabel = addrIdent (Proxy @arch) dst
          edgeLabel = srcLabel <> tgtLabel
          content = HMS.fromList [ (T.pack "id", JSON.String edgeLabel)
                                 , (T.pack "source", JSON.String srcLabel)
                                 , (T.pack "target", JSON.String tgtLabel)
                                 ]
      in JSON.Object (HMS.fromList [(T.pack "data", JSON.Object content)])


addrIdent :: (PA.ArchConstraints arch) => proxy arch -> MC.ArchSegmentOff arch -> T.Text
addrIdent _ = T.pack . show

-- | Render a set of blocks (a slice) as a graph in the UI (using cytoscape)
--
-- This sets up the necessary DOM elements (easy) and translates the block
-- structure into a graph suitable for display in cytoscaope. It uses the FFI
-- mechanism of threepenny-gui to sent the graph data to JS.
--
-- The cytoscape API expects a list of JS objects; it turns out that threepenny
-- can just use the Aeson Value type for that.
--
-- The format of the data should be a JS object with two top-level fields:
--
-- 1. nodes: A list of {data: {id : <ident>, text: <desc>}}
--
-- 2. edges: A list of {data: {id: <edgeLabel>, source: <src>, target: <tgt>}}
--
-- Note that this code uses block addresses (stringified) as identifiers.
renderSliceGraph
  :: (PA.ArchConstraints arch)
  => String
  -> PE.Blocks arch bkind
  -> (TP.UI TP.Element, TP.UI ())
renderSliceGraph divId (PE.Blocks _ parsedBlocks) =
  (TP.div # TP.set TP.id_ divId, TP.runFunction (initializeGraph divId (JSON.Object graph)))
  where
    nodes = F.foldl' blockNode Map.empty parsedBlocks
    edges = F.foldl' (blockEdges nodes) [] parsedBlocks
    graph = HMS.fromList [ (T.pack "nodes", JSON.Array (DV.fromList (Map.elems nodes)))
                         , (T.pack "edges", JSON.Array (DV.fromList (concat edges)))
                         ]


initializeGraph :: String -> JSON.Value -> TP.JSFunction ()
initializeGraph divId graphData = TP.ffi "initializeGraphIn(%1, %2)" divId graphData

renderCounterexample :: PE.EquivalenceResult arch -> [TP.UI TP.Element]
renderCounterexample er =
  case er of
    PE.Equivalent -> []
    PE.Inconclusive -> []
    PE.Inequivalent ir ->
      case ir of
        PT.InequivalentResults _traceDiff _exitDiff regs _retAddrs rsn ->
          [TP.ul #+ [ TP.li #+ [ TP.string ("Reason: " ++ show rsn)
                               , TP.pre #+ [TP.string (PC.ppPreRegs regs)]
                               ]
                   ]
          ]

-- | Note that we always look up the original address because we key the
-- function name off of that... we could do better
renderSource :: (PA.ArchConstraints arch)
             => State arch
             -> (SourcePair LC.CTranslUnit -> LC.CTranslUnit)
             -> L.Getter (State arch) (Maybe (PB.LoadedELF arch, b))
             -> MC.MemAddr (MC.ArchAddrWidth arch)
             -> [TP.UI TP.Element]
renderSource st getSource binL addr = fromMaybe [] $ do
  (lelf, _) <- st ^. binL
  bname <- MBL.symbolFor (PB.loadedBinary lelf) addr
  let sname = UTF8.toString (UTF8.fromRep bname)
  LC.CTranslUnit decls _ <- getSource <$> st ^. sources
  fundef <- F.find (matchingFunctionName sname) decls
  return [ TP.code #+ [ TP.pre # TP.set TP.text (show (LC.pretty fundef)) #. "source-listing" ] ]

-- | Find the declaration matching the given function name
matchingFunctionName :: String -> LC.CExternalDeclaration LC.NodeInfo -> Bool
matchingFunctionName sname def =
  case def of
    LC.CDeclExt {} -> False
    LC.CAsmExt {} -> False
    LC.CFDefExt (LC.CFunDef _declspecs declr _decls _stmts _annot) ->
      case declr of
        LC.CDeclr (Just ident) _ _ _ _ -> LC.identToString ident == sname
        LC.CDeclr Nothing _ _ _ _ -> False

renderFunctionName :: (PA.ArchConstraints arch)
                   => State arch
                   -> MC.MemAddr (MC.ArchAddrWidth arch)
                   -> [TP.UI TP.Element]
renderFunctionName st origAddr = fromMaybe [] $ do
  (lelf, _) <- st ^. originalBinary
  bname <- MBL.symbolFor (PB.loadedBinary lelf) origAddr
  let sname = UTF8.toString (UTF8.fromRep bname)
  return [TP.string ("(Function: " ++ sname ++ ")")]

renderEquivalenceResult :: PE.EquivalenceResult arch -> TP.UI TP.Element
renderEquivalenceResult res =
  case res of
    PE.Equivalent -> TP.span #+ [ TP.string "["
                                , TP.string "✓" #. "sat-equivalent"
                                , TP.string "]"
                                ]
    PE.Inconclusive -> TP.span #+ [ TP.string "["
                                , TP.string "?" #. "sat-indeterminate"
                                , TP.string "]"
                                ]
    PE.Inequivalent _mdl -> TP.span #+ [ TP.string "["
                                       , TP.string "✗" #. "sat-inequivalent"
                                       , TP.string "]"
                                       ]

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
