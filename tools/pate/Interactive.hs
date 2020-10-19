{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Interactive (
  consumeEvents,
  startInterface,
  StateRef,
  newState
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Lens as L
import           Control.Lens ( (^.), (%~), (&) )
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.FileEmbed as DFE
import qualified Data.IORef as IOR
import qualified Data.Map.Strict as Map
import qualified Data.String.UTF8 as UTF8
import qualified Graphics.UI.Threepenny as TP
import           Graphics.UI.Threepenny ( (#), (#+), (#.) )
import qualified Text.PrettyPrint.ANSI.Leijen as PPL

import qualified Data.Macaw.CFG as MC

import qualified Pate.Event as PE
import qualified Pate.Types as PT

import           Interactive.State

-- | Embed the CSS we need into the Haskell to ensure that binaries can be relocatable
cssContent :: String
cssContent = UTF8.toString (UTF8.fromRep $(DFE.embedFile "tools/pate/pate.css"))

data StateRef arch =
  StateRef { stateRef :: IOR.IORef (State arch)
           , stateChangeEvent :: TP.Event ()
           , stateChangeEmitter :: () -> IO ()
           }

newState :: IO (StateRef arch)
newState = do
  r <- IOR.newIORef emptyState
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
        PE.CheckedEquivalence origBlock@(PE.Blocks addr _) patchedBlock res duration -> do
          let et = EquivalenceTest origBlock patchedBlock duration
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
      -- Notify the UI that we got a new result
      stateChangeEmitter r0 ()
      consumeEvents chan r0

recentEventCount :: Int
recentEventCount = 20

addRecent :: Int -> a -> [a] -> [a]
addRecent n elt elts = elt : take (n - 1) elts

-- | Start a persistent interface for the user to inspect data coming out of the
-- verifier
startInterface :: (MC.ArchConstraints arch) => StateRef arch -> IO ()
startInterface r = do
  let uiConf = TP.defaultConfig
  TP.startGUI uiConf (uiSetup r)

uiSetup :: (MC.ArchConstraints arch) => StateRef arch -> TP.Window -> TP.UI ()
uiSetup r wd = do
  st0 <- liftIO $ IOR.readIORef (stateRef r)
  void $ return wd # TP.set TP.title "PATE Verifier"
  void $ TP.getHead wd #+ [ TP.mkElement "style" # TP.set TP.text cssContent ]
  consoleDiv <- TP.div #. "console-output-pane"
  summaryDiv <- TP.div #. "summary-pane"
  detailDiv <- TP.div #. "detail-pane"
  void $ TP.getBody wd #+ [ TP.h1 #+ [TP.string "Console Output"]
                          , return consoleDiv #+ [renderConsole r detailDiv]
                          , TP.h1 #+ [TP.string "Summary"]
                          , return summaryDiv #+ [renderSummaryTable st0]
                          , TP.h1 #+ [TP.string "Details"]
                          , return detailDiv
                          ]
  void $ liftIO $ TP.register (stateChangeEvent r) (updateConsole r wd consoleDiv summaryDiv detailDiv)
  return ()

updateConsole :: (MC.ArchConstraints arch)
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
renderConsole :: (MC.ArchConstraints arch)
              => StateRef arch
              -> TP.Element
              -> TP.UI TP.Element
renderConsole r detailDiv = do
  state <- liftIO $ IOR.readIORef (stateRef r)
  TP.ul #+ (map (\evt -> TP.li #+ [renderEvent detailDiv evt]) (reverse (state ^. recentEvents)))

renderEvent :: (MC.ArchConstraints arch) => TP.Element -> PE.Event arch -> TP.UI TP.Element
renderEvent detailDiv evt =
  case evt of
    PE.CheckedEquivalence ob@(PE.Blocks (PT.ConcreteAddress origAddr) _) pb@(PE.Blocks (PT.ConcreteAddress patchedAddr) _) res duration -> do
      blockLink <- TP.a # TP.set TP.text (show origAddr)
                        # TP.set TP.href ("#" ++ show origAddr)
      TP.on TP.click blockLink (showBlockPairDetail detailDiv ob pb)
      TP.span #+ [ TP.string "Checking original block at "
                 , return blockLink
                 , TP.string " against patched block at "
                 , TP.string (show patchedAddr)
                 , TP.string (" (in " ++ show duration ++ ")")
                 , renderEquivalenceResult res
                 ]

-- | Show the original block at the given address (as well as its corresponding patched block)
showBlockPairDetail :: (MC.ArchConstraints arch)
                    => TP.Element
                    -> PE.Blocks arch
                    -> PE.Blocks arch
                    -> a
                    -> TP.UI ()
showBlockPairDetail detailDiv (PE.Blocks (PT.ConcreteAddress origAddr) opbs) (PE.Blocks (PT.ConcreteAddress patchedAddr) ppbs) _ = do
  g <- TP.grid [ [renderAddr "Original Code" origAddr, renderAddr "Patched Code" patchedAddr]
               , [renderCode opbs, renderCode ppbs]
               ]
  void $ return detailDiv # TP.set TP.children [g]
  return ()
  where
    renderAddr label addr = TP.string (label ++ " (" ++ show addr ++ ")")
    renderCode pbs = TP.code #+ [TP.pre # TP.set TP.text (renderBlocks pbs)]
    renderBlocks pbs = show (PPL.vcat (map PPL.pretty pbs))

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
