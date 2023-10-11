{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}

module Output
  ( Output
  , OutputElem(..)
  , printOutput
  , outputList
  , outputMsg
  , outputErr
  , printMsg
  , printErr
  , printMsgLn
  , printErrLn
  , printPrompt
  , outputBreak
  , printBreak
  , printOutputLn
  , setJSONMode
  , hasStdOut
  , printHeartbeat
  )
 where

import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified System.IO as IO
import qualified Control.Monad.IO.Class as IO

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter.Render.Text as PPText
import qualified Data.Aeson as JSON
import qualified Data.IORef as IO
import qualified GHC.IO as IO hiding (liftIO)
import qualified Data.ByteString.Lazy as BS
import Data.Maybe


data OutputElem = 
  OutputElem 
    { outIdx :: Int
    , outIndent :: Int
    , outFinished :: Bool
    , outPP :: PP.Doc ()
    , outJSON :: JSON.Value
    , outSuffix :: Maybe (PP.Doc ())
    , outMoreResults :: Bool
    -- ^ more results at this nesting level that were omitted
    }

data Output = 
    OutputElemList [OutputElem]
  | OutputInfo (PP.Doc ())
  | OutputErr (PP.Doc ())
  | OutputBreak
  | OutputPrompt String
  | OutputHeartbeat
  -- ^ linebreak

jsonOutputHandle :: IO.IORef (Maybe IO.Handle)
jsonOutputHandle = IO.unsafePerformIO (IO.newIORef Nothing)

stdOutputHandle :: IO.IORef (Maybe IO.Handle)
stdOutputHandle = IO.unsafePerformIO (IO.newIORef (Just IO.stdout))

errOutputHandle :: IO.IORef (Maybe IO.Handle)
errOutputHandle = IO.unsafePerformIO (IO.newIORef (Just IO.stderr))

hasStdOut :: IO Bool
hasStdOut = isJust <$> IO.readIORef stdOutputHandle

setJSONMode :: Bool -> IO ()
setJSONMode True = do
  IO.writeIORef stdOutputHandle Nothing
  IO.writeIORef errOutputHandle Nothing
  IO.writeIORef jsonOutputHandle (Just IO.stdout)
setJSONMode False = do
  IO.writeIORef stdOutputHandle (Just IO.stdout)
  IO.writeIORef errOutputHandle (Just IO.stderr)
  IO.writeIORef jsonOutputHandle Nothing

writeOut :: HasOutput m => PP.Doc a -> IO.Handle -> m ()
writeOut p hdl = do
  let s = PP.layoutSmart (PP.defaultLayoutOptions { PP.layoutPageWidth = PP.Unbounded }) p
  IO.liftIO $ Text.hPutStr hdl (PPText.renderStrict s)

type HasOutput m = IO.MonadIO m

outputList :: [OutputElem] -> Output
outputList es = OutputElemList es

outputMsg :: PP.Doc () -> Output
outputMsg msg = OutputInfo msg

printMsg :: HasOutput m => PP.Doc () -> m ()
printMsg msg = printOutput (outputMsg msg)

printMsgLn :: HasOutput m => PP.Doc () -> m ()
printMsgLn msg = printMsg msg >> printBreak

outputErr :: PP.Doc () -> Output
outputErr msg_er = OutputErr msg_er

printErr :: HasOutput m => PP.Doc () -> m ()
printErr msg = printOutput (outputErr msg)

printErrLn :: HasOutput m => PP.Doc () -> m ()
printErrLn msg = printErr msg >> printBreak

outputBreak :: Output
outputBreak = OutputBreak

printBreak :: HasOutput m => m ()
printBreak = printOutput outputBreak

printPrompt :: HasOutput m => String -> m ()
printPrompt msg = printOutput (OutputPrompt msg)

printHeartbeat :: HasOutput m => m ()
printHeartbeat = printOutput OutputHeartbeat

ppOutputElem :: OutputElem -> PP.Doc ()
ppOutputElem nd = 
  let p = case outSuffix nd of
        Just s -> outPP nd <+> s
        Nothing -> outPP nd
      p' = case outMoreResults nd of
        True -> p <+> "more results..."
        False -> p
  in PP.pretty (outIdx nd) <> ":" <+> (PP.indent (outIndent nd) p')

ppOutput :: Output -> PP.Doc ()
ppOutput (OutputElemList es) = PP.vsep (map ppOutputElem es)
ppOutput (OutputInfo msg) = msg
ppOutput (OutputErr msg) = msg
ppOutput OutputBreak = "\n"
ppOutput (OutputPrompt str) = PP.pretty str
ppOutput OutputHeartbeat = "."

jsonOutput :: Output -> JSON.Value
jsonOutput (OutputElemList es) = JSON.toJSON (map outJSON es)
jsonOutput (OutputInfo msg) = JSON.object ["message" JSON..= show msg]
jsonOutput (OutputErr msg) = JSON.object ["error" JSON..= show msg]
jsonOutput OutputBreak = JSON.Null
jsonOutput OutputPrompt{} = JSON.Null
jsonOutput OutputHeartbeat = JSON.Null

printOutput :: HasOutput m => Output -> m ()
printOutput o = do
  mhdl <- case o of
    OutputErr{} -> IO.liftIO $ IO.readIORef errOutputHandle
    _ -> IO.liftIO $ IO.readIORef stdOutputHandle
  case mhdl of
    Just hdl -> writeOut (ppOutput o) hdl
    _ -> return ()
  case jsonOutput o of
    JSON.Null -> return ()
    x -> (IO.liftIO $ IO.readIORef jsonOutputHandle) >>= \case
      Just jsonout -> IO.liftIO $ BS.hPut jsonout (JSON.encode x) >> IO.putStrLn ""
      Nothing -> return ()


printOutputLn :: IO.MonadIO m => Output -> m ()
printOutputLn o = do
  printOutput o
  printOutput OutputBreak