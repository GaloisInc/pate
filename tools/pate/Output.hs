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
  , tagOutput
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

data Output_ =
    OutputElemList [OutputElem]
  | OutputInfo (PP.Doc ())
  | OutputErr (PP.Doc ())
  | OutputBreak
  | OutputPrompt String
  | OutputHeartbeat
  -- ^ linebreak

data Output = Output
  { outputC :: Output_
  , output_this :: Maybe (PP.Doc ())
  , output_tag :: Maybe (Text.Text)
  }

output :: Output_ -> Output
output o = Output o Nothing Nothing

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
outputList es = output $ OutputElemList es

outputMsg :: PP.Doc () -> Output
outputMsg msg = output $ OutputInfo msg

printMsg :: HasOutput m => PP.Doc () -> m ()
printMsg msg = printOutput (outputMsg msg)

printMsgLn :: HasOutput m => PP.Doc () -> m ()
printMsgLn msg = printMsg msg >> printBreak

outputErr :: PP.Doc () -> Output
outputErr msg_er = output $ OutputErr msg_er

printErr :: HasOutput m => PP.Doc () -> m ()
printErr msg = printOutput (outputErr msg)

printErrLn :: HasOutput m => PP.Doc () -> m ()
printErrLn msg = printErr msg >> printBreak

outputBreak :: Output
outputBreak = output OutputBreak

printBreak :: HasOutput m => m ()
printBreak = printOutput outputBreak

printPrompt :: HasOutput m => String -> m ()
printPrompt msg = printOutput $ output (OutputPrompt msg)

printHeartbeat :: HasOutput m => m ()
printHeartbeat = printOutput $ output OutputHeartbeat

ppOutputElem :: OutputElem -> PP.Doc ()
ppOutputElem nd = 
  let p = case outSuffix nd of
        Just s -> outPP nd <+> s
        Nothing -> outPP nd
      p' = case outMoreResults nd of
        True -> p <+> "more results..."
        False -> p
  in PP.pretty (outIdx nd) <> ":" <+> (PP.indent (outIndent nd) p')

tagOutput :: Maybe (PP.Doc ()) -> Maybe (Text.Text) -> Output -> Output
tagOutput msg tag o = Output (outputC o) msg tag

ppOutput_ :: Output_ -> [PP.Doc ()]
ppOutput_ (OutputElemList es) = map ppOutputElem es
ppOutput_ (OutputInfo msg) = [msg]
ppOutput_ (OutputErr msg) = [msg]
ppOutput_ OutputBreak = ["\n"]
ppOutput_ (OutputPrompt str) = [PP.pretty str]
ppOutput_ OutputHeartbeat = ["."]

ppOutput :: Output -> PP.Doc ()
ppOutput (Output out_ Nothing _) = PP.vsep $ ppOutput_ out_
ppOutput (Output out_ (Just this_) _) = PP.vsep $ this_:(ppOutput_ out_)

{-
mkJSON' :: [OutputElem] -> ([JSON.Value], [OutputElem])
mkJSON' (e1 : e2 : es) = case compare (outIndent e1) (outIndent e2) of
  -- increasing indent
  LT ->
    let
      (v2, es') = mkJSON' (e2 : es)
      sub_v2 = JSON.object
        [ "subnode_header" JSON..= outJSON e1, "subnode" JSON..= JSON.toJSON v2]
      (vs, es'') = mkJSON' es'
    in (sub_v2:vs, es'')
  -- decreasing indent
  GT -> ([outJSON e1], e2 : es)
  EQ ->
    let
      v1 = outJSON e1
      (vs, es') = mkJSON' (e2 : es)
    in (v1 : vs, es')
mkJSON' [e] = ([outJSON e], [])
mkJSON' [] = ([],[])

mkJSON :: [OutputElem] -> JSON.Value
mkJSON es = case mkJSON' es of
  (vs, []) -> JSON.toJSON vs
  (_, _es') -> error "Unexpected leftover elemenbts"
-}

jsonOutput :: Output -> JSON.Value
jsonOutput (Output out_ this_ tag_) =
  case out_ of
    OutputElemList es | Just this__ <- this_ ->
      JSON.object
        [ "this" JSON..= show this__
        , "trace_node_kind" JSON..= tag_
        , "trace_node_contents" JSON..= map outJSON es
        ]
    OutputElemList es -> JSON.toJSON $ map outJSON es
    OutputInfo msg -> JSON.object ["message" JSON..= show msg]
    OutputErr msg -> JSON.object ["error" JSON..= show msg]
    OutputBreak -> JSON.Null
    OutputPrompt{} -> JSON.Null
    OutputHeartbeat{} -> JSON.Null

printOutput :: HasOutput m => Output -> m ()
printOutput o = do
  mhdl <- case outputC o of
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
  printBreak