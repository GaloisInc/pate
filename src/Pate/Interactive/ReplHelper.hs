module Pate.Interactive.ReplHelper 
  ( getLastRunCmd
  , setLastRunCmd
  , freshNonce
  , nonceValid
  , thePromptFn
  , loadNonce
  ) where

import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO

lastRunCmd :: IO.IORef (Maybe String)
lastRunCmd = IO.unsafePerformIO (IO.newIORef Nothing)

setLastRunCmd :: String -> IO ()
setLastRunCmd cmd = IO.writeIORef lastRunCmd (Just cmd)

getLastRunCmd :: IO (Maybe String)
getLastRunCmd = IO.readIORef lastRunCmd

loadNonce :: IO.IORef Int
loadNonce = IO.unsafePerformIO (IO.newIORef 0)

freshNonce :: IO Int
freshNonce = IO.atomicModifyIORef' loadNonce (\n -> (n + 1, n + 1))

nonceValid :: Int -> IO Bool
nonceValid i = do
  j <- IO.readIORef loadNonce
  return $ i == j

thePromptFn :: IO.IORef (IO String)
thePromptFn = IO.unsafePerformIO (IO.newIORef (return ""))
