{-# LANGUAGE ScopedTypeVariables #-}
-- | A type for ports that comes with a guarantee that it is in the valid range
module Pate.Interactive.Port (
  Port,
  port,
  portNumber,
  portMaybe
  ) where

import Control.Monad ( guard )
import Data.Word ( Word16 )
import Text.Read ( readMaybe )

-- | A type for representing port numbers
newtype Port = Port { portNumber :: Word16 }
  deriving (Show, Eq, Ord)

-- | A safe constructor for ports
--
-- This is safe as long as the caller ensures that no overflow occurred while
-- computing the port; this is fine for literals.
port :: Word16 -> Port
port = Port

-- | A safe reader for ports that ensures there is no overflow
portMaybe :: String -> Maybe Port
portMaybe s = do
  asInteger :: Integer
            <- readMaybe s
  asWord :: Word16
         <- readMaybe s
  guard (asInteger == toInteger asWord)
  return (Port asWord)
