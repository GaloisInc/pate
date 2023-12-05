{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Pate.Timeout (
  Timeout(..),
  Microseconds,
  timeoutAsMicros,
  timeout,
  timeout'
  ) where

import qualified System.Timeout as ST

data Timeout where
  -- | No timeout is specified
  None :: Timeout
  -- | Specify a timeout in the given number of microseconds
  Microseconds :: Int -> Timeout
  -- | Specify a timeout in the given number of seconds
  Seconds :: Int -> Timeout
  -- | Specify a timeout in the given number of minutes
  Minutes :: Int -> Timeout

deriving instance Eq Timeout
deriving instance Ord Timeout
deriving instance Show Timeout
deriving instance Read Timeout

newtype Microseconds = MicrosecondsC Int
  deriving (Show, Read, Eq, Ord)

-- | Convert a timeout to a number of microseconds (unless it was 'None')
timeoutAsMicros :: Timeout -> Maybe Microseconds
timeoutAsMicros to =
  case to of
    None -> Nothing
    Microseconds ms -> Just (MicrosecondsC ms)
    Seconds s -> Just (MicrosecondsC (s * 1000000))
    Minutes m -> Just (MicrosecondsC (m * 60 * 1000000))

timeout :: Microseconds -> IO a -> IO (Maybe a)
timeout (MicrosecondsC us) act = ST.timeout us act

timeout' :: Timeout -> IO a -> IO (Maybe a)
timeout' to act = case timeoutAsMicros to of
  Just micros -> timeout micros act
  Nothing -> Just <$> act
