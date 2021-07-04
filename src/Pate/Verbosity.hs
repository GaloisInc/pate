module Pate.Verbosity ( Verbosity(..) ) where

data Verbosity = Info
               | Debug
               deriving (Read, Show, Eq, Ord)
