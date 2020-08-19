module Pate.Utils
  ( orElse
  , showSignedHex
  , showSignedHexWithPlus
  , (<>|)
  ) where

import Data.List.NonEmpty ( NonEmpty((:|)) )
import Data.Maybe ( fromMaybe )
import Text.Printf ( PrintfArg, printf )

infixr 1 `orElse`
orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

showSignedHex :: ( Num a, Ord a, PrintfArg a ) => a -> String
showSignedHex i = printf "%s0x%x" (if i >= 0 then "" else "-") (abs i)

showSignedHexWithPlus :: ( Num a, Ord a, PrintfArg a ) => a -> String
showSignedHexWithPlus i = printf "%s0x%x" (if i >= 0 then "+" else "-") (abs i)

infixr 6 <>|
(<>|) :: [a] -> NonEmpty a -> NonEmpty a
[] <>| as' = as'
(a:as) <>| (a':|as') = a :| (as <> (a':as'))
