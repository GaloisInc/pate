{- Helper functions for loading binaries -}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Binary
  ( type WhichBinary
  , KnownBinary
  , Original
  , Patched
  , WhichBinaryRepr(..)
  , OtherBinary
  , flipRepr
  , short)
where

import           Data.Parameterized.WithRepr
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Prettyprinter as PP
import           Pate.TraceTree

-- | A type-level tag describing whether the data value is from an original binary or a patched binary
data WhichBinary = Original | Patched deriving (Bounded, Enum, Eq, Ord, Read, Show)

type Original = 'Original
type Patched = 'Patched

-- | A run-time representative of which type of binary (original or patched) this is
data WhichBinaryRepr (bin :: WhichBinary) where
  OriginalRepr :: WhichBinaryRepr 'Original
  PatchedRepr :: WhichBinaryRepr 'Patched

type family OtherBinary (bin :: WhichBinary) :: WhichBinary

type instance OtherBinary Original = Patched
type instance OtherBinary Patched = Original

flipRepr :: WhichBinaryRepr bin -> WhichBinaryRepr (OtherBinary bin)
flipRepr = \case
  OriginalRepr -> PatchedRepr
  PatchedRepr -> OriginalRepr

short :: WhichBinaryRepr bin -> String
short OriginalRepr = "O"
short PatchedRepr = "P"

instance IsTraceNode (k :: l) "binary" where
  type TraceNodeType k "binary" = Some WhichBinaryRepr
  prettyNode () (Some wb) = PP.pretty (show wb)

instance TestEquality WhichBinaryRepr where
  testEquality repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> Just Refl
    (PatchedRepr, PatchedRepr) -> Just Refl
    _ -> Nothing

instance OrdF WhichBinaryRepr where
  compareF repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> EQF
    (PatchedRepr, PatchedRepr) -> EQF
    (OriginalRepr, PatchedRepr) -> LTF
    (PatchedRepr, OriginalRepr) -> GTF

instance Show (WhichBinaryRepr bin) where
  show OriginalRepr = "Original"
  show PatchedRepr = "Patched"

instance PP.Pretty (WhichBinaryRepr bin) where
  pretty = PP.viaShow

instance KnownRepr WhichBinaryRepr Original where
  knownRepr = OriginalRepr

instance KnownRepr WhichBinaryRepr Patched where
  knownRepr = PatchedRepr

type KnownBinary (bin :: WhichBinary) = KnownRepr WhichBinaryRepr bin

instance IsRepr WhichBinaryRepr
