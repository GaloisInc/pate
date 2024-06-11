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
  , binCases
  , flipRepr
  , short
  , otherInvolutive
  )
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

type family OtherBinary (bin :: WhichBinary) :: WhichBinary where
  OtherBinary Original = Patched
  OtherBinary Patched = Original

otherInvolutive :: WhichBinaryRepr bin -> (OtherBinary (OtherBinary bin) :~: bin)
otherInvolutive bin = case binCases bin (flipRepr bin) of
  Left Refl -> Refl
  Right Refl -> Refl

flipRepr :: WhichBinaryRepr bin -> WhichBinaryRepr (OtherBinary bin)
flipRepr = \case
  OriginalRepr -> PatchedRepr
  PatchedRepr -> OriginalRepr

binCases :: WhichBinaryRepr bin1 -> WhichBinaryRepr bin2 -> Either (bin1 :~: bin2) ('(bin1, bin2) :~: '(OtherBinary bin2, OtherBinary bin1))
binCases bin1 bin2 = case (bin1, bin2) of
  (OriginalRepr, OriginalRepr) -> Left Refl
  (OriginalRepr, PatchedRepr) -> Right Refl
  (PatchedRepr, PatchedRepr) -> Left Refl
  (PatchedRepr, OriginalRepr) -> Right Refl

short :: WhichBinaryRepr bin -> String
short OriginalRepr = "O"
short PatchedRepr = "P"

instance IsTraceNode (k :: l) "binary" where
  type TraceNodeType k "binary" = Some WhichBinaryRepr
  prettyNode () (Some wb) = PP.pretty (show wb)
  nodeTags = mkTags @k @"binary" [Summary, Simplified]

instance TestEquality WhichBinaryRepr where
  testEquality repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> Just Refl
    (PatchedRepr, PatchedRepr) -> Just Refl
    _ -> Nothing

instance Eq (WhichBinaryRepr bin) where
  repr1 == repr2 | Just Refl <- testEquality repr1 repr2 = True
  _ == _ = False

instance OrdF WhichBinaryRepr where
  compareF repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> EQF
    (PatchedRepr, PatchedRepr) -> EQF
    (OriginalRepr, PatchedRepr) -> LTF
    (PatchedRepr, OriginalRepr) -> GTF

instance Ord (WhichBinaryRepr bin) where
  compare repr1 repr2 = toOrdering (compareF repr1 repr2)

instance Show (WhichBinaryRepr bin) where
  show OriginalRepr = "original"
  show PatchedRepr = "patched"

instance PP.Pretty (WhichBinaryRepr bin) where
  pretty = PP.viaShow

instance KnownRepr WhichBinaryRepr Original where
  knownRepr = OriginalRepr

instance KnownRepr WhichBinaryRepr Patched where
  knownRepr = PatchedRepr

type KnownBinary (bin :: WhichBinary) = KnownRepr WhichBinaryRepr bin

instance IsRepr WhichBinaryRepr
