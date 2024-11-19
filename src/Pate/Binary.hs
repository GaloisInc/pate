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
{-# LANGUAGE PatternSynonyms #-}

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
  , type BinaryType
  , BinaryTypeRepr(..)
  , BinaryPair(..)
  , SingleBinary
  , BothBinaries
  , SomeBinary(..)
  , HasWhichBinary
  , getSingle
  , AsSingle(..)
  )
where

import           Data.Kind (Type)
import           Data.Functor.Const

import qualified Control.Lens as L
import           Control.Lens ( (^.) )

import           Data.Parameterized.WithRepr
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Prettyprinter as PP
import           Pate.TraceTree
import qualified Data.Parameterized.TraversableFC as TFC

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


-- | A generalization of 'WhichBinary', where a type can be
--   tagged as belonging to either individual binary or
--   for both.
data BinaryType = SingleBinary WhichBinary | BothBinaries

type SingleBinary bin = 'SingleBinary bin
type BothBinaries = 'BothBinaries

data AsSingle (f :: BinaryType -> k) (wbin :: WhichBinary) where
  AsSingle :: WhichBinaryRepr wbin -> f (SingleBinary wbin) -> AsSingle f wbin

instance Eq (f (SingleBinary bin)) => Eq (AsSingle f bin) where
  AsSingle _ x == AsSingle _ y = x == y

instance (forall bin. Eq (f (SingleBinary bin))) => TestEquality (AsSingle f) where
  testEquality (AsSingle binx x) (AsSingle biny y) = case testEquality binx biny of
    Just Refl | x == y -> Just Refl
    _ -> Nothing

instance (forall bin. Ord (f (SingleBinary bin))) => OrdF (AsSingle f) where
  compareF (AsSingle binx x) (AsSingle biny y) = 
    lexCompareF binx biny $ fromOrdering $ compare x y

instance Ord (f (SingleBinary bin)) => Ord (AsSingle f bin) where
  compare (AsSingle _ x) (AsSingle _ y) = compare x y

data BinaryPair (f :: WhichBinary -> Type) (bin :: BinaryType) where
  BinarySingle :: WhichBinaryRepr bin -> f bin -> BinaryPair f (SingleBinary bin)
  BinaryPair :: f Original -> f Patched -> BinaryPair f BothBinaries

class HasLens x y where
  getLens :: L.Lens' x y

instance forall f bin wbin. HasWhichBinary bin wbin => HasLens (BinaryPair f bin) (f wbin) where
  getLens = \f bpair ->
    hasWhichBinaryCases @bin @wbin @f bpair (\bin x -> fmap (BinarySingle bin) (f x)) $ \bin x y -> case bin of
      OriginalRepr -> fmap (\z -> BinaryPair z y) (f x)
      PatchedRepr -> fmap (\z -> BinaryPair y z) (f x)

instance HasLens (AsSingle f wbin) (f (SingleBinary wbin)) where
  getLens f (AsSingle bin x) = fmap (\z -> AsSingle bin z) (f x)

pairToRepr :: BinaryPair f bin -> BinaryTypeRepr bin
pairToRepr (BinarySingle bin _) = SingleBinaryRepr bin
pairToRepr (BinaryPair{}) = BothBinariesRepr

reprToPair :: BinaryTypeRepr bin -> BinaryPair WhichBinaryRepr bin
reprToPair (SingleBinaryRepr bin) = BinarySingle bin bin
reprToPair BothBinariesRepr = BinaryPair OriginalRepr PatchedRepr

hasWhichBinaryCases ::
  forall bin wbin f a.
  HasWhichBinary bin wbin =>
  BinaryPair f bin ->
  (bin ~ SingleBinary wbin => WhichBinaryRepr wbin -> f wbin -> a) ->
  (bin ~ BothBinaries => WhichBinaryRepr wbin -> f wbin -> f (OtherBinary wbin) -> a) ->
  a
hasWhichBinaryCases bpair f_single f_pair = case (bpair, getWhichBinary @bin @wbin (reprToPair (pairToRepr bpair))) of
  (BinarySingle bin1 x, bin2) | Just Refl <- testEquality bin1 bin2 -> f_single bin1 x
  (BinaryPair x y, bin) -> case bin of
    OriginalRepr -> f_pair OriginalRepr x y
    PatchedRepr -> f_pair PatchedRepr y x
  _ -> error "hasWhichBinaryCases : impossible"

getSingle :: BinaryPair f (SingleBinary wbin) -> f wbin
getSingle (BinarySingle _ x) = x

instance (forall bin. Eq (f bin)) => TestEquality (BinaryPair f) where
  testEquality x y = case (x,y) of
    (BinarySingle binx x', BinarySingle biny y') 
      | Just Refl <- testEquality binx biny, x' == y' -> Just Refl
    (BinaryPair x1 x2, BinaryPair y1 y2) |
      x1 == y1, x2 == y2 -> Just Refl
    _ -> Nothing

instance (forall wbin. Eq (f wbin)) => Eq (BinaryPair f bin) where
  x == y = case (x,y) of
    (BinarySingle _ x', BinarySingle _ y') -> x' == y'
    (BinaryPair x1 x2, BinaryPair y1 y2) -> x1 == y1 && x2 == y2

instance (forall wbin. Ord (f wbin)) => Ord (BinaryPair f bin) where
  compare x y = case (x,y) of
    (BinarySingle _ x', BinarySingle _ y') -> compare x' y'
    (BinaryPair x1 x2, BinaryPair y1 y2) -> compare x1 y1 <> compare x2 y2

instance (forall bin. Ord (f bin)) => OrdF (BinaryPair f) where
  compareF x y = case (x, y) of
    (BinarySingle binx x', BinarySingle biny y') -> 
      lexCompareF binx biny $ fromOrdering $ compare x' y'
    (BinaryPair x1 x2, BinaryPair y1 y2) -> fromOrdering $ compare x1 y1 <> compare x2 y2
    (BinarySingle{}, BinaryPair{}) -> LTF
    (BinaryPair{}, BinarySingle{}) -> GTF

binType :: BinaryPair f bin -> BinaryTypeRepr bin
binType = \case
  BinarySingle bin _ -> SingleBinaryRepr bin
  BinaryPair _ _ -> BothBinariesRepr

class HasWhichBinary (bin :: BinaryType) (wbin :: WhichBinary) where
  getWhichBinary :: BinaryPair f bin -> f wbin

instance HasWhichBinary (SingleBinary wbin) wbin where
  getWhichBinary (BinarySingle _ x) = x

instance HasWhichBinary BothBinaries Original where
  getWhichBinary (BinaryPair x _y) = x

instance HasWhichBinary BothBinaries Patched where
  getWhichBinary (BinaryPair _x y) = y

lens :: 
  forall wbin bin f.
  HasWhichBinary bin wbin =>
  WhichBinaryRepr wbin -> 
  L.Lens' (BinaryPair f bin)  (f wbin)
lens _ = getLens @(BinaryPair f bin) @(f wbin)

withWhichBinary ::
  Applicative m =>
  BinaryTypeRepr bin ->  
  (forall wbin. HasWhichBinary bin wbin => WhichBinaryRepr wbin -> m (h wbin)) ->
  m (BinaryPair h bin)
withWhichBinary brepr f = case brepr of
  SingleBinaryRepr bin -> BinarySingle <$> pure bin <*> f bin
  BothBinariesRepr -> BinaryPair <$> f OriginalRepr <*> f PatchedRepr

_test ::
  Monad m =>
  BinaryPair WhichBinaryRepr bin ->
  m (BinaryPair (Const String) bin)
_test bp = withWhichBinary (binType bp) $ \bin -> do
  case (bp ^. lens bin) of
    OriginalRepr -> return $ Const "original"
    PatchedRepr -> return $ Const "patched"

data SomeBinary (f :: BinaryType -> Type) = forall bin. SomeBinary (BinaryTypeRepr bin) (f bin)

instance (forall bin. Eq (f bin)) => Eq (SomeBinary f) where
  SomeBinary binx x == SomeBinary biny y = case testEquality binx biny of
    Just Refl -> x == y
    Nothing -> False

instance (forall bin. Ord (f bin)) => Ord (SomeBinary f) where
  compare (SomeBinary binx x) (SomeBinary biny y) = case compareF binx biny of
    EQF -> compare x y
    LTF -> LT
    GTF -> GT


instance TFC.FunctorFC BinaryPair where
  fmapFC f = \case
    BinarySingle bin x -> BinarySingle bin (f x)
    BinaryPair x y -> BinaryPair (f x) (f y)

instance TFC.FoldableFC BinaryPair where
  foldrFC f b = \case
    BinarySingle _ x -> f x b
    BinaryPair x y -> f x $ f y b

instance TFC.TraversableFC BinaryPair where
  traverseFC f = \case
    BinarySingle bin x -> BinarySingle bin <$> f x
    BinaryPair x y -> BinaryPair <$> f x <*> f y

data BinaryTypeRepr (bin :: BinaryType) where
  SingleBinaryRepr :: WhichBinaryRepr bin -> BinaryTypeRepr (SingleBinary bin)
  BothBinariesRepr :: BinaryTypeRepr BothBinaries

instance TestEquality BinaryTypeRepr where
  testEquality repr1 repr2 = case (repr1, repr2) of
    (SingleBinaryRepr rep1, SingleBinaryRepr rep2) -> case testEquality rep1 rep2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
    (BothBinariesRepr, BothBinariesRepr) -> Just Refl
    _ -> Nothing

instance Eq (BinaryTypeRepr bin) where
  repr1 == repr2 | Just Refl <- testEquality repr1 repr2 = True
  _ == _ = False

instance OrdF BinaryTypeRepr where
  compareF repr1 repr2 = case (repr1, repr2) of
    (SingleBinaryRepr rep1, SingleBinaryRepr rep2) -> lexCompareF rep1 rep2 $ EQF
    (BothBinariesRepr, BothBinariesRepr) -> EQF
    (SingleBinaryRepr{}, BothBinariesRepr) -> LTF
    (BothBinariesRepr, SingleBinaryRepr{}) -> GTF

instance Ord (BinaryTypeRepr bin) where
  compare repr1 repr2 = toOrdering (compareF repr1 repr2)

instance Show (BinaryTypeRepr bin) where
  show (SingleBinaryRepr OriginalRepr) = "original"
  show (SingleBinaryRepr PatchedRepr) = "patched"
  show BothBinariesRepr = "pair"

instance PP.Pretty (BinaryTypeRepr bin) where
  pretty = PP.viaShow

instance KnownRepr BinaryTypeRepr (SingleBinary Original) where
  knownRepr = SingleBinaryRepr OriginalRepr

instance KnownRepr BinaryTypeRepr (SingleBinary Patched) where
  knownRepr = SingleBinaryRepr PatchedRepr

instance IsRepr BinaryTypeRepr

