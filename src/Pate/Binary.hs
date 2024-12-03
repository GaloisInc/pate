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
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Binary
  ( type WhichBinary
  , type BinaryPair
  , KnownBinary
  , Original
  , Patched
  , WhichBinaryRepr(..)
  , OtherBinary
  , binCases
  , flipRepr
  , short
  , otherInvolutive
  , ppBinaryPair
  , ppBinaryPairEq
  , ppBinaryPair'
  , w4SerializePair
  )
where

import           Data.Kind ( Type )
import           Control.Applicative.Alternative ( (<|>) )

import           Data.Parameterized.WithRepr
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.TotalMapF as TMF
import qualified Data.Aeson as JSON

import qualified Data.Quant as Qu
import           Data.Quant ( Quant, QuantK)
import qualified Prettyprinter as PP
import           Pate.TraceTree
import qualified What4.JSON as W4S
import           What4.JSON ( (.:) )
import qualified Pate.ExprMappable as PEM

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

instance TMF.HasTotalMapF WhichBinaryRepr where
  allValues = [Some OriginalRepr, Some PatchedRepr]

instance Qu.HasReprK WhichBinary where
  type ReprOf = WhichBinaryRepr

type BinaryPair f = Qu.Quant (f :: WhichBinary -> Type)

jsonQuant ::
  (forall bin. f bin -> JSON.Value) -> BinaryPair f (qbin :: QuantK WhichBinary) -> JSON.Value
jsonQuant f q = case q of
  Qu.All g -> JSON.object [ "original" JSON..= f (g OriginalRepr), "patched" JSON..= f (g PatchedRepr)]
  Qu.Single bin x -> case bin of
    OriginalRepr -> JSON.object [ "original" JSON..= f x ]
    PatchedRepr ->  JSON.object [ "patched" JSON..= f x ]


instance (forall bin. JSON.ToJSON (f bin)) => JSON.ToJSON (Qu.Quant f (qbin :: QuantK WhichBinary)) where
  toJSON p = jsonQuant (JSON.toJSON) p


w4SerializePair :: BinaryPair f qbin -> (forall bin. f bin -> W4S.W4S sym JSON.Value) -> W4S.W4S sym JSON.Value
w4SerializePair bpair f = case bpair of
    Qu.All g -> do
      o_v <- f (g OriginalRepr)
      p_v <- f (g PatchedRepr)
      return $ JSON.object ["original" JSON..= o_v, "patched" JSON..= p_v]
    Qu.Single bin x -> case bin of
      OriginalRepr -> do
        o_v <- f x
        return $ JSON.object ["original" JSON..= o_v]
      PatchedRepr -> do
        p_v <- f x
        return $ JSON.object ["patched" JSON..= p_v]

instance W4S.W4SerializableF sym f => W4S.W4Serializable sym (Qu.Quant f (qbin :: QuantK WhichBinary)) where
  w4Serialize ppair = w4SerializePair ppair W4S.w4SerializeF


instance forall f sym. (forall bin. KnownRepr WhichBinaryRepr bin => W4S.W4Deserializable sym (f bin)) => W4S.W4Deserializable sym (Quant f Qu.ExistsK) where
  w4Deserialize_ v = do
    JSON.Object o <- return v
    let
      case_pair = do
        (vo :: f Original) <- o .: "original"
        (vp :: f Patched) <- o .: "patched"
        return $ Qu.All $ \case OriginalRepr -> vo; PatchedRepr -> vp
      case_orig = do
        (vo :: f Original) <- o .: "original"
        return $ Qu.Single OriginalRepr vo
      case_patched = do
        (vp :: f Patched) <- o .: "patched"
        return $ Qu.Single PatchedRepr vp
    case_pair <|> case_orig <|> case_patched

ppBinaryPair :: (forall bin. tp bin -> PP.Doc a) -> BinaryPair tp qbin -> PP.Doc a
ppBinaryPair f (Qu.All g) = f (g OriginalRepr) PP.<+> "(original) vs." PP.<+> f (g PatchedRepr) PP.<+> "(patched)"
ppBinaryPair f (Qu.Single OriginalRepr a1) = f a1 PP.<+> "(original)"
ppBinaryPair f (Qu.Single PatchedRepr a1) = f a1 PP.<+> "(patched)"

ppBinaryPair' :: (forall bin. tp bin -> PP.Doc a) -> BinaryPair tp qbin -> PP.Doc a
ppBinaryPair' f pPair = ppBinaryPairEq (\x y -> show (f x) == show (f y)) f pPair

-- | True if the two given values would be printed identically
ppEq :: PP.Pretty x => PP.Pretty y => x -> y -> Bool
ppEq x y = show (PP.pretty x) == show (PP.pretty y)

instance ShowF tp => Show (Quant tp (qbin :: QuantK WhichBinary)) where
  show (Qu.All g) = 
    let
      s1 = showF (g OriginalRepr)
      s2 = showF (g PatchedRepr)
    in if s1 == s2 then s1 else s1 ++ " vs. " ++ s2
  show (Qu.Single OriginalRepr a1) = showF a1 ++ " (original)"
  show (Qu.Single PatchedRepr a1) = showF a1 ++ " (patched)"


ppBinaryPairEq ::
  (tp Original -> tp Patched -> Bool) ->
  (forall bin. tp bin -> PP.Doc a) ->
  BinaryPair tp qbin ->
  PP.Doc a
ppBinaryPairEq test f (Qu.All g) = case test (g OriginalRepr) (g PatchedRepr) of
  True -> f $ g OriginalRepr
  False -> f (g OriginalRepr) PP.<+> "(original) vs." PP.<+> f (g PatchedRepr) PP.<+> "(patched)"
ppBinaryPairEq _ f pPair = ppBinaryPair f pPair

instance (forall bin. PP.Pretty (f bin)) => PP.Pretty (Quant f (qbin :: QuantK WhichBinary)) where
  pretty = ppBinaryPairEq ppEq PP.pretty

instance (Qu.HasReprK k, forall (bin :: k). PEM.ExprMappable sym (f bin)) => PEM.ExprMappable sym (Quant f qbin) where
  mapExpr sym f pp = Qu.traverse (PEM.mapExpr sym f) pp