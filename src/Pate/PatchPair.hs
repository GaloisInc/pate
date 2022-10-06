{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
module Pate.PatchPair (
    PatchPair(..)
  , patchPairRepr
  , PatchPairC(..)
  , toPatchPairC
  , mergePatchPairCs
  , zipMPatchPairC
  , ppPatchPairCEq
  , ppPatchPairEq
  , ppPatchPairC
  , ppPatchPair
  , get
  , forBins
  , forBins'
  , forBinsC
  , catBins
  , getPair'
  , setPair
  , ppEq
  ) where

import           Data.Functor.Const ( Const(..) )
import qualified Data.Kind as DK
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF
import qualified Prettyprinter as PP

import qualified Pate.Binary as PB
import qualified Pate.ExprMappable as PEM

data PatchPair (tp :: PB.WhichBinary -> DK.Type) = PatchPair
  { pOriginal :: tp PB.Original
  , pPatched :: tp PB.Patched
  }

getPair' :: PB.WhichBinaryRepr bin -> PatchPair tp -> tp bin
getPair' PB.OriginalRepr pPair = pOriginal pPair
getPair' PB.PatchedRepr pPair = pPatched pPair


setPair :: PB.WhichBinaryRepr bin -> tp bin -> PatchPair tp -> PatchPair tp
setPair PB.OriginalRepr a pPair = pPair { pOriginal = a }
setPair PB.PatchedRepr a pPair = pPair { pPatched = a }

get :: forall bin tp. PB.KnownBinary bin => PatchPair tp -> tp bin
get = getPair' knownRepr

patchPairRepr :: PatchPair PB.WhichBinaryRepr
patchPairRepr = PatchPair PB.OriginalRepr PB.PatchedRepr

forBins :: Applicative m => (forall bin. PB.KnownBinary bin => (forall tp. PatchPair tp -> tp bin) -> m (f bin)) -> m (PatchPair f)
forBins f = PatchPair <$> f (get @PB.Original) <*> f (get @PB.Patched)

forBins' :: Applicative m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (f bin)) -> m (PatchPair f)
forBins' f = PatchPair <$> f PB.OriginalRepr <*> f PB.PatchedRepr

forBinsC :: Applicative m => (forall bin. PB.KnownBinary bin => (forall tp. PatchPair tp -> tp bin) -> m f) -> m (f, f)
forBinsC f = (,) <$> f (get @PB.Original) <*> f (get @PB.Patched)

catBins :: Applicative m => Semigroup w => (forall bin. PB.KnownBinary bin => (forall tp. PatchPair tp -> tp bin) -> m w) -> m w
catBins f = (<>) <$> f (get @PB.Original) <*> f (get @PB.Patched)

-- | True if the two given values would be printed identically
ppEq :: PP.Pretty x => PP.Pretty y => x -> y -> Bool
ppEq x y = show (PP.pretty x) == show (PP.pretty y)

data PatchPairC tp = PatchPairC
  { pcOriginal :: tp
  , pcPatched :: tp
  }
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (PEM.ExprMappable sym tp) => PEM.ExprMappable sym (PatchPairC tp) where
  mapExpr sym f (PatchPairC a1 a2) = PatchPairC
    <$> PEM.mapExpr sym f a1
    <*> PEM.mapExpr sym f a2

toPatchPairC ::
  PatchPair (Const f) ->
  PatchPairC f
toPatchPairC (PatchPair (Const v1) (Const v2)) = PatchPairC v1 v2

mergePatchPairCs ::
  PatchPairC a ->
  PatchPairC b ->
  PatchPairC (a, b)
mergePatchPairCs (PatchPairC o1 p1) (PatchPairC o2 p2) = PatchPairC (o1, o2) (p1, p2)

zipMPatchPairC ::
  Applicative m =>
  PatchPairC a ->
  PatchPairC b ->
  (a -> b -> m c) ->
  m (PatchPairC c)
zipMPatchPairC (PatchPairC a1 a2) (PatchPairC b1 b2) f = PatchPairC
  <$> f a1 b1
  <*> f a2 b2

instance TestEquality tp => Eq (PatchPair tp) where
  PatchPair o1 p1 == PatchPair o2 p2
    | Just Refl <- testEquality o1 o2
    , Just Refl <- testEquality p1 p2
    = True
  _ == _ = False

instance (TestEquality tp, OrdF tp) => Ord (PatchPair tp) where
  compare (PatchPair o1 p1) (PatchPair o2 p2) = toOrdering $ (lexCompareF o1 o2 (compareF p1 p2))

instance TF.FunctorF PatchPair where
  fmapF = TF.fmapFDefault

instance TF.FoldableF PatchPair where
  foldMapF = TF.foldMapFDefault

instance (forall bin. PEM.ExprMappable sym (f bin)) => PEM.ExprMappable sym (PatchPair f) where
  mapExpr sym f (PatchPair o p) = PatchPair <$> PEM.mapExpr sym f o <*> PEM.mapExpr sym f p

instance TF.TraversableF PatchPair where
  traverseF f (PatchPair o p) = PatchPair <$> f o <*> f p



instance ShowF tp => Show (PatchPair tp) where
  show (PatchPair a1 a2) = showF a1 ++ " vs. " ++ showF a2

instance (forall bin. PP.Pretty (f bin)) => PP.Pretty (PatchPair f) where
  pretty = ppPatchPairEq ppEq PP.pretty




ppPatchPair :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair f (PatchPair a1 a2) = f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"


ppPatchPairEq ::
  (tp PB.Original -> tp PB.Patched -> Bool) ->
  (forall bin. tp bin -> PP.Doc a) ->
  PatchPair tp ->
  PP.Doc a
ppPatchPairEq test f (PatchPair a1 a2) = case test a1 a2 of
  True -> f a1
  False -> f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"

ppPatchPairC ::
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairC f (PatchPairC o p) = ppPatchPair (\(Const v) -> f v) (PatchPair (Const o) (Const p))

ppPatchPairCEq ::
  Eq tp =>
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairCEq f ppair@(PatchPairC o p) = case o == p of
  True -> f o
  False -> ppPatchPairC f ppair



