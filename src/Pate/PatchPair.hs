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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Pate.PatchPair (
    PatchPair
  , pattern PatchPair
  , pattern PatchPairSingle
  , PatchPairError(..)
  , PatchPairM(..)
  , PatchPairT
  , PatchPairC
  , pattern PatchPairC
  , withPatchPairT
  , pOriginal
  , pPatched
  , pcOriginal
  , pcPatched
  , patchPairRepr
  , mkPair
  , mkSingle
  , ppPatchPairCEq
  , ppPatchPairEq
  , ppPatchPairC
  , ppPatchPair
  , ppPatchPair'
  , forBins
  , forBinsC
  , catBins
  , get
  , set
  , ppEq
  , LiftF(..)
  , PatchPairF
  , pattern PatchPairF
  , forBinsF
  
  ) where

import           Control.Monad.Trans.Maybe
import           Control.Monad.Error
import           Control.Monad.Catch
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Trans as CMT
import qualified Control.Monad.Trans.Except as CME
import           Control.Exception
import           Control.Monad.IO.Class

import           Data.Functor.Const ( Const(..) )
import qualified Data.Kind as DK
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF
import qualified Prettyprinter as PP

import qualified Pate.Binary as PB
import qualified Pate.ExprMappable as PEM

{-# DEPRECATED PatchPairCtor,pOriginal,pPatched,pcOriginal,pcPatched  "Use accessors" #-}
-- | A pair of values indexed based on which binary they are associated with (either the
--   original binary or the patched binary).
--   A 'PatchPair' may also be a singleton (i.e. only containing a value for either the original
--   or patched binary). During most of the verification process, all 'PatchPair' values are
--   "full" (i.e. containing values for both binaries). Singleton 'PatchPair' values are used
--   to handle cases where the control flow between the binaries has diverged and the verifier
--   needs to handle each one independently.
data PatchPair (tp :: PB.WhichBinary -> DK.Type) = PatchPairCtor
  { pOriginal :: tp PB.Original
  , pPatched :: tp PB.Patched
  }
  | forall bin. PB.KnownBinary bin => PatchPairSingle (PB.WhichBinaryRepr bin) (tp bin)

pattern PatchPair :: (tp PB.Original) -> (tp PB.Patched) -> PatchPair tp
pattern PatchPair a b = PatchPairCtor a b

pattern PatchPairOriginal :: tp PB.Original -> PatchPair tp
pattern PatchPairOriginal a = PatchPairSingle PB.OriginalRepr a

pattern PatchPairPatched :: tp PB.Patched -> PatchPair tp
pattern PatchPairPatched a = PatchPairSingle PB.PatchedRepr a

{-# COMPLETE PatchPair, PatchPairSingle #-}
{-# COMPLETE PatchPair, PatchPairOriginal, PatchPairPatched #-}

-- | Select the value from the 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Returns 'Nothing' if the given 'PatchPair' does not contain a value for the given binary
--   (i.e. it is a singleton 'PatchPair' and the opposite binary repr is given)
getPair :: PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> Maybe (tp bin))
getPair repr pPair = case pPair of
  PatchPair orig patched -> case repr of
    PB.OriginalRepr -> Just orig
    PB.PatchedRepr -> Just patched
  PatchPairSingle repr' a | Just Refl <- testEquality repr repr' -> Just a
  _ -> Nothing

-- | Set the value in the given 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Returns 'Nothing' if the given 'PatchPair' does not contain a value for the given binary.
--   (n.b. this will not convert a singleton 'PatchPair' into a full 'PatchPair')
setPair :: PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> tp bin -> Maybe (PatchPair tp))
setPair PB.OriginalRepr pPair a = case pPair of
  PatchPair _ patched -> Just $ PatchPair a patched
  PatchPairOriginal _ -> Just $ PatchPairOriginal a
  PatchPairPatched _ -> Nothing
setPair PB.PatchedRepr pPair a = case pPair of
  PatchPair orig _ -> Just $ PatchPair orig a
  PatchPairPatched _ -> Just $ PatchPairPatched a
  PatchPairOriginal _ -> Nothing


class PatchPairError e where
  patchPairErr :: e

-- | The 'PatchPairM' class defines how a monad should handle mismatched 'PatchPair' values.
--   Specifically there is always a background 'PatchPair PB.WhichBinaryRepr' that controls
--   the shape of all new 'PatchPair' values.
class (PatchPairError e, MonadError e m) => PatchPairM e m | m -> e where
  getPairRepr :: m (PatchPair PB.WhichBinaryRepr)
  -- ^ controls how all 'PatchPair' values are traversed and the shape of all new 'PatchPair'
  --   values (i.e. if this is a singleton "original" 'PatchPair' then all traversals will be
  --   limited to "original" values and all new 'PatchPair' values will be "original" singletons)

instance PatchPairError () where
  patchPairErr = ()

instance PatchPairM () Maybe where
  getPairRepr = return patchPairRepr

instance PatchPairM e m => PatchPairM e (MaybeT m) where
  getPairRepr = CMT.lift getPairRepr

liftPairErr :: PatchPairM e m => Maybe a -> m a
liftPairErr (Just a) = return a
liftPairErr Nothing = throwError patchPairErr

-- | Select the value from the 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Raises 'pairErr' if the given 'PatchPair' does not contain a value for the given binary.
get :: PatchPairM e m => PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> m (tp bin))
get repr pPair = liftPairErr (getPair repr pPair)

-- | Set the value in the given 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Raises 'pairErr' if the given 'PatchPair' does not contain a value for the given binary.
set :: PatchPairM e m => PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> tp bin -> m (PatchPair tp))
set repr pPair a = liftPairErr (setPair repr pPair a)

-- | Simple monadic transformer for giving a default 'PatchPairM' implementation
--   to any monad.
newtype PatchPairT m a = PatchPairT (CMR.ReaderT (PatchPair PB.WhichBinaryRepr) m a)
  deriving (Functor, Applicative, Monad, CMR.MonadReader (PatchPair PB.WhichBinaryRepr), CMR.MonadTrans)

deriving instance MonadError e m => MonadError e (PatchPairT m)
deriving instance MonadThrow m => MonadThrow (PatchPairT m)
deriving instance MonadIO m => MonadIO (PatchPairT m)
deriving instance MonadFail m => MonadFail (PatchPairT m)

instance PatchPairError IOException where
  patchPairErr = userError "PatchPair: unexpected incompatible binaries in PatchPair combination"

instance (PatchPairError e, MonadError e m) => PatchPairM e (PatchPairT m) where
  getPairRepr = CMR.ask

-- | Run a 'PatchPairT' computation, using the given 'PatchPair' as the basis
--  for the underlying 'getPairRepr'.
--  NOTE: 'PatchPairT' only satisfies 'PatchPairM' if the monad 'm' is a
--  'MonadError' with an error that has a 'PatchPairError' instance
withPatchPairT :: PatchPair x -> PatchPairT m a -> m a
withPatchPairT pPair (PatchPairT m) = CMR.runReaderT m (toPatchPairRepr pPair)

patchPairRepr :: PatchPair PB.WhichBinaryRepr
patchPairRepr = PatchPair PB.OriginalRepr PB.PatchedRepr

toPatchPairRepr :: PatchPair x -> PatchPair PB.WhichBinaryRepr
toPatchPairRepr = \case
  PatchPair{} -> patchPairRepr
  PatchPairSingle bin _ -> PatchPairSingle bin bin

mkPair :: PB.WhichBinaryRepr bin -> tp bin -> tp (PB.OtherBinary bin) -> PatchPair tp
mkPair bin b1 b2 = case bin of
  PB.OriginalRepr -> PatchPair b1 b2
  PB.PatchedRepr -> PatchPair b2 b1

mkSingle :: PB.KnownBinary bin => tp bin -> PatchPair tp
mkSingle a = PatchPairSingle knownRepr a

-- | Create a 'PatchPair' with a shape according to 'getPairRepr'.
--   The provided function is run once for each value in the 'PatchPair' (i.e. twice for a full
--   'PatchPair' or once for a singleton).
--    Note: in the case where 'getPairRepr' is a singleton, the default error for 'PatchPairM' will
--    be raised if the getter or setter is applied to a singleton 'PatchPair' for the opposite binary.
forBins :: PatchPairM e m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (f bin)) -> m (PatchPair f)
forBins f = getPairRepr >>= \case
  PatchPair{} -> PatchPair
    <$> (f PB.OriginalRepr)
    <*> (f PB.PatchedRepr)
  PatchPairOriginal{} -> PatchPairOriginal <$> (f PB.OriginalRepr)
  PatchPairPatched{} -> PatchPairPatched <$> (f PB.PatchedRepr)

{-
forBins :: PatchPairM m => (forall bin. PB.KnownBinary bin => PairGetter bin m -> PairSetter bin m -> m (f bin)) -> m (PatchPair f)
forBins f = forBins_ $ \bin -> f (getPair bin) (setPair bin)
-}

-- | Specialization of 'PatchPair' to types which are not indexed on 'PB.WhichBinary'
type PatchPairC tp = PatchPair (Const tp)

pattern PatchPairC :: tp -> tp -> PatchPair (Const tp)
pattern PatchPairC a b = PatchPairCtor (Const a) (Const b)

{-# COMPLETE PatchPairC, PatchPairSingle #-}

pcOriginal :: PatchPairC tp -> tp
pcOriginal = getConst . pOriginal

pcPatched :: PatchPairC tp -> tp
pcPatched = getConst . pPatched

-- | The same as 'forBins' but specialized to 'PatchPairC' (i.e. when type in the 'PatchPair' is not
--   indexed by 'PB.WhichBinary')
forBinsC :: PatchPairM e m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m f) -> m (PatchPairC f)
forBinsC f = forBins $ \bin -> Const <$> f bin

newtype LiftF (t :: l -> DK.Type) (f :: k -> l) (tp :: k) = LiftF { unLiftF :: (t (f tp)) }

-- | Specialization of 'PatchPair' to lift inner types over the 'bin' parameter.
type PatchPairF t tp = PatchPair (LiftF t tp)

pattern PatchPairF :: t (tp PB.Original) -> t (tp PB.Patched) -> PatchPair (LiftF t tp)
pattern PatchPairF a b = PatchPairCtor (LiftF a) (LiftF b)

{-# COMPLETE PatchPairF, PatchPairSingle #-}

forBinsF :: PatchPairM e m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (t (f bin))) -> m (PatchPairF t f)
forBinsF f = forBins $ \bin -> LiftF <$> f bin

-- | Run the given function once for each value in the current 'getPairRepr', and then concatenate the result.
--   For singleton 'PatchPair' values this is just the result of running the function once.
catBins :: PatchPairM e m => Semigroup w => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m w) -> m w
catBins f = forBinsC f >>= \case
  PatchPair (Const a) (Const b) -> pure (a <> b)
  PatchPairSingle _ (Const a) -> pure a

-- | True if the two given values would be printed identically
ppEq :: PP.Pretty x => PP.Pretty y => x -> y -> Bool
ppEq x y = show (PP.pretty x) == show (PP.pretty y)

instance TestEquality tp => Eq (PatchPair tp) where
  PatchPair o1 p1 == PatchPair o2 p2
    | Just Refl <- testEquality o1 o2
    , Just Refl <- testEquality p1 p2
    = True
  PatchPairSingle _ a1 == PatchPairSingle _ a2 | Just Refl <- testEquality a1 a2 = True
  _ == _ = False

instance forall tp. (TestEquality tp, OrdF tp) => Ord (PatchPair tp) where
  compare pp1 pp2 = case (pp1,pp2) of
    (PatchPair o1 p1, PatchPair o2 p2) -> toOrdering $ (lexCompareF o1 o2 (compareF p1 p2))
    (PatchPairSingle _ s1, PatchPairSingle _ s2) -> toOrdering $ compareF s1 s2
    (PatchPairSingle{},PatchPair{}) -> LT
    (PatchPair{},PatchPairSingle{}) -> GT

instance TF.FunctorF PatchPair where
  fmapF = TF.fmapFDefault

instance TF.FoldableF PatchPair where
  foldMapF = TF.foldMapFDefault

instance (forall bin. PEM.ExprMappable sym (f bin)) => PEM.ExprMappable sym (PatchPair f) where
  mapExpr sym f pp = TF.traverseF (PEM.mapExpr sym f) pp

instance TF.TraversableF PatchPair where
  traverseF f pp = case pp of
    (PatchPair o p) -> PatchPair <$> f o <*> f p
    (PatchPairSingle bin s) -> PatchPairSingle bin <$> f s


instance ShowF tp => Show (PatchPair tp) where
  show (PatchPair a1 a2) = showF a1 ++ " vs. " ++ showF a2
  show (PatchPairOriginal a1) = showF a1 ++ " (original)"
  show (PatchPairPatched a1) = showF a1 ++ " (patched)"

instance (forall bin. PP.Pretty (f bin)) => PP.Pretty (PatchPair f) where
  pretty = ppPatchPairEq ppEq PP.pretty

ppPatchPair' :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair' f pPair = ppPatchPairEq (\x y -> show (f x) == show (f y)) f pPair


ppPatchPair :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair f (PatchPair a1 a2) = f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"
ppPatchPair f (PatchPairOriginal a1) = f a1 PP.<+> PP.pretty "(original)"
ppPatchPair f (PatchPairPatched a1) = f a1 PP.<+> PP.pretty "(patched)"

ppPatchPairEq ::
  (tp PB.Original -> tp PB.Patched -> Bool) ->
  (forall bin. tp bin -> PP.Doc a) ->
  PatchPair tp ->
  PP.Doc a
ppPatchPairEq test f (PatchPair a1 a2) = case test a1 a2 of
  True -> f a1
  False -> f a1 PP.<+> PP.pretty "(original) vs." PP.<+> f a2 PP.<+> PP.pretty "(patched)"
ppPatchPairEq _ f pPair = ppPatchPair f pPair



ppPatchPairC ::
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairC f ppair = ppPatchPair (\(Const v) -> f v) ppair

ppPatchPairCEq ::
  Eq tp =>
  (tp -> PP.Doc a) ->
  PatchPairC tp ->
  PP.Doc a
ppPatchPairCEq f ppair@(PatchPair (Const o) (Const p)) = case o == p of
  True -> f o
  False -> ppPatchPairC f ppair
ppPatchPairCEq f (PatchPairOriginal (Const a)) = f a PP.<+> PP.pretty "(original)"
ppPatchPairCEq f (PatchPairPatched (Const a)) = f a PP.<+> PP.pretty "(patched)"



