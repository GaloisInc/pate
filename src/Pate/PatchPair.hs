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
  , PatchPairM(..)
  , PatchPairT
  , PatchPairC
  , pattern PatchPairC
  , runPatchPairT
  , runPatchPairT'
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


class Monad m => PatchPairM m where
  -- | Called when an invalid patch pair access occurs (i.e. some 'get' or 'set' operation
  -- was performed on a 'PatchPair' that did not have a value for the given binary)
  throwPairErr :: m a
  -- | Run the first function, falling through to the second function if
  --   any 'throwPairErr' calls are made.
  catchPairErr :: m a -> m a -> m a

instance PatchPairM Maybe where
  throwPairErr = Nothing
  catchPairErr a b = catchError a (\_ -> b)

instance Monad m => PatchPairM (MaybeT m) where
  throwPairErr = fail ""
  catchPairErr (MaybeT a) (MaybeT b) = MaybeT $ a >>= \case
    Just ra -> return $ Just ra
    Nothing -> b

liftPairErr :: PatchPairM m => Maybe a -> m a
liftPairErr (Just a) = return a
liftPairErr Nothing = throwPairErr

-- | Select the value from the 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Raises 'pairErr' if the given 'PatchPair' does not contain a value for the given binary.
get :: PatchPairM m => PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> m (tp bin))
get repr pPair = liftPairErr (getPair repr pPair)

-- | Set the value in the given 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Raises 'pairErr' if the given 'PatchPair' does not contain a value for the given binary.
set :: PatchPairM m => PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> tp bin -> m (PatchPair tp))
set repr pPair a = liftPairErr (setPair repr pPair a)

data InconsistentPatchPairAccess = InconsistentPatchPairAccess
  deriving (Show)

-- | Simple monadic transformer for giving a default 'PatchPairM' implementation
--   to any monad.
newtype PatchPairT m a = PatchPairT (MaybeT m a)
  deriving (Functor, Applicative, Monad, CMT.MonadTrans)

deriving instance Monad m => PatchPairM (PatchPairT m)
deriving instance MonadError e m => MonadError e (PatchPairT m)
deriving instance MonadThrow m => MonadThrow (PatchPairT m)
deriving instance MonadIO m => MonadIO (PatchPairT m)
deriving instance MonadFail m => MonadFail (PatchPairT m)

-- | Run a 'PatchPairT' computation, using the given 'PatchPair' as the basis
--  for the underlying 'getPairRepr'.
--  NOTE: 'PatchPairT' only satisfies 'PatchPairM' if the monad 'm' is a
--  'MonadError' with an error that has a 'PatchPairError' instance
runPatchPairT' :: PatchPairT m a -> m (Maybe a)
runPatchPairT' (PatchPairT m) = runMaybeT m

runPatchPairT :: MonadFail m => PatchPairT m a -> m a
runPatchPairT m = runPatchPairT' m >>= \case
  Just a -> return a
  Nothing -> fail "PatchPair: inconsistent patch pair access pattern"

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
--   The provided function execution for both the original and patched binaries
--   (i.e. given 'PB.OriginalRepr' and 'PB.PatchedRepr'), but may fail early
--   if 'get' or 'set' is called on a 'PatchPair' that is missing a value for the corresponding binary.
--   In other words, calling 'get' or 'set' on any singleton 'PatchPair' values in the given
--   function will cause the returned 'PatchPair' to be a singleton for the same binary.
--   In the case of an inconsistent access pattern (i.e. two mismatched singletons are given)
--   then 'throwPairErr' will be called instead of returning a result.
forBins :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (f bin)) -> m (PatchPair f)
forBins f = do
  omResult <- catchPairErr (Just <$> (f PB.OriginalRepr)) (return Nothing)
  pmResult <- catchPairErr (Just <$> (f PB.PatchedRepr)) (return Nothing)
  case (omResult, pmResult) of
    (Just oResult, Just pResult) -> return $ PatchPair oResult pResult
    (Just oResult, Nothing) -> return $ PatchPairOriginal oResult
    (Nothing, Just pResult) -> return $ PatchPairPatched pResult
    (Nothing, Nothing) -> throwPairErr

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
forBinsC :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m f) -> m (PatchPairC f)
forBinsC f = forBins $ \bin -> Const <$> f bin

newtype LiftF (t :: l -> DK.Type) (f :: k -> l) (tp :: k) = LiftF { unLiftF :: (t (f tp)) }

-- | Specialization of 'PatchPair' to lift inner types over the 'bin' parameter.
type PatchPairF t tp = PatchPair (LiftF t tp)

pattern PatchPairF :: t (tp PB.Original) -> t (tp PB.Patched) -> PatchPair (LiftF t tp)
pattern PatchPairF a b = PatchPairCtor (LiftF a) (LiftF b)

{-# COMPLETE PatchPairF, PatchPairSingle #-}

forBinsF :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (t (f bin))) -> m (PatchPairF t f)
forBinsF f = forBins $ \bin -> LiftF <$> f bin

-- | Run the given function once for each binary, and then concatenate the result.
--   If any singleton 'PatchPair' values are accessed, the return value will be the
--   result of running the function once on the corresponding binary.
--   As in 'forBins', accessing mismatched 'PatchPair' values will result in calling 'throwError'
--   instead of returning a result.
catBins :: PatchPairM m => Semigroup w => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m w) -> m w
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



