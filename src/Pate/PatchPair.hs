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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Pate.PatchPair (
    PatchPair
  , traverse
  , map
  , pattern PatchPair
  , pattern PatchPairSingle
  , pattern PatchPairOriginal
  , pattern PatchPairPatched
  , PatchPairM(..)
  , PatchPairT
  , PatchPairC
  , pattern PatchPairC
  , lensC
  , runPatchPairT
  , runPatchPairT'
  , handleSingletonStub
  , patchPairRepr
  , mkPair
  , mkSingle
  , ppPatchPairCEq
  , ppPatchPairEq
  , ppPatchPairC
  , ppPatchPair
  , ppPatchPair'
  , forBins
  , update
  , insertWith
  , forBinsC
  , catBins
  , get
  , set
  , view
  , lens
  , asTuple
  , fromTuple
  , fromMaybes
  , ppEq
  , LiftF(..)
  , PatchPairF
  , pattern PatchPairF
  , lensF
  , PatchPairMaybeCases(..)
  , toMaybeCases
  , forBins2
  , forBinsF
  , oneBin
  , some
  , someC
  , getC
  , getF
  , catBinsPure
  , defaultPair
  , joinPatchPred
  , collapse
  , asSingleton
  , toSingleton
  , zip
  , WithBin(..)
  , matchShape
  ) where

import           Prelude hiding (zip, map, traverse)
import           GHC.Stack (HasCallStack)
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Except
import           Control.Monad.Catch
import qualified Control.Monad.Trans as CMT
import           Control.Monad.IO.Class (MonadIO)

import           Data.Functor.Const ( Const(..) )
import qualified Data.Kind as DK
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Quant as Qu

import qualified Prettyprinter as PP
import qualified Data.Aeson as JSON
import qualified Compat.Aeson as JSON

import qualified Pate.Binary as PB
import qualified Pate.ExprMappable as PEM
import Data.Parameterized (Some(..), Pair(..))
import Control.Monad.Identity
import Pate.TraceTree
import qualified What4.JSON as W4S
import What4.JSON
import Control.Monad.State.Strict (StateT (..), put)
import qualified Control.Monad.State.Strict as CMS
import           Control.Applicative ( (<|>) )
import qualified Control.Lens as L

-- | A pair of values indexed based on which binary they are associated with (either the
--   original binary or the patched binary).
--   A 'PatchPair' may also be a singleton (i.e. only containing a value for either the original
--   or patched binary). During most of the verification process, all 'PatchPair' values are
--   "full" (i.e. containing values for both binaries). Singleton 'PatchPair' values are used
--   to handle cases where the control flow between the binaries has diverged and the verifier
--   needs to handle each one independently.
type PatchPair (tp :: PB.WhichBinary -> DK.Type) = Qu.Quant tp Qu.ExistsK 

map :: (forall (bin :: PB.WhichBinary). f bin -> g bin) -> PatchPair f -> PatchPair g
map = TFC.fmapFC

traverse :: Applicative m => (forall (bin :: PB.WhichBinary). f bin -> m (g bin)) -> PatchPair f -> m (PatchPair g)
traverse = TFC.traverseFC

pattern PatchPair :: (tp PB.Original) -> (tp PB.Patched) -> PatchPair tp
pattern PatchPair a b <- ((\l -> case l of Qu.All f -> Just (f PB.OriginalRepr, f PB.PatchedRepr); _ -> Nothing) -> Just (a, b))
  where
     PatchPair a b = Qu.QuantSome $ Qu.generateAll $ \case
      PB.OriginalRepr -> a
      PB.PatchedRepr -> b

pattern PatchPairSingle :: () => forall x. PB.WhichBinaryRepr x -> tp x -> PatchPair tp
pattern PatchPairSingle repr x <- (Qu.Single repr x)
  where
      PatchPairSingle repr x = Qu.QuantSome $ Qu.QuantOne repr x

pattern PatchPairOriginal :: tp PB.Original -> PatchPair tp
pattern PatchPairOriginal a = PatchPairSingle PB.OriginalRepr a

pattern PatchPairPatched :: tp PB.Patched -> PatchPair tp
pattern PatchPairPatched a = PatchPairSingle PB.PatchedRepr a

lens ::
  PB.WhichBinaryRepr bin ->
  k bin {- ^ default value -} ->
  L.Lens' (PatchPair k) (k bin)
lens bin default_ f ppair = case (bin, ppair) of
  (PB.OriginalRepr, PatchPair a b) -> fmap (\k -> PatchPair k b) (f a)
  (PB.PatchedRepr, PatchPair a b) -> fmap (\k -> PatchPair a k) (f b)
  (PB.OriginalRepr, PatchPairOriginal a) -> fmap (\k -> PatchPairOriginal k) (f a)
  (PB.PatchedRepr, PatchPairPatched b) -> fmap (\k -> PatchPairPatched k) (f b)
  (PB.OriginalRepr, PatchPairPatched b) -> fmap (\k -> PatchPair k b) (f default_)
  (PB.PatchedRepr, PatchPairOriginal a) -> fmap (\k -> PatchPair a k) (f default_)



{-# COMPLETE PatchPair, PatchPairSingle #-}
{-# COMPLETE PatchPair, PatchPairOriginal, PatchPairPatched #-}

-- | Tag any type with a 'PB.WhichBinary'
data WithBin f (bin :: PB.WhichBinary) = 
  WithBin { withBinRepr :: PB.WhichBinaryRepr bin, withBinValue :: f }

instance Eq f => TestEquality (WithBin f) where
  testEquality (WithBin bin1 f1) (WithBin bin2 f2)
    | Just Refl <- testEquality bin1 bin2
    , f1 == f2
    = Just Refl
  testEquality _ _ = Nothing

instance Ord f => OrdF (WithBin f) where
  compareF (WithBin bin1 f1) (WithBin bin2 f2) = 
    lexCompareF bin1 bin2 $ fromOrdering (compare f1 f2) 

instance Eq f => Eq (WithBin f bin) where
  (WithBin _ f1) == (WithBin _ f2) = f1 == f2

instance Ord f => Ord (WithBin f bin) where
  compare (WithBin _ f1) (WithBin _ f2) = compare f1 f2

-- NB: not a Monoid because we don't have an empty value for <>
instance (forall bin. Semigroup (f bin)) => Semigroup (PatchPair f) where
  p1 <> p2 = case (p1,p2) of
    (PatchPair a1 b1, PatchPair a2 b2) -> PatchPair (a1 <> a2) (b1 <> b2)
    (PatchPairSingle bin1 v1, PatchPair a2 b2) -> case bin1 of
      PB.OriginalRepr -> PatchPair (v1 <> a2) b2
      PB.PatchedRepr -> PatchPair a2 (v1 <> b2)
    (PatchPair a1 b1, PatchPairSingle bin2 v2) -> case bin2 of
      PB.OriginalRepr -> PatchPair (a1 <> v2) b1
      PB.PatchedRepr -> PatchPair a1 (b1 <> v2)
    (PatchPairSingle bin1 v1, PatchPairSingle bin2 v2) -> case (bin1, bin2) of
      (PB.OriginalRepr, PB.PatchedRepr) -> PatchPair v1 v2
      (PB.OriginalRepr, PB.OriginalRepr) -> PatchPairSingle bin1 (v1 <> v2)
      (PB.PatchedRepr, PB.OriginalRepr) -> PatchPair v2 v1
      (PB.PatchedRepr, PB.PatchedRepr) ->PatchPairSingle bin1 (v1 <> v2)

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

-- {-# DEPRECATED handleSingletonStub "Missing implementation for handling singleton PatchPair values" #-}
handleSingletonStub :: HasCallStack => a
handleSingletonStub = error "Missing implementation for handling singleton PatchPair values"

class Monad m => PatchPairM m where
  -- | Called when an invalid patch pair access occurs (i.e. some 'get' or 'set' operation
  -- was performed on a 'PatchPair' that did not have a value for the given binary)
  throwPairErr :: HasCallStack => m a
  -- | Run the first function, falling through to the second function if
  --   any 'throwPairErr' calls are made.
  catchPairErr :: m a -> m a -> m a

instance PatchPairM m => PatchPairM (NoTreeBuilder k m) where
  throwPairErr = noTracing $ throwPairErr
  catchPairErr (NoTreeBuilder f) (NoTreeBuilder g) = NoTreeBuilder (catchPairErr f g)

instance PatchPairM Maybe where
  throwPairErr = Nothing
  catchPairErr a b = catchError a (\_ -> b)

instance Monad m => PatchPairM (MaybeT m) where
  throwPairErr = fail ""
  catchPairErr (MaybeT a) (MaybeT b) = MaybeT $ a >>= \case
    Just ra -> return $ Just ra
    Nothing -> b

instance PatchPairM m => PatchPairM (StateT s m) where
  throwPairErr = lift $ throwPairErr
  catchPairErr a b = do
    s <- CMS.get
    (x, s') <- lift $ catchPairErr (runStateT a s) (runStateT b s)
    put s'
    return x

liftPairErr :: PatchPairM m => Maybe a -> m a
liftPairErr (Just a) = return a
liftPairErr Nothing = throwPairErr

-- | Select the value from the 'PatchPair' according to the given 'PB.WhichBinaryRepr'
--   Raises 'pairErr' if the given 'PatchPair' does not contain a value for the given binary.
get :: HasCallStack => PatchPairM m => PB.WhichBinaryRepr bin -> (forall tp. PatchPair tp -> m (tp bin))
get repr pPair = liftPairErr (getPair repr pPair)

getC :: HasCallStack => PatchPairM m => PB.WhichBinaryRepr bin -> (forall tp. PatchPairC tp -> m tp)
getC repr pPair = getConst <$> liftPairErr (getPair repr pPair)

getF :: HasCallStack => PatchPairM m => PB.WhichBinaryRepr bin -> (forall tp. PatchPairF t tp -> m (t (tp bin)))
getF repr pPair = unLiftF <$> liftPairErr (getPair repr pPair)


-- | Project out a value from a 'PatchPair'.
--   Returns the same value twice for singletons
view :: (forall bin. tp bin -> x) -> PatchPair tp -> (x, x)
view f pPair = case pPair of
  PatchPair v1 v2 -> (f v1, f v2)
  PatchPairSingle _ v -> (f v, f v)

asTuple :: PatchPairM m => PatchPair tp -> m (tp PB.Original, tp PB.Patched)
asTuple pPair = case pPair of
  PatchPair v1 v2 -> return (v1, v2)
  PatchPairSingle{} -> throwPairErr


fromTuple :: (tp PB.Original, tp PB.Patched) -> PatchPair tp
fromTuple (vO,vP) = PatchPair vO vP

fromMaybes :: PatchPairM m => (Maybe (tp PB.Original), Maybe (tp PB.Patched)) -> m (PatchPair tp)
fromMaybes = \case
  (Just vO,Just vP) -> return $ PatchPair vO vP
  (Just vO, Nothing) -> return $ PatchPairSingle PB.OriginalRepr vO
  (Nothing, Just vP) -> return $ PatchPairSingle PB.PatchedRepr vP
  (Nothing, Nothing) -> throwPairErr


set :: PB.WhichBinaryRepr bin -> tp bin -> PatchPair tp -> PatchPair tp
set repr v pPair = case pPair of
  PatchPair a b -> case repr of
    PB.OriginalRepr -> PatchPair v b
    PB.PatchedRepr -> PatchPair a v
  PatchPairSingle repr' v' -> case PB.binCases repr' repr of
    Left Refl -> PatchPairSingle repr v
    Right Refl -> mkPair repr v v'

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

instance PatchPairM m => PatchPairM (NodeBuilderT k nm m) where
  throwPairErr = lift $ throwPairErr
  catchPairErr f g = do
    nb <- getNodeBuilder
    lift $ catchPairErr (runNodeBuilderT f nb) (runNodeBuilderT g nb)

-- | Run a 'PatchPairT' computation, using the given 'PatchPair' as the basis
--  for the underlying 'getPairRepr'.
--  NOTE: 'PatchPairT' only satisfies 'PatchPairM' if the monad 'm' is a
--  'MonadError' with an error that has a 'PatchPairError' instance
runPatchPairT' :: PatchPairT m a -> m (Maybe a)
runPatchPairT' (PatchPairT m) = runMaybeT m

runPatchPairT :: HasCallStack => MonadFail m => PatchPairT m a -> m a
runPatchPairT m = runPatchPairT' m >>= \case
  Just a -> return a
  Nothing -> fail "PatchPair: inconsistent patch pair access pattern"

patchPairRepr :: PatchPair PB.WhichBinaryRepr
patchPairRepr = PatchPair PB.OriginalRepr PB.PatchedRepr

mkPair :: PB.WhichBinaryRepr bin -> tp bin -> tp (PB.OtherBinary bin) -> PatchPair tp
mkPair bin b1 b2 = case bin of
  PB.OriginalRepr -> PatchPair b1 b2
  PB.PatchedRepr -> PatchPair b2 b1

-- | Zip two PatchPairs together, where at least one is a singleton. Throws
--   with 'throwPairErr' otherwise.
zip :: PatchPairM m => PatchPair tp -> PatchPair tp -> m (PatchPair tp)
zip (PatchPairSingle bin1 v1) pPair = do
  v2 <- get (PB.flipRepr bin1) pPair
  return $ mkPair bin1 v1 v2
zip pPair (PatchPairSingle bin2 v2) = do
  v1 <- get (PB.flipRepr bin2) pPair
  return $ mkPair bin2 v2 v1
zip (PatchPair{}) (PatchPair{}) = throwPairErr

mkSingle :: PB.WhichBinaryRepr bin -> tp bin -> PatchPair tp
mkSingle bin a = PatchPairSingle bin a

-- | Return the single 'tp' and which binary if the input is a singleton 'PatchPair'.
--   'asSingleton (toSingleton bin x) == (bin, x)' when 'x' contains an entry for 'bin'
--   '(y,bin) <- asSingleton x; toSingleton bin y == x' when 'x' is a singleton
asSingleton :: PatchPairM m => Qu.Quant tp qbin -> m (Pair PB.WhichBinaryRepr tp)
asSingleton (Qu.Single bin v) = return (Pair bin v)
asSingleton _ = throwPairErr

-- | Convert a 'PatchPair' into a singleton containing only
--   a value for the given binary 'bin'.
toSingleton ::
  HasCallStack =>
  PatchPairM m =>
  PB.WhichBinaryRepr bin -> 
  PatchPair tp ->
  m (PatchPair tp)
toSingleton bin pPair = PatchPairSingle bin <$> get bin pPair

-- | Produce a 'PatchPair' with the same shape as a given pair by filling missing fields
--   with a given default value, or dropping values, as needed.
matchShape ::
  Monad m =>
  PatchPair tp1 ->
  PatchPair tp2 ->
  (forall bin. PB.WhichBinaryRepr bin -> m (tp2 bin)) ->
  m (PatchPair tp2)
matchShape p1 p2 f = case (p1, p2) of
  (PatchPair{}, PatchPair{}) -> return p2
  (PatchPairSingle bin1 _, PatchPairSingle bin2 x2) -> case PB.binCases bin1 bin2 of
    Left Refl -> return p2
    Right Refl -> do
      x1 <- f bin1
      return $ mkPair bin1 x1 x2
  (PatchPair{}, PatchPairSingle bin2 x2) -> do
    x1 <- f (PB.flipRepr bin2)
    return $ mkPair bin2 x2 x1
  (PatchPairSingle bin1 _, PatchPair x1 x2) -> case bin1 of
    PB.OriginalRepr -> return $ PatchPairSingle PB.OriginalRepr x1
    PB.PatchedRepr -> return $ PatchPairSingle PB.PatchedRepr x2

-- | Create a 'PatchPair' with a shape according to 'getPairRepr'.
--   The provided function execution for both the original and patched binaries
--   (i.e. given 'PB.OriginalRepr' and 'PB.PatchedRepr'), but may fail early
--   if 'get' or 'set' is called on a 'PatchPair' that is missing a value for the corresponding binary.
--   In other words, calling 'get' or 'set' on any singleton 'PatchPair' values in the given
--   function will cause the returned 'PatchPair' to be a singleton for the same binary.
--   In the case of an inconsistent access pattern (i.e. two mismatched singletons are given)
--   then 'throwPairErr' will be called instead of returning a result.
forBins :: HasCallStack => PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (f bin)) -> m (PatchPair f)
forBins f = do
  omResult <- catchPairErr (Just <$> (f PB.OriginalRepr)) (return Nothing)
  pmResult <- catchPairErr (Just <$> (f PB.PatchedRepr)) (return Nothing)
  case (omResult, pmResult) of
    (Just oResult, Just pResult) -> return $ PatchPair oResult pResult
    (Just oResult, Nothing) -> return $ PatchPairOriginal oResult
    (Nothing, Just pResult) -> return $ PatchPairPatched pResult
    (Nothing, Nothing) -> throwPairErr

-- | Update the elements of a given 'PatchPair', leaving elements unmodified
--   if the given function is undefined for the corresponding binary.
--   NOTE: This may promote a singleton 'PatchPair' by providing a value for a previously-undefined entry.
update :: PatchPairM m => PatchPair f -> (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (f bin)) -> m (PatchPair f)
update src f = do
  tgt <- forBins f
  case (src, tgt) of
    (_, PatchPair{}) -> return tgt
    (PatchPairOriginal{}, PatchPairOriginal{}) -> return tgt
    (PatchPairPatched{}, PatchPairPatched{}) -> return tgt
    (PatchPairPatched a, PatchPairOriginal b) -> return $ PatchPair b a
    (PatchPairOriginal a, PatchPairPatched b) -> return $ PatchPair a b
    (PatchPair _ b, PatchPairOriginal a) -> return $ PatchPair a b
    (PatchPair a _, PatchPairPatched b) -> return $ PatchPair a b

-- | Add a value to a 'PatchPair', combining it with an existing entry if
--   present using the given function (i.e. similar to Map.insertWith)
insertWith ::
  PB.WhichBinaryRepr bin -> 
  f bin -> 
  (f bin -> f bin -> f bin) ->
  PatchPair f ->
  PatchPair f
insertWith bin v f = \case
  PatchPair vO vP | PB.OriginalRepr <- bin -> PatchPair (f v vO) vP
  PatchPair vO vP | PB.PatchedRepr <- bin -> PatchPair vO (f v vP)
  PatchPairSingle bin' v' -> case (bin, bin') of
    (PB.OriginalRepr, PB.OriginalRepr) -> PatchPairSingle bin (f v v')
    (PB.PatchedRepr, PB.PatchedRepr) -> PatchPairSingle bin (f v v')
    (PB.PatchedRepr, PB.OriginalRepr) -> PatchPair v' v
    ( PB.OriginalRepr, PB.PatchedRepr) -> PatchPair v v'

-- | Specialization of 'PatchPair' to types which are not indexed on 'PB.WhichBinary'
type PatchPairC tp = PatchPair (Const tp)

pattern PatchPairC :: tp -> tp -> PatchPair (Const tp)
pattern PatchPairC a b = PatchPair (Const a) (Const b)

lensC ::
  PB.WhichBinaryRepr bin ->
  k {- ^ default value -} ->
  L.Lens' (PatchPairC k) k
lensC bin default_ = (lens bin (Const default_) . (\f -> fmap Const . f . getConst))

{-# COMPLETE PatchPairC, PatchPairSingle #-}
{-# COMPLETE PatchPairC, PatchPairOriginal, PatchPairPatched #-}

-- | The same as 'forBins' but specialized to 'PatchPairC' (i.e. when type in the 'PatchPair' is not
--   indexed by 'PB.WhichBinary')
forBinsC :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m f) -> m (PatchPairC f)
forBinsC f = forBins $ \bin -> Const <$> f bin

newtype LiftF (t :: l -> DK.Type) (f :: k -> l) (tp :: k) = LiftF { unLiftF :: (t (f tp)) }

liftFLens :: L.Lens' (LiftF k tp bin) (k (tp bin))
liftFLens f (LiftF v) = fmap LiftF (f v)

instance Show (t (f tp)) => Show (LiftF t f tp) where
  show (LiftF x) = show x 

instance (forall tp. Show (t (f tp))) => ShowF (LiftF t f)

-- | Specialization of 'PatchPair' to lift inner types over the 'bin' parameter.
type PatchPairF t tp = PatchPair (LiftF t tp)

pattern PatchPairF :: t (tp PB.Original) -> t (tp PB.Patched) -> PatchPair (LiftF t tp)
pattern PatchPairF a b = PatchPair (LiftF a) (LiftF b)

{-# COMPLETE PatchPairF, PatchPairSingle #-}
{-# COMPLETE PatchPairF, PatchPairOriginal, PatchPairPatched #-}

lensF ::
  PB.WhichBinaryRepr bin ->
  k (tp bin) {- ^ default value -} ->
  L.Lens' (PatchPairF k tp) (k (tp bin))
lensF bin default_ = (lens bin (LiftF default_) . liftFLens)

forBinsF :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (t (f bin))) -> m (PatchPairF t f)
forBinsF f = forBins $ \bin -> LiftF <$> f bin

data PatchPairMaybeCases tp =
    PatchPairJust (PatchPair tp)
  | PatchPairNothing
  | forall bin. PatchPairMismatch (PB.WhichBinaryRepr bin) (tp bin)

toMaybeCases :: PatchPairF Maybe tp -> PatchPairMaybeCases tp
toMaybeCases = \case
  PatchPairF (Just a) (Just b) -> PatchPairJust (PatchPair a b)
  PatchPairSingle bin (LiftF (Just a)) -> PatchPairJust (PatchPairSingle bin a)
  PatchPairF Nothing Nothing -> PatchPairNothing
  PatchPairSingle _ (LiftF Nothing) -> PatchPairNothing
  PatchPairF (Just a) Nothing -> PatchPairMismatch PB.OriginalRepr a
  PatchPairF Nothing (Just b) -> PatchPairMismatch PB.PatchedRepr b

-- | Run the given function once for each binary, and then concatenate the result.
--   If any singleton 'PatchPair' values are accessed, the return value will be the
--   result of running the function once on the corresponding binary.
--   As in 'forBins', accessing mismatched 'PatchPair' values will result in calling 'throwError'
--   instead of returning a result.
catBins :: PatchPairM m => Semigroup w => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m w) -> m w
catBins f = forBinsC f >>= \case
  PatchPair (Const a) (Const b) -> pure (a <> b)
  PatchPairSingle _ (Const a) -> pure a

-- | Like 'catBins', but a pure function. If the 'PatchPair' combination is inconsistent, the result is
--   the empty 'w' (rather than throwing an error).
catBinsPure :: Monoid w => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> (PatchPairT Identity) w) -> w
catBinsPure f = runIdentity $
  runPatchPairT' (catBins f) >>= \case
    Just w -> return w
    Nothing -> return mempty

collapse :: Semigroup w =>  (forall bin. PB.KnownBinary bin => tp bin -> w) -> PatchPair tp -> w
collapse f (PatchPair a b) = f @PB.Original a <> f @PB.Patched b
collapse f (PatchPairOriginal a) = f @PB.Original a
collapse f (PatchPairPatched a) = f @PB.Patched a

-- | Execute the given function on exactly one binary. Attempts the "Original" binary first,
--   and then uses the "Patched" binary as a fallback.
oneBin :: PatchPairM m =>
  (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m a) ->
  m a
oneBin f = do
  omResult <- catchPairErr (Just <$> (f PB.OriginalRepr)) (return Nothing)
  case omResult of
    Just oResult -> return oResult
    Nothing -> f PB.PatchedRepr

-- | Returns the given default value if the given 'PatchPair' is a singleton,
--   otherwise runs the given function on the value pair.
defaultPair ::
  a ->
  PatchPair tp ->
  (tp PB.Original -> tp PB.Patched -> a) ->
  a
defaultPair _default (PatchPairSingle{}) _ = _default
defaultPair _default (PatchPair po pp) f = f po pp

-- | Run a monadic function for 'Original' and 'Patched' binaries
--   and then combine the result.
--   If one of the function executions fails due to a missing 'PatchPair' field
--   then the result of the other execution is given for both arguments
--   to the combination function.
joinPatchPred :: PatchPairM m =>
  (a -> a -> m b) ->
  (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m a) ->
  m b
joinPatchPred g f = (forBinsC f) >>= \case
  PatchPairC a b -> g a b
  PatchPairSingle _ (Const a) -> g a a

-- | Return some element of the 'PatchPair'. Prefers the "Original" entry
--   if it exists.
some :: PatchPair tp -> (Some tp)
some (PatchPair a _) = Some a
some (PatchPairSingle _ a) = Some a

-- | Return some element of the 'PatchPairC'. Prefers the "Original" entry
--   if it exists.
someC :: PatchPairC tp -> tp
someC (PatchPairC a _) = a
someC (PatchPairSingle _ (Const a)) = a

data PairF a b tp = PairF { _fstF :: (a tp), _sndF :: (b tp) }

unzipPatchPair2 ::
  PatchPair (PairF tp1 tp2) -> (PatchPair tp1, PatchPair tp2)
unzipPatchPair2 (PatchPair (PairF a b) (PairF c d)) = (PatchPair a c, PatchPair b d)
unzipPatchPair2 (PatchPairSingle bin (PairF a b)) = (PatchPairSingle bin a, PatchPairSingle bin b)

forBins2 :: PatchPairM m => (forall bin. PB.KnownBinary bin => PB.WhichBinaryRepr bin -> m (tp1 bin, tp2 bin)) -> m (PatchPair tp1, PatchPair tp2)
forBins2 f = fmap unzipPatchPair2 $ forBins $ \bin -> do
  (a, b) <- f bin
  return $ PairF a b

-- | True if the two given values would be printed identically
ppEq :: PP.Pretty x => PP.Pretty y => x -> y -> Bool
ppEq x y = show (PP.pretty x) == show (PP.pretty y)

ppPatchPair' :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair' f pPair = ppPatchPairEq (\x y -> show (f x) == show (f y)) f pPair

ppPatchPair :: (forall bin. tp bin -> PP.Doc a) -> PatchPair tp -> PP.Doc a
ppPatchPair = PB.ppBinaryPair

ppPatchPairEq ::
  (tp PB.Original -> tp PB.Patched -> Bool) ->
  (forall bin. tp bin -> PP.Doc a) ->
  PatchPair tp ->
  PP.Doc a
ppPatchPairEq test f (PatchPair a1 a2) = case test a1 a2 of
  True -> f a1
  False -> f a1 PP.<+> "(original) vs." PP.<+> f a2 PP.<+> "(patched)"
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
ppPatchPairCEq f (PatchPairOriginal (Const a)) = f a PP.<+> "(original)"
ppPatchPairCEq f (PatchPairPatched (Const a)) = f a PP.<+> "(patched)"