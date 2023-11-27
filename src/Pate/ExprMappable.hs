{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-simplifiable-class-constraints #-}

module Pate.ExprMappable (
    ExprMappable(..)
  , ExprFoldable(..)
  , SkipTransformation(..)
  , ToExprMappable(..)
  , SymExprMappable(..)
  , symExprMappable
  , mapPartExpr
  , mapExprPartial
  , PartialF(..)
  , toPartialSeq
  , updateFilterSeq
  , ExprMapFElems(..)

  ) where

import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Trans.State as CMS
import           Control.Monad.Trans.Class ( lift )

import           Data.Functor.Const
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI
import qualified What4.Partial as WP
import qualified What4.Expr.Builder as W4B

import qualified Data.Parameterized.SetF as SetF
import qualified What4.ExprHelpers as WEH
import qualified What4.PredMap as WPM
import qualified Pate.Parallel as Par

import Unsafe.Coerce(unsafeCoerce)
import Lang.Crucible.Simulator.SymSequence
import Data.Maybe (fromMaybe)
import qualified Lang.Crucible.Utils.MuxTree as MT
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.TraversableF as TF
import Data.Text
import Control.Monad (forM)

-- Expression binding

-- | Declares a type as being expression-containing, where the given traversal
--   occurs shallowly (i.e. not applied recursively to sub-expressions) on all embedded expressions.
class ExprMappable sym f where
  mapExpr ::
    WI.IsSymExprBuilder sym =>
    IO.MonadIO m =>
    sym ->
    (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) ->
    f ->
    m f

  default mapExpr ::
    ExprMappable2 sym sym f f =>
    WI.IsSymExprBuilder sym =>
    IO.MonadIO m =>
    sym ->
    (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) ->
    f ->
    m f
  mapExpr sym f a = mapExpr2 sym sym f a

class ExprMappable2 sym sym' f f' where
  mapExpr2 ::
    (WI.IsSymExprBuilder sym,
    WEH.HasIntegerToNat sym',
    IO.MonadIO m) =>
    sym ->
    sym' ->
    (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym' tp)) ->
    f ->
    m f'

class ExprFoldable sym f where
  foldExpr ::
    WI.IsSymExprBuilder sym =>
    IO.MonadIO m =>
    sym ->
    (forall tp. WI.SymExpr sym tp -> b -> m b) ->
    f ->
    b ->
    m b

instance ExprMappable sym f => ExprFoldable sym f where
  foldExpr sym f e b =
    CMS.execStateT (mapExpr sym (\e' -> CMS.get >>= \s -> lift (f e' s) >>= CMS.put >> return e') e) b

instance (ExprMappable sym a, ExprMappable sym b) => ExprMappable sym (a, b) where
  mapExpr sym f (a, b) = (,) <$> mapExpr sym f a <*> mapExpr sym f b

instance (ExprMappable2 sym sym' a a', ExprMappable2 sym sym' b b') => ExprMappable2 sym sym' (a, b) (a', b') where
  mapExpr2 sym sym' f (a, b) = (,) <$> mapExpr2 sym sym' f a <*> mapExpr2 sym sym' f b

instance ExprMappable2 sym sym' (CS.RegValue' sym (CT.BaseToType bt)) (CS.RegValue' sym' (CT.BaseToType bt)) where
  mapExpr2 _ _ f (CS.RV x) = CS.RV <$> f x

instance ExprMappable sym (CS.RegValue' sym (CT.BaseToType bt)) where

instance ExprMappable2 sym sym' (CS.RegValue' sym (CLM.LLVMPointerType w)) (CS.RegValue' sym' (CLM.LLVMPointerType w)) where
  mapExpr2 sym sym' f (CS.RV x) = CS.RV <$> WEH.mapExprPtr2 sym sym' f x

instance ExprMappable sym (CS.RegValue' sym (CLM.LLVMPointerType w)) where

instance ExprMappable sym (CS.RegValue' sym tp) => ExprMappable sym (CS.RegValue' sym (CT.MaybeType tp)) where
  mapExpr sym f (CS.RV pe) = CS.RV <$> case pe of
    WP.PE p e -> do
      p' <- f p
      CS.RV e' <- mapExpr sym f (CS.RV @sym @tp e)
      return $ WP.PE p' e'
    WP.Unassigned -> return WP.Unassigned

instance forall sym sym' tp. ExprMappable2 sym sym' (CS.RegValue' sym tp) (CS.RegValue' sym' tp) => ExprMappable2 sym sym' (CS.RegValue' sym (CT.MaybeType tp)) (CS.RegValue' sym' (CT.MaybeType tp)) where
  mapExpr2 sym sym' f (CS.RV pe) = do
    (e' :: CS.RegValue sym' (CT.MaybeType tp)) <- case pe of
      WP.PE p e -> do
        (p' :: WI.Pred sym') <- f p
        CS.RV e' <- mapExpr2 @_ @_ @_ @(CS.RegValue' sym' tp) sym sym' f (CS.RV @sym @tp e)
        return $ (WP.PE @(WI.Pred sym') @(CS.RegValue sym' tp) p' e')
      WP.Unassigned -> return $ (WP.Err @_ @(WI.Pred sym') @(CS.RegValue sym' tp) ())
    return $ CS.RV e'

instance ExprMappable sym (f (a tp)) => ExprMappable sym (Par.ConstF f a tp) where
  mapExpr sym f (Par.ConstF a) = Par.ConstF <$> mapExpr sym f a

instance ExprMappable2 sym sym' (f (a tp)) (g (b tp)) => ExprMappable2 sym sym' (Par.ConstF f a tp) (Par.ConstF g b tp) where
  mapExpr2 sym sym' f (Par.ConstF a) = Par.ConstF <$> mapExpr2 sym sym' f a

instance ExprMappable sym f => ExprMappable sym ((Const f) tp)  where
  mapExpr sym f (Const e) = Const <$> mapExpr sym f e

instance ExprMappable2 sym sym' f g => ExprMappable2 sym sym' ((Const f) tp) ((Const g) tp') where
  mapExpr2 sym sym' f (Const e) = Const <$> mapExpr2 sym sym' f e

instance (forall tp. ExprMappable sym (f tp)) => ExprMappable sym (Some f) where
  mapExpr sym f (Some v) = Some <$> mapExpr sym f v

instance forall sym sym' f f'. (forall tp. ExprMappable2 sym sym' (f tp) (f' tp)) => ExprMappable2 sym sym' (Some f) (Some f') where
  mapExpr2 sym sym' f (Some (v :: f tp)) = Some <$> mapExpr2 @_ @_ @(f tp) @(f' tp) sym sym' f v

instance ExprMappable2 sym sym' a a' => ExprMappable2 sym sym' (Maybe a) (Maybe a') where
  mapExpr2 sym sym' f ma = case ma of
    Just a -> Just <$> mapExpr2 sym sym' f a
    Nothing -> return Nothing


instance ExprMappable sym a => ExprMappable sym (Maybe a) where
  mapExpr sym f ma = case ma of
    Just a -> Just <$> mapExpr sym f a
    Nothing -> return Nothing

instance ExprMappable sym (Ctx.Assignment f Ctx.EmptyCtx) where
  mapExpr _ _ = return

instance
  (ExprMappable sym (Ctx.Assignment f ctx), ExprMappable sym (f tp)) =>
  ExprMappable sym (Ctx.Assignment f (ctx Ctx.::> tp)) where
  mapExpr sym f (asn Ctx.:> x) = do
    asn' <- mapExpr sym f asn
    x' <- mapExpr sym f x
    return $ asn' Ctx.:> x'

instance ExprMappable2 sym sym' (Ctx.Assignment f Ctx.EmptyCtx) (Ctx.Assignment f' Ctx.EmptyCtx)  where
  mapExpr2 _sym _sym' _f _ = return Ctx.empty

instance
  (ExprMappable2 sym sym' (Ctx.Assignment f ctx) (Ctx.Assignment f' ctx), ExprMappable2 sym sym' (f tp) (f' tp)) =>
  ExprMappable2 sym sym' (Ctx.Assignment f (ctx Ctx.::> tp)) (Ctx.Assignment f' (ctx Ctx.::> tp)) where
  mapExpr2 sym sym' f (asn Ctx.:> x) = do
    asn' <- mapExpr2 sym sym' f asn
    x' <- mapExpr2 sym sym' f x
    return $ asn' Ctx.:> x'

instance ExprMappable (W4B.ExprBuilder t st fs) (W4B.Expr t tp) where
  mapExpr sym f e = applyExprMappable sym f e

-- | This is a bit redundant, but it forces the function to be evaluated
--   according to the 'ToExprMappable' instance for 'ExprMappable', which
--   avoids the potential for conflicting instances for 'W4B.Expr' vs. 'WI.SymExpr'
--   when using 'symExprMappable'.
applyExprMappable ::
  forall sym tp m.
  IO.MonadIO m =>
  WI.IsSymExprBuilder sym =>
  sym ->
  (forall tp'. WI.SymExpr sym tp' -> m (WI.SymExpr sym tp')) ->
  WI.SymExpr sym tp ->
  m (WI.SymExpr sym tp)
applyExprMappable sym f e | SymExprMappable asEM <- symExprMappable sym =
  asEM @tp $ mapExpr sym f e

-- | Wrap a 'WI.SymExpr' as an 'ExprMappable, which can't be defined directly
-- as it is a type family
newtype ToExprMappable sym tp = ToExprMappable { unEM :: WI.SymExpr sym tp }

instance ExprMappable sym (ToExprMappable sym tp) where
  mapExpr _sym f (ToExprMappable e) = ToExprMappable <$> f e

instance ExprMappable sym a => ExprMappable sym [a] where
  mapExpr sym f l = mapM (mapExpr sym f) l

-- | Wrap a type to give a trivial 'ExprMappable' instance (i.e. make 'mapExpr' a no-op).
-- This is useful for carrying extra information out of functions which are otherwise
-- expected to return only ExprMappable values.
newtype SkipTransformation a = SkipTransformation { unSkip :: a }

instance ExprMappable sym (SkipTransformation a) where
  mapExpr _ _ = return

instance (Ord f, ExprMappable sym f) => ExprMappable sym (WPM.PredMap sym f k) where
  mapExpr sym f pm = WPM.alter sym pm (\v p -> (,) <$> mapExpr sym f v <*> f p)

instance (OrdF f, ExprMappable sym (f tp)) => ExprMappable sym (SetF.SetF f tp) where
  mapExpr sym f s = SetF.fromList <$> traverse (mapExpr sym f) (SetF.toList s)

newtype SymExprMappable sym f = SymExprMappable (forall tp a. ((ExprMappable sym (f tp)) => a) -> a)

-- | Deduce ad-hoc 'ExprMappable' instances for 'WI.SymExpr'.
--   This uses an unsafe coercion to implicitly use the 'ExprMappable' instance
--   defined in 'ToExprMappable'.
--   This is necessary because 'WI.SymExpr' is a type family and therefore we cannot
--   declare the obvious instance for it.
--   TODO: This wouldn't be necessary if 'mapExpr' was instead defined to require
--   that 'sym' is an 'ExprBuilder', but we would need to thread that constraint
--   around in more places to be able to support that.
symExprMappable ::
  forall sym.
  sym ->
  SymExprMappable sym (WI.SymExpr sym)
symExprMappable _sym =
  -- here we are coercing 'SymExprMappable sym (ToExprMappable sym)' into
  -- 'SymExprMappable sym (WI.SymExpr sym)'.
  -- This is (mostly) safe because really we are only coercing 'ToExprMappable sym' to
  -- 'WI.SymExpr sym'.
  -- The one caveat is that if 'sym' is concretely known to be an 'ExprBuilder' then
  -- the 'W4B.Expr' instance will be ignored in favor of the 'ToExprBuilder' instance.
  -- We therefore define the 'W4B.Expr' instance to go through this interface instead
  -- of applying the function directly, which ensures that the 'ToExprMappable' instance
  -- is always used regardless of additonal constraints on 'sym'.
  unsafeCoerce r
  where r :: SymExprMappable sym (ToExprMappable sym)
        r = SymExprMappable (\a -> a)


mapPartExpr :: 
  (IO.MonadIO m, WI.IsSymExprBuilder sym) =>
  ExprMappable sym f =>
  sym ->
  (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) ->
  WP.PartExpr (WI.Pred sym) f ->
  m (WP.PartExpr (WI.Pred sym) f)
mapPartExpr sym f = \case
  WP.Unassigned -> pure WP.Unassigned
  WP.PE p v -> WP.PE <$> f p <*> (mapExpr sym f v)

-- | Lifting a functor to partial values (i.e. values with an associated predicate)
data PartialF sym t f = PartialF (t (WP.PartExpr (WI.Pred sym) f))

mapExprPartial ::
  (IO.MonadIO m, WI.IsSymExprBuilder sym) =>
  ExprMappable sym f =>
  sym ->
  (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) ->
  (forall x. (x -> m x) -> t x -> m (t x)) ->
  PartialF sym t f ->
  m (PartialF sym t f)
mapExprPartial sym f trav (PartialF e) = PartialF <$> trav (mapPartExpr sym f) e

{-
instance 
  (ExprMappable sym f, Traversable t) =>
  ExprMappable sym (PartialF sym t f) where
    mapExpr sym f e = mapExprPartial sym f traverse e
-}

instance (ExprMappable sym f) => ExprMappable sym (PartialF sym (SymSequence sym) f) where
  mapExpr sym f e = mapExprPartial sym f (traverseSymSequence sym) e

toPartialSeq :: 
  IO.MonadIO m =>
  WI.IsExprBuilder sym =>
  sym -> 
  SymSequence sym a -> 
  m (PartialF sym (SymSequence sym) a)
toPartialSeq sym s = PartialF <$> traverseSymSequence sym (\x -> pure $ WP.PE (WI.truePred sym) x) s

-- | Map the given function over a sequence, filtering elements according to
--   the resulting predicate. Additionally if the result of the function includes
--   a 'Just x' result, the resulting value will be used in place in the resulting sequence.
updateFilterSeq ::
  WI.IsExprBuilder sym =>
  OrdF (W4B.SymExpr sym) =>
  IO.MonadIO m =>
  sym ->
  (x -> m (Maybe x, WI.Pred sym)) ->
  SymSequence sym x ->
  m (SymSequence sym x)
updateFilterSeq sym f_ s_ = evalWithFreshCache f s_
  where
    f _rec SymSequenceNil = IO.liftIO $ nilSymSequence sym

    f rec s@(SymSequenceCons _ x xs) = do
      xs' <- rec xs
      (mx, p) <- f_ x
      let x' = fromMaybe x mx
      -- Try not to rebuild the sequence if we don't need to
      let get_seq = case xs == xs' && not (isJust mx) of
            True -> return s
            False -> IO.liftIO $ consSymSequence sym x' xs'
      
      case WI.asConstantPred p of
        Just True -> get_seq
        Just False -> return xs'
        _ -> do
          s' <- get_seq
          IO.liftIO $ muxSymSequence sym p s' xs'

    f rec s@(SymSequenceAppend _ xs ys) = do
      xs' <- rec xs
      ys' <- rec ys
      case xs' == xs && ys' == ys of
        True -> return s
        False -> IO.liftIO $ appendSymSequence sym xs' ys'

    f rec s@(SymSequenceMerge _ p xs ys) = do
      xs' <- rec xs
      ys' <- rec ys
      case xs' == xs && ys' == ys of
        True -> return s
        False -> IO.liftIO $ muxSymSequence sym p xs' ys'


instance ExprMappable sym () where
  mapExpr _sym _f _e = pure ()

instance ExprMappable sym Text where
  mapExpr _ _ = return

instance (Ord f, ExprMappable sym f) => ExprMappable sym (MT.MuxTree sym f) where
  mapExpr sym (f :: forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) mt = do
    go (MT.viewMuxTree @sym mt)
    where
      go :: WI.IsExprBuilder sym => [(f, WI.Pred sym)] -> m (MT.MuxTree sym f)
      go [] = error "Unexpected empty Mux Tree"
      go [(a,_p)] = MT.toMuxTree sym <$> mapExpr sym f a
      go ((a, p):xs) = do
        a' <- MT.toMuxTree sym <$> mapExpr sym f a
        x <- go xs
        p' <- f p
        IO.liftIO $ MT.mergeMuxTree sym p' a' x

-- | Wrapper for 'MapF' indicating that only the elements of the map should be
--   traversed with 'mapExpr'
newtype ExprMapFElems a b = ExprMapFElems { unExprMapFElems :: (MapF a b) }

instance (forall tp. ExprMappable sym (f tp)) => ExprMappable sym (ExprMapFElems a f) where
  mapExpr sym f (ExprMapFElems m) = ExprMapFElems <$> TF.traverseF (mapExpr sym f) m