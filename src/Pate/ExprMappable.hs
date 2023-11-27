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
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}
{-# OPTIONS_GHC -fno-warn-simplifiable-class-constraints #-}

module Pate.ExprMappable (
    ExprMappable2(..)
  , ExprMappable
  , ExprFoldable(..)
  , mapExpr
  , SkipTransformation(..)
  , ToExprMappable(..)
  , SymExprMappable(..)
  , symExprMappable
  , SymExprMappable2(..)
  , symExprMappable2
  , PartialF(..)
  , toPartialSeq
  , updateFilterSeq
  , ExprMapFElems(..)
  , HasSymComparator
  , ValidTargetSym
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
import Control.Monad (forM)
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.TraversableF as TF

-- Expression binding

-- | Declares a type as being expression-containing, where the given traversal
--   occurs shallowly (i.e. not applied recursively to sub-expressions) on all embedded expressions.

type HasSymComparator sym1 sym2 = (?compareSym :: Maybe (sym1 :~: sym2))  
type ExprMappable sym f = ExprMappable2 sym sym f f

mapExpr ::
  ExprMappable sym f =>
  WI.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (forall tp. WI.SymExpr sym tp -> m (WI.SymExpr sym tp)) ->
  f ->
  m f
mapExpr sym f a = 
  let ?compareSym = Just Refl in 
    WPM.asHasPredOps sym $ mapExpr2 sym sym f a

type ValidTargetSym sym' = (WEH.HasIntegerToNat sym', WPM.HasPredOps sym', OrdF (WI.SymExpr sym'))

class ExprMappable2 sym sym' f f' where
  mapExpr2 ::
    (WI.IsSymExprBuilder sym,
    ValidTargetSym sym',
    HasSymComparator sym sym',
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

instance (ExprMappable2 sym sym' a a', ExprMappable2 sym sym' b b') => ExprMappable2 sym sym' (a, b) (a', b') where
  mapExpr2 sym sym' f (a, b) = (,) <$> mapExpr2 sym sym' f a <*> mapExpr2 sym sym' f b

instance ExprMappable2 sym sym' (CS.RegValue' sym (CT.BaseToType bt)) (CS.RegValue' sym' (CT.BaseToType bt)) where
  mapExpr2 _ _ f (CS.RV x) = CS.RV <$> f x

instance ExprMappable2 sym sym' (CS.RegValue' sym (CLM.LLVMPointerType w)) (CS.RegValue' sym' (CLM.LLVMPointerType w)) where
  mapExpr2 sym sym' f (CS.RV x) = CS.RV <$> WEH.mapExprPtr2 sym sym' f x

instance forall sym sym' tp. ExprMappable2 sym sym' (CS.RegValue' sym tp) (CS.RegValue' sym' tp) => ExprMappable2 sym sym' (CS.RegValue' sym (CT.MaybeType tp)) (CS.RegValue' sym' (CT.MaybeType tp)) where
  mapExpr2 sym sym' f (CS.RV pe) = do
    (e' :: CS.RegValue sym' (CT.MaybeType tp)) <- case pe of
      WP.PE p e -> do
        (p' :: WI.Pred sym') <- f p
        CS.RV e' <- mapExpr2 @_ @_ @_ @(CS.RegValue' sym' tp) sym sym' f (CS.RV @sym @tp e)
        return $ (WP.PE @(WI.Pred sym') @(CS.RegValue sym' tp) p' e')
      WP.Unassigned -> return $ (WP.Err @_ @(WI.Pred sym') @(CS.RegValue sym' tp) ())
    return $ CS.RV e'

instance ExprMappable2 sym sym' (f (a tp)) (g (b tp)) => ExprMappable2 sym sym' (Par.ConstF f a tp) (Par.ConstF g b tp) where
  mapExpr2 sym sym' f (Par.ConstF a) = Par.ConstF <$> mapExpr2 sym sym' f a

instance ExprMappable2 sym sym' f g => ExprMappable2 sym sym' ((Const f) tp) ((Const g) tp') where
  mapExpr2 sym sym' f (Const e) = Const <$> mapExpr2 sym sym' f e

instance forall sym sym' f f'. (forall tp. ExprMappable2 sym sym' (f tp) (f' tp)) => ExprMappable2 sym sym' (Some f) (Some f') where
  mapExpr2 sym sym' f (Some (v :: f tp)) = Some <$> mapExpr2 @_ @_ @(f tp) @(f' tp) sym sym' f v

instance ExprMappable2 sym sym' a a' => ExprMappable2 sym sym' (Maybe a) (Maybe a') where
  mapExpr2 sym sym' f ma = case ma of
    Just a -> Just <$> mapExpr2 sym sym' f a
    Nothing -> return Nothing

instance ExprMappable2 sym sym' (Ctx.Assignment f Ctx.EmptyCtx) (Ctx.Assignment f' Ctx.EmptyCtx)  where
  mapExpr2 _sym _sym' _f _ = return Ctx.empty

instance
  (ExprMappable2 sym sym' (Ctx.Assignment f ctx) (Ctx.Assignment f' ctx), ExprMappable2 sym sym' (f tp) (f' tp)) =>
  ExprMappable2 sym sym' (Ctx.Assignment f (ctx Ctx.::> tp)) (Ctx.Assignment f' (ctx Ctx.::> tp)) where
  mapExpr2 sym sym' f (asn Ctx.:> x) = do
    asn' <- mapExpr2 sym sym' f asn
    x' <- mapExpr2 sym sym' f x
    return $ asn' Ctx.:> x'

instance ExprMappable2 (W4B.ExprBuilder t st fs) (W4B.ExprBuilder t' st' fs') (W4B.Expr t tp) (W4B.Expr t' tp) where
  mapExpr2 sym1 sym2 f e = applyExprMappable sym1 sym2 f e

-- | This is a bit redundant, but it forces the function to be evaluated
--   according to the 'ToExprMappable' instance for 'ExprMappable', which
--   avoids the potential for conflicting instances for 'W4B.Expr' vs. 'WI.SymExpr'
--   when using 'symExprMappable'.
applyExprMappable ::
  forall sym sym' tp m.
  IO.MonadIO m =>
  WI.IsSymExprBuilder sym =>
  ValidTargetSym sym' =>
  HasSymComparator sym sym' =>
  sym ->
  sym' ->
  (forall tp'. WI.SymExpr sym tp' -> m (WI.SymExpr sym' tp')) ->
  WI.SymExpr sym tp ->
  m (WI.SymExpr sym' tp)
applyExprMappable sym sym' f e | SymExprMappable2 asEM <- symExprMappable2 sym sym' =
  asEM @tp $ mapExpr2 sym sym' f e

-- | Wrap a 'WI.SymExpr' as an 'ExprMappable, which can't be defined directly
-- as it is a type family
newtype ToExprMappable sym tp = ToExprMappable { unEM :: WI.SymExpr sym tp }

instance ExprMappable2 sym1 sym2 (ToExprMappable sym1 tp) (ToExprMappable sym2 tp) where
  mapExpr2 _sym1 _sym2 f (ToExprMappable e) = ToExprMappable <$> f e

instance ExprMappable2 sym1 sym2 a b => ExprMappable2 sym1 sym2 [a] [b] where
  mapExpr2 sym1 sym2 f l = mapM (mapExpr2 sym1 sym2 f) l

-- | Wrap a type to give a trivial 'ExprMappable' instance (i.e. make 'mapExpr' a no-op).
-- This is useful for carrying extra information out of functions which are otherwise
-- expected to return only ExprMappable values.
newtype SkipTransformation a = SkipTransformation { unSkip :: a }

instance ExprMappable2 sym1 sym2 (SkipTransformation a) (SkipTransformation a) where
  mapExpr2 _ _ _ = return

instance (Ord f, Ord g, ExprMappable2 sym1 sym2 f g) => ExprMappable2 sym1 sym2 (WPM.PredMap sym1 f k) (WPM.PredMap sym2 g k)  where
  mapExpr2 sym1 sym2 f pm = do
    pm' <- WPM.traverse pm (\_ p -> f p) 
    WPM.alter' sym2 pm' (\v p -> (,) <$> mapExpr2 sym1 sym2 f v <*> pure p)

instance (OrdF g, ExprMappable2 sym1 sym2 (f tp) (g tp)) => ExprMappable2 sym1 sym2 (SetF.SetF f tp) (SetF.SetF g tp) where
  mapExpr2 sym1 sym2 f s = SetF.fromList <$> traverse (mapExpr2 sym1 sym2 f) (SetF.toList s)

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

newtype SymExprMappable2 sym1 sym2 f g = SymExprMappable2 (forall tp a. ((ExprMappable2 sym1 sym2 (f tp) (g tp)) => a) -> a)

symExprMappable2 ::
  forall sym1 sym2.
  sym1 ->
  sym2 ->
  SymExprMappable2 sym1 sym2 (WI.SymExpr sym1) (WI.SymExpr sym2)
symExprMappable2 _sym =
  unsafeCoerce r
  where r :: SymExprMappable2 sym1 sym2 (ToExprMappable sym1) (ToExprMappable sym2)
        r = SymExprMappable2 (\a -> a)

instance (ExprMappable2 sym1 sym2 p1 p2, ExprMappable2 sym1 sym2 v1 v2) => 
  ExprMappable2 sym1 sym2 (WP.PartExpr p1 v1) (WP.PartExpr p2 v2)  where
    mapExpr2 sym1 sym2 f = \case
      WP.Unassigned -> pure WP.Unassigned
      WP.PE p v -> WP.PE <$> mapExpr2 sym1 sym2 f p <*> (mapExpr2 sym1 sym2 f v)

-- | Lifting a functor to partial values (i.e. values with an associated predicate)
data PartialF sym t f = PartialF (t (WP.PartExpr (WI.Pred sym) f))

instance (ExprMappable2 sym1 sym2 f g, forall x y. ExprMappable2 sym1 sym2 x y => ExprMappable2 sym1 sym2 (t x) (t' y)) => 
  ExprMappable2 sym1 sym2 (PartialF sym1 t f) (PartialF sym2 t' g) where
    mapExpr2 sym1 sym2 f (PartialF e) | SymExprMappable2 asEM <- symExprMappable2 sym1 sym2 = 
      asEM @WI.BaseBoolType $ PartialF <$> mapExpr2 sym1 sym2 f e

instance (ExprMappable2 sym1 sym2 f g) => ExprMappable2 sym1 sym2 (SymSequence sym1 f) (SymSequence sym2 g)  where
  mapExpr2 sym1 sym2 f e = traverseSymSequence sym1 (mapExpr2 sym1 sym2 f) e >>= swapSymSequenceSym sym1 sym2 f

swapSymSequenceSym ::
 forall m sym1 sym2 a.
 IO.MonadIO m =>
 sym1 ->
 sym2 ->
 (forall tp. WI.SymExpr sym1 tp -> m (WI.SymExpr sym2 tp)) ->
 SymSequence sym1 a -> 
 m (SymSequence sym2 a)
swapSymSequenceSym sym1 sym2 f s = case s of
  SymSequenceNil -> return SymSequenceNil
  SymSequenceCons n a s' -> SymSequenceCons n a <$> go s'
  SymSequenceAppend n s1 s2 -> SymSequenceAppend n <$> go s1 <*> go s2
  SymSequenceMerge n p s1 s2 -> SymSequenceMerge n <$> f p <*> go s1 <*> go s2
  where
    go :: SymSequence sym1 a -> m (SymSequence sym2 a)
    go = swapSymSequenceSym sym1 sym2 f

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


instance ExprMappable2 sym1 sym2 () () where
  mapExpr2 _sym1 _sym2 _f _e = pure ()

instance (Ord g, ExprMappable2 sym1 sym2 f g) => ExprMappable2 sym1 sym2 (MT.MuxTree sym1 f) (MT.MuxTree sym2 g) where
  mapExpr2 sym1 sym2 (f :: forall tp. WI.SymExpr sym1 tp -> m (WI.SymExpr sym2 tp)) mt = do
    WPM.asPartialBuilder sym2 $ go (MT.viewMuxTree @sym1 mt)
    where
      go :: WI.IsExprBuilder sym2 => [(f, WI.Pred sym1)] -> m (MT.MuxTree sym2 g)
      go [] = error "Unexpected empty Mux Tree"
      go [(a,_p)] = MT.toMuxTree sym2 <$> mapExpr2 sym1 sym2 f a
      go ((a, p):xs) = do
        a' <- MT.toMuxTree sym2 <$> mapExpr2 sym1 sym2 f a
        x <- go xs
        p' <- f p
        IO.liftIO $ MT.mergeMuxTree sym2 p' a' x

-- | Wrapper for 'MapF' indicating that only the elements of the map should be
--   traversed with 'mapExpr'
data ExprMapFElems a b = OrdF a => ExprMapFElems { unExprMapFElems :: (MapF a b) }

instance (forall tp. ExprMappable2 sym1 sym2 (f tp) (g tp)) => ExprMappable2 sym1 sym2 (ExprMapFElems a f) (ExprMapFElems a g) where
  mapExpr2 sym1 sym2 f (ExprMapFElems m) = ExprMapFElems <$> TF.traverseF (mapExpr2 sym1 sym2 f) m
