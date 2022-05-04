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
-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}
module Pate.ExprMappable (
    ExprMappable(..)
  , ExprFoldable(..)
  , SkipTransformation(..)
  , ToExprMappable(..)
  ) where

import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Trans.State as CMS
import           Control.Monad.Trans.Class ( lift )

import           Data.Functor.Const
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI
import qualified What4.Partial as WP
import qualified What4.Expr.Builder as W4B

import qualified What4.ExprHelpers as WEH
import qualified Pate.Parallel as Par

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

instance ExprMappable sym (CS.RegValue' sym (CT.BaseToType bt)) where
  mapExpr _ f (CS.RV x) = CS.RV <$> f x

instance ExprMappable sym (CS.RegValue' sym (CLM.LLVMPointerType w)) where
  mapExpr sym f (CS.RV x) = CS.RV <$> WEH.mapExprPtr sym f x

instance ExprMappable sym (CS.RegValue' sym tp) => ExprMappable sym (CS.RegValue' sym (CT.MaybeType tp)) where
  mapExpr sym f (CS.RV pe) = CS.RV <$> case pe of
    WP.PE p e -> do
      p' <- f p
      CS.RV e' <- mapExpr sym f (CS.RV @sym @tp e)
      return $ WP.PE p' e'
    WP.Unassigned -> return WP.Unassigned


instance ExprMappable sym (f (a tp)) => ExprMappable sym (Par.ConstF f a tp) where
  mapExpr sym f (Par.ConstF a) = Par.ConstF <$> mapExpr sym f a

instance ExprMappable sym f => ExprMappable sym ((Const f) tp)  where
  mapExpr sym f (Const e) = Const <$> mapExpr sym f e

instance (forall tp. ExprMappable sym (f tp)) => ExprMappable sym (Some f) where
  mapExpr sym f (Some v) = Some <$> mapExpr sym f v

instance ExprMappable sym (Ctx.Assignment f Ctx.EmptyCtx) where
  mapExpr _ _ = return

instance
  (ExprMappable sym (Ctx.Assignment f ctx), ExprMappable sym (f tp)) =>
  ExprMappable sym (Ctx.Assignment f (ctx Ctx.::> tp)) where
  mapExpr sym f (asn Ctx.:> x) = do
    asn' <- mapExpr sym f asn
    x' <- mapExpr sym f x
    return $ asn' Ctx.:> x'


instance ExprMappable (W4B.ExprBuilder t st fs) (W4B.Expr t tp) where
  mapExpr _sym f e = f e

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
