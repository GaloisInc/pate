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
-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}
module Pate.ExprMappable (
    ExprMappable(..)
  , NoExprMap(..)
  ) where

import qualified Data.IORef as IO

import           Data.Functor.Const
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
    sym ->
    (forall tp. WI.SymExpr sym tp -> IO (WI.SymExpr sym tp)) ->
    f ->
    IO f
  foldMapExpr ::
    WI.IsSymExprBuilder sym =>
    sym ->
    (forall tp. WI.SymExpr sym tp -> b -> IO (WI.SymExpr sym tp, b)) ->
    f ->
    b ->
    IO (f, b)    
  foldMapExpr sym f e b = do
    ref <- IO.newIORef b
    let
      f' :: forall tp. WI.SymExpr sym tp -> IO (WI.SymExpr sym tp)
      f' e' = do
          b' <- IO.readIORef ref
          (e'', b'') <- f e' b'
          IO.writeIORef ref b''
          return e''
    e' <- mapExpr sym f' e
    b' <- IO.readIORef ref
    return (e', b')
  foldExpr ::
    WI.IsSymExprBuilder sym =>
    sym ->
    (forall tp. WI.SymExpr sym tp -> b -> IO b) ->
    f ->
    b ->
    IO b    
  foldExpr sym f e b = snd <$> foldMapExpr sym (\e' b' -> f e' b' >>= \b'' -> return (e', b'')) e b

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


instance ExprMappable sym f => ExprMappable sym (Par.Future f) where
  mapExpr sym f future = Par.forFuture future (mapExpr sym f)
  -- | Folding on a "future" requires joining it first
  foldMapExpr sym f future b = do
    result <- Par.joinFuture future
    (result', b') <- foldMapExpr sym f result b
    return (Par.Immediate result', b')

instance ExprMappable sym (f (a tp)) => ExprMappable sym (Par.ConstF f a tp) where
  mapExpr sym f (Par.ConstF a) = Par.ConstF <$> mapExpr sym f a

instance ExprMappable sym f => ExprMappable sym ((Const f) tp)  where
  mapExpr sym f (Const e) = Const <$> mapExpr sym f e
  foldMapExpr sym f (Const e) b = do
    (e', b') <- foldMapExpr sym f e b
    return $ (Const e', b')

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
  foldMapExpr _sym f e b = f e b


-- | Wrap a type to give a trivial 'ExprMappable' instance (i.e. make 'mapExpr' a no-op)
newtype NoExprMap a = NoExprMap { unNEM :: a }

instance ExprMappable sym (NoExprMap a) where
  mapExpr _ _ = return
  foldMapExpr _ _ f b = return (f, b)
