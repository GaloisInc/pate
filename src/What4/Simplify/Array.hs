{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module What4.Simplify.Array (
    multiArraySimplify
) where

import qualified Control.Monad.IO.Class as IO
import           Control.Monad.Trans (lift)

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC

import           What4.Simplify
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B



-- | Wrap accesses to multi-dimensional arrays in defined function calls.
--   If the base array is a variable, the function is given the same name.
---  Otherwise, a generic "multiArray" function is defined, where the array
--   is passed as an argument.
multiArraySimplifyApp ::
  forall sym m tp.
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  W4B.App (W4.SymExpr sym) tp -> 
  SimpT sym m (W4.SymExpr sym tp)
multiArraySimplifyApp rec app =  withSym $ \sym -> do
  -- looking for arrays with at least two index elements
  W4B.SelectArray _ arr args@(_ Ctx.:> _ Ctx.:> _) <- return app
  args' <- TFC.traverseFC (\arg -> lift $ rec arg) args
  arr' <- lift $ rec arr


  vars <- IO.liftIO $ 
    TFC.traverseFC (\arg -> W4.freshBoundVar sym W4.emptySymbol (W4.exprType arg)) args
  let vals = TFC.fmapFC (W4.varExpr sym) vars
  case arr' of
    W4B.BoundVarExpr bv -> IO.liftIO $ do
      body <- W4.arrayLookup sym arr' vals
      let nm = W4B.bvarName bv
      fn <-  W4.definedFn sym nm vars body W4.NeverUnfold
      W4.applySymFn sym fn args'

    _ -> IO.liftIO $ do
      arr_var <- W4.freshBoundVar sym W4.emptySymbol (W4.exprType arr)
      body <- W4.arrayLookup sym (W4.varExpr sym arr_var) vals
      let nm = W4.safeSymbol "multiArray"
      fn <-  W4.definedFn sym nm (vars Ctx.:> arr_var) body W4.NeverUnfold
      W4.applySymFn sym fn (args' Ctx.:> arr')

multiArraySimplify ::
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) => 
  SimpStrategy sym m
multiArraySimplify = liftSimpTStrategy multiArraySimplifyApp
