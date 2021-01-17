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
  ) where

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI
import qualified What4.Partial as WP

import qualified What4.ExprHelpers as WEH

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

instance ExprMappable sym (Ctx.Assignment f Ctx.EmptyCtx) where
  mapExpr _ _ = return

instance
  (ExprMappable sym (Ctx.Assignment f ctx), ExprMappable sym (f tp)) =>
  ExprMappable sym (Ctx.Assignment f (ctx Ctx.::> tp)) where
  mapExpr sym f (asn Ctx.:> x) = do
    asn' <- mapExpr sym f asn
    x' <- mapExpr sym f x
    return $ asn' Ctx.:> x'
