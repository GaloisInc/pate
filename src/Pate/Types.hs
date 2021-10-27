{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveTraversable #-}


-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Types
  ( BlockTarget(..)
  )
where

import qualified Data.Macaw.CFG as MM

import           Pate.Block

----------------------------------


----------------------------------


data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"


----------------------------------


----------------------------------


--------------------------------

-- showModelForExpr :: forall sym tp.
--   SymGroundEvalFn sym ->
--   W4.SymExpr sym tp ->
--   IO String
-- showModelForExpr fn@(SymGroundEvalFn _) expr = do
--   freeTerms <- freeExprTerms expr
--   v <- execGroundFnIO fn expr
--   let
--     s = "Expression: " ++ show expr ++ "\n" ++
--         "Value: " ++ showGroundValue (W4.exprType expr) v ++ "\n" ++
--         "Environment:"

--   foldM go s freeTerms
--   where
--     go :: String -> Some (W4.SymExpr sym)  -> IO String
--     go s (Some e) = do
--       gv <- execGroundFnIO fn e
--       return $ s ++ "\n" ++ show e ++ " :== " ++ showGroundValue (W4.exprType e) gv

-- showGroundValue ::
--   W4.BaseTypeRepr tp ->
--   W4G.GroundValue tp ->
--   String
-- showGroundValue repr gv = case repr of
--   W4.BaseBoolRepr -> show gv
--   W4.BaseBVRepr w -> BVS.ppHex w gv
--   W4.BaseIntegerRepr -> show gv
--   _ -> "Unsupported ground value"
