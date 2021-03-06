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
  ( BlockMapping(..)
  , BlockTarget(..)
  , ParsedBlockMap(..)
  , ParsedFunctionMap
  )
where

import           Data.IntervalMap (IntervalMap)
import           Data.Map ( Map )
import qualified Data.Map as M

import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD

import           Pate.Address
import           Pate.Block

----------------------------------

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))

----------------------------------


data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

-- | Map from the start of original blocks to patched block addresses
newtype BlockMapping arch = BlockMapping (M.Map (ConcreteAddress arch) (ConcreteAddress arch))



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
