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
{-# LANGUAGE ConstraintKinds #-}
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
  , parsedFunctionEntries
  , markEntryPoint

  , ValidSym
  , Sym(..)

  --- register helpers
  , zipRegStates
  , zipRegStatesPar
  , zipWithRegStatesM
  --- reporting
  , EquivalenceStatistics(..)
  , EquivalenceStatus(..)
  , equivSuccess
  , ppEquivalenceStatistics
  )
where

import           Control.Lens hiding ( op, pre )
import           Control.Monad ( join )

import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import           Data.Map ( Map )
import qualified Data.Map as M

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )

import qualified Lang.Crucible.Backend as CB

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Solver as WS

import           Pate.Address
import           Pate.Block
import qualified Pate.Parallel as PP

----------------------------------

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))

-- | Return the list of entry points in the parsed function map
parsedFunctionEntries :: ParsedFunctionMap arch -> [MM.ArchSegmentOff arch]
parsedFunctionEntries = concatMap M.keys . IM.elems

markEntryPoint ::
  MM.ArchSegmentOff arch ->
  ParsedBlockMap arch ids ->
  ParsedFunctionMap arch
markEntryPoint segOff blocks = M.singleton segOff (Some blocks) <$ getParsedBlockMap blocks

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


data EquivalenceStatistics = EquivalenceStatistics
  { numPairsChecked :: Int
  , numEquivalentPairs :: Int
  , numPairsErrored :: Int
  } deriving (Eq, Ord, Read, Show)

instance Semigroup EquivalenceStatistics where
  EquivalenceStatistics checked total errored <> EquivalenceStatistics checked' total' errored' = EquivalenceStatistics
    (checked + checked')
    (total + total')
    (errored + errored')

instance Monoid EquivalenceStatistics where
  mempty = EquivalenceStatistics 0 0 0


data EquivalenceStatus =
    Equivalent
  | Inequivalent
  | ConditionallyEquivalent
  | Errored String

instance Semigroup EquivalenceStatus where
  Errored err <> _ = Errored err
  _ <> Errored err = Errored err
  Inequivalent <> _ = Inequivalent
  _ <> Inequivalent = Inequivalent
  ConditionallyEquivalent <> _ = ConditionallyEquivalent
  _ <> ConditionallyEquivalent = ConditionallyEquivalent
  Equivalent <> Equivalent = Equivalent

instance Monoid EquivalenceStatus where
  mempty = Equivalent

equivSuccess :: EquivalenceStatistics -> Bool
equivSuccess (EquivalenceStatistics checked total errored) = errored == 0 && checked == total

----------------------------------


----------------------------------

-- Register helpers

zipRegStatesPar :: PP.IsFuture m future
                => MM.RegisterInfo r
                => MM.RegState r f
                -> MM.RegState r g
                -> (forall u. r u -> f u -> g u -> m (future h))
                -> m (future [h])
zipRegStatesPar regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> Const <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  PP.promise $ mapM (\(MapF.Pair _ (Const v)) -> PP.joinFuture v) $ MapF.toList $ MM.regStateMap regs'

zipRegStates :: Monad m
             => MM.RegisterInfo r
             => MM.RegState r f
             -> MM.RegState r g
             -> (forall u. r u -> f u -> g u -> m h)
             -> m [h]
zipRegStates regs1 regs2 f = join $ zipRegStatesPar regs1 regs2 (\r e1 e2 -> return $ f r e1 e2)

zipWithRegStatesM :: Monad m
                  => MM.RegisterInfo r
                  => MM.RegState r f
                  -> MM.RegState r g
                  -> (forall u. r u -> f u -> g u -> m (h u))
                  -> m (MM.RegState r h)
zipWithRegStatesM regs1 regs2 f = MM.mkRegStateM (\r -> f r (regs1 ^. MM.boundValue r) (regs2 ^. MM.boundValue r))

----------------------------------

type ValidSym sym =
  ( W4.IsExprBuilder sym
  , CB.IsSymInterface sym
  , ShowF (W4.SymExpr sym)
  )

data Sym sym where
  Sym :: (sym ~ (W4B.ExprBuilder t st fs), ValidSym sym) => PN.Nonce PN.GlobalNonceGenerator sym -> sym -> WS.SolverAdapter st -> Sym sym

----------------------------------


----------------------------------

ppEquivalenceStatistics :: EquivalenceStatistics -> String
ppEquivalenceStatistics (EquivalenceStatistics checked equiv err) = unlines
  [ "Summary of checking " ++ show checked ++ " pairs:"
  , "\t" ++ show equiv ++ " equivalent"
  , "\t" ++ show (checked-equiv-err) ++ " inequivalent"
  , "\t" ++ show err ++ " skipped due to errors"
  ]

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
