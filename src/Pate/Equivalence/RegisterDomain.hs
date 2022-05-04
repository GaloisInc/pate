{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings   #-}
module Pate.Equivalence.RegisterDomain (
    RegisterDomain
  , mux
  , universal
  , empty
  , update
  , toList
  , fromList
  , fromRegState
  , registerInDomain
  , registerInDomain'
  , traverseWithReg
  , ppRegisterDomain
  ) where

import           Control.Monad (  foldM )
import           Data.Functor.Const
import           Data.Maybe ( mapMaybe )
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map

import qualified What4.Interface as WI

import qualified Data.Macaw.CFG as MM

import qualified Prettyprinter as PP

import qualified Pate.Solver as PS
import qualified Pate.ExprMappable as PEM

---------------------------------------------
-- Register domain

-- | The register domain of an equivalence problem: representing the registers that are either
-- assumed (in a pre-domain) or proven (in a post-domain) to be equivalent.

newtype RegisterDomain sym arch =
  RegisterDomain { _unRD :: Map (Some (MM.ArchReg arch)) (WI.Pred sym) }

traverseWithReg ::
  forall m sym arch.
  WI.IsExprBuilder sym =>
  Applicative m =>
  RegisterDomain sym arch ->
  (forall tp. MM.ArchReg arch tp -> WI.Pred sym -> m (WI.Pred sym)) ->
  m (RegisterDomain sym arch)
traverseWithReg (RegisterDomain dom) f =
  mkDomain <$> Map.traverseWithKey f' dom
    where
      f' :: Some (MM.ArchReg arch) -> WI.Pred sym -> m (WI.Pred sym)
      f' (Some reg) p = f reg p

update ::
  forall sym arch tp.
  WI.IsExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  (WI.Pred sym -> WI.Pred sym) ->
  MM.ArchReg arch tp ->
  RegisterDomain sym arch ->
  RegisterDomain sym arch
update sym f reg (RegisterDomain dom) = RegisterDomain $ Map.alter f' (Some reg) dom
  where
    f' :: Maybe (WI.Pred sym) -> Maybe (WI.Pred sym)
    f' Nothing = Just (f (WI.falsePred sym))
    f' (Just p) = case WI.asConstantPred p of
      Just False -> Nothing
      _ -> Just (f p)

mkDomain ::
  forall sym arch.
  WI.IsExprBuilder sym =>
  Map (Some (MM.ArchReg arch)) (WI.Pred sym) ->
  RegisterDomain sym arch
mkDomain dom = dropFalseRegisters $ RegisterDomain dom

-- | Drop entries with false conditions.
dropFalseRegisters ::
  forall sym arch.
  WI.IsExprBuilder sym =>
  RegisterDomain sym arch ->
  RegisterDomain sym arch
dropFalseRegisters (RegisterDomain dom) = RegisterDomain $ Map.mapMaybe dropFalse dom
  where
    dropFalse ::
      WI.Pred sym ->
      Maybe (WI.Pred sym)
    dropFalse p = case WI.asConstantPred p of
      Just False -> Nothing
      _ -> Just p

-- | Register domain that contains all registers
universal ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  sym ->
  RegisterDomain sym arch
universal sym = fromRegState $ MM.mkRegState (\_ -> Const $ WI.truePred sym)

-- | Register domain that contains no registers
empty :: RegisterDomain sym arch
empty = RegisterDomain $ Map.empty

-- | Create a register domain from a list of registers and associated predicates.
-- Assumes that each register is present in the list at most once.
fromList ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  [(Some (MM.ArchReg arch), WI.Pred sym)] ->
  RegisterDomain sym arch
fromList regs = RegisterDomain $ Map.fromList regs

fromRegState ::
  forall sym arch.
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  MM.RegState (MM.ArchReg arch) (Const (WI.Pred sym)) ->
  RegisterDomain sym arch
fromRegState regState =
  let
    mapF = MapF.toAscList $ MM.regStateMap regState
    f (MapF.Pair reg (Const p)) = case WI.asConstantPred p of
      Just False -> Nothing
      _ -> Just (Some reg, p)
  in RegisterDomain $ Map.fromAscList $ mapMaybe f mapF

toList ::
  RegisterDomain sym arch ->
  [(Some (MM.ArchReg arch), WI.Pred sym)]
toList (RegisterDomain regs) = Map.toList regs


mux ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  WI.Pred sym ->
  RegisterDomain sym arch ->
  RegisterDomain sym arch ->
  IO (RegisterDomain sym arch)
mux sym p (RegisterDomain domT) (RegisterDomain domF) = case WI.asConstantPred p of
  Just True -> return $ RegisterDomain domT
  Just False -> return $ RegisterDomain domF
  _ -> mkDomain <$> do
    notp <- WI.notPred sym p
    Map.mergeA
      (Map.traverseMissing (\_ pT -> WI.andPred sym pT p))
      (Map.traverseMissing (\_ pF -> WI.andPred sym pF notp))
      (Map.zipWithAMatched (\_ p1 p2 -> WI.baseTypeIte sym p p1 p2))
      domT
      domF

-- | Specialized 'registerInDomain' that returns 'Nothing' if the
-- register is in concretely known to not be in the domain.
registerInDomain' ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  MM.ArchReg arch tp ->
  RegisterDomain sym arch ->
  Maybe (WI.Pred sym)
registerInDomain' reg (RegisterDomain dom) = Map.lookup (Some reg) dom

-- | Predicate that is true iff the given register is in this domain
registerInDomain ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  sym ->
  MM.ArchReg arch tp ->
  RegisterDomain sym arch ->
  WI.Pred sym
registerInDomain sym reg dom = case registerInDomain' reg dom of
  Just p -> p
  Nothing -> WI.falsePred sym

instance PEM.ExprMappable sym (RegisterDomain sym arch) where
  mapExpr _sym f (RegisterDomain dom) = mkDomain <$> traverse f dom

ppRegisterDomain ::
  forall sym arch a.
  ( MM.RegisterInfo (MM.ArchReg arch)
  , WI.IsExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  (WI.Pred sym -> PP.Doc a) ->
  RegisterDomain sym arch ->
  PP.Doc a
ppRegisterDomain showCond dom =
  PP.vsep
   [ PP.pretty (showF reg) <> PP.line <> (PP.indent 2 (showCond p))
   | (Some reg, p) <- toList dom
   , WI.asConstantPred p /= Just True
   ]

instance
  (MM.RegisterInfo (MM.ArchReg arch), WI.IsExprBuilder sym) =>
  PP.Pretty (RegisterDomain sym arch) where
  pretty = ppRegisterDomain WI.printSymExpr
