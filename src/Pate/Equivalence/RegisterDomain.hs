{-# LANGUAGE DataKinds #-}
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
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeApplications   #-}

module Pate.Equivalence.RegisterDomain (
    RegisterDomain
  , mux
  , intersect
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

import qualified Pate.Location as PL
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

instance (WI.IsExprBuilder sym, MM.RegisterInfo (MM.ArchReg arch)) => PL.LocationWitherable sym arch (RegisterDomain sym arch) where
  witherLocation _sym (RegisterDomain d) f = do
    d' <- Map.traverseMaybeWithKey (\(Some r) p -> f (PL.Location @"register" r) p >>= \case
            Just (_, p') -> return (Just p')
            Nothing -> return Nothing) d
    return $ RegisterDomain d'

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
mkDomain dom = RegisterDomain dom

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

dropFalse ::
  PS.ValidSym sym =>
  RegisterDomain sym arch ->
  RegisterDomain sym arch
dropFalse (RegisterDomain d) = mkDomain $ 
  Map.filter (\p -> case WI.asConstantPred p of Just False -> False; _ -> True) d

-- | Combine two 'RegisterDomain' values, where a register is
-- in the resulting domain iff it is in both of the input domains
-- (intersection)
intersect ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  RegisterDomain sym arch ->
  RegisterDomain sym arch ->
  IO (RegisterDomain sym arch)
intersect sym (RegisterDomain domA) (RegisterDomain domB) = (dropFalse . mkDomain) <$> do
  Map.mergeA
    (Map.traverseMissing (\_ _ -> return $ WI.falsePred sym ))
    (Map.traverseMissing (\_ _ -> return $ WI.falsePred sym))
    (Map.zipWithAMatched (\_ pA pB -> WI.andPred sym pA pB))
    domA
    domB 

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
  (forall tp. MM.ArchReg arch tp -> Maybe (PP.Doc a)) ->
  RegisterDomain sym arch ->
  PP.Doc a
ppRegisterDomain showCond showReg dom =
  PP.vsep
   [ PP.vsep ([reg_s] ++
      case (registerInDomain' reg dom) of
        Nothing -> []
        Just p | Just False <- WI.asConstantPred p -> []
        Just p -> [PP.indent 2 (showCond p)]
             )
   | (MapF.Pair reg _) <- MapF.toList (MM.archRegSet @(MM.ArchReg arch))
   , Just reg_s <- [showReg reg]
   -- FIXME: should we always exclude these from printing?
   , (Some reg) /= (Some (MM.sp_reg @(MM.ArchReg arch)))
   , (Some reg) /= (Some (MM.ip_reg @(MM.ArchReg arch)))
   , (fmap WI.asConstantPred (registerInDomain' reg dom)) /= (Just (Just True))
   ]

instance
  (MM.RegisterInfo (MM.ArchReg arch), WI.IsExprBuilder sym) =>
  PP.Pretty (RegisterDomain sym arch) where
  pretty = ppRegisterDomain WI.printSymExpr (\r -> Just (PP.pretty (showF r)))
