{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Equivalence.EquivalenceDomain (
    EquivalenceDomain(..)
  , mux
  , ppEquivalenceDomain
  ) where

import qualified What4.Interface as WI
import qualified Prettyprinter as PP
import           Data.Parameterized.Classes

import qualified Data.Macaw.CFG as MM

import qualified Pate.Solver as PS
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.ExprMappable as PEM
import qualified Pate.Location as PL

---------------------------------------------
-- Equivalence domain

-- | The domain of an equivalence problem: representing the state that is either
-- assumed (in a pre-domain) or proven (in a post-domain) to be equivalent.
data EquivalenceDomain sym arch where
  EquivalenceDomain ::
    { -- | Each register is considered to be in this domain if the given predicate is true.
      eqDomainRegisters :: PER.RegisterDomain sym arch
      -- | The memory domain that is specific to stack variables.
    , eqDomainStackMemory :: PEM.MemoryDomain sym arch
      -- | The memory domain that is specific to non-stack (i.e. global) variables.
    , eqDomainGlobalMemory :: PEM.MemoryDomain sym arch
    }  -> EquivalenceDomain sym arch

instance (WI.IsExprBuilder sym, OrdF (WI.SymExpr sym), MM.RegisterInfo (MM.ArchReg arch)) => PL.LocationWitherable sym arch (EquivalenceDomain sym arch) where
  witherLocation sym (EquivalenceDomain a b c) f = EquivalenceDomain <$> PL.witherLocation sym a f <*> PL.witherLocation sym b f <*> PL.witherLocation sym c f


ppEquivalenceDomain ::
  forall sym arch a.
  ( MM.RegisterInfo (MM.ArchReg arch)
  , WI.IsSymExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  -- | Called when a cell is in the domain conditionally, with
  -- a non-trivial condition
  (WI.Pred sym -> PP.Doc a) ->
  EquivalenceDomain sym arch ->
  PP.Doc a
ppEquivalenceDomain showCond dom =
  PP.vsep
  [ "== Registers =="
  , PER.ppRegisterDomain showCond (eqDomainRegisters dom)
  , "== Stack =="
  , PEM.ppMemoryDomainEntries showCond (eqDomainStackMemory dom)
  , "== Globals =="
  , PEM.ppMemoryDomainEntries showCond (eqDomainGlobalMemory dom)
  ]


mux ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  WI.Pred sym ->
  EquivalenceDomain sym arch ->
  EquivalenceDomain sym arch ->
  IO (EquivalenceDomain sym arch)
mux sym p domT domF = case WI.asConstantPred p of
  Just True -> return domT
  Just False -> return domF
  _ -> do
    regs <- PER.mux sym p (eqDomainRegisters domT) (eqDomainRegisters domF)
    stack <- PEM.mux sym p (eqDomainStackMemory domT) (eqDomainStackMemory domF)
    mem <- PEM.mux sym p (eqDomainGlobalMemory domT) (eqDomainGlobalMemory domF)
    return $ EquivalenceDomain regs stack mem


instance PEM.ExprMappable sym (EquivalenceDomain sym arch) where
  mapExpr sym f dom = do
    regs <- PEM.mapExpr sym f (eqDomainRegisters dom)
    stack <- PEM.mapExpr sym f (eqDomainStackMemory dom)
    mem <- PEM.mapExpr sym f (eqDomainGlobalMemory dom)
    return $ EquivalenceDomain regs stack mem
