{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}

module Pate.Equivalence.EquivalenceDomain (
    EquivalenceDomain(..)
  , mux
  , intersect
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
import qualified What4.PredMap as WPM
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
    , eqDomainMaxRegion :: PL.NamedPred sym WPM.PredDisjT "maxRegion"
    }  -> EquivalenceDomain sym arch

instance (WI.IsSymExprBuilder sym, OrdF (WI.SymExpr sym), MM.RegisterInfo (MM.ArchReg arch)) => PL.LocationTraversable sym arch (EquivalenceDomain sym arch) where
  traverseLocation sym x f = PL.witherLocation sym x (\loc p -> Just <$> f loc p)

instance (WI.IsSymExprBuilder sym, OrdF (WI.SymExpr sym), MM.RegisterInfo (MM.ArchReg arch)) => PL.LocationWitherable sym arch (EquivalenceDomain sym arch) where
  witherLocation sym (EquivalenceDomain a b c d) f = 
    EquivalenceDomain 
    <$> PL.witherLocation sym a f 
    <*> PL.witherLocation sym b f 
    <*> PL.witherLocation sym c f
    <*> PL.witherLocation sym d f


ppEquivalenceDomain ::
  forall sym arch a.
  ( MM.RegisterInfo (MM.ArchReg arch)
  , WI.IsSymExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  -- | Called when a cell is in the domain conditionally, with
  -- a non-trivial condition
  (WI.Pred sym -> PP.Doc a) ->
   -- FIXME: can't use displayRegister from Arch due to import cycle
  (forall tp. MM.ArchReg arch tp -> Maybe (PP.Doc a)) ->
  EquivalenceDomain sym arch ->
  PP.Doc a
ppEquivalenceDomain showCond showReg dom =
  PP.vsep
  [ "== Registers =="
 
  , PER.ppRegisterDomain showCond showReg (eqDomainRegisters dom)
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
    mr <- PL.NamedPred <$> WPM.mux sym p (PL.namedPredMap $ eqDomainMaxRegion domT) (PL.namedPredMap $ eqDomainMaxRegion domF)
    return $ EquivalenceDomain regs stack mem mr

intersect ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  EquivalenceDomain sym arch ->
  EquivalenceDomain sym arch ->
  IO (EquivalenceDomain sym arch)
intersect sym dom1 dom2 = do
  regs <- PER.intersect sym (eqDomainRegisters dom1) (eqDomainRegisters dom2)
  stack <- PEM.intersect sym (eqDomainStackMemory dom1) (eqDomainStackMemory dom2)
  mem <- PEM.intersect sym (eqDomainGlobalMemory dom1) (eqDomainGlobalMemory dom2)
  mr <- PL.NamedPred <$> WPM.intersect sym (PL.namedPredMap $ eqDomainMaxRegion dom1) (PL.namedPredMap $ eqDomainMaxRegion dom2)
  return $ EquivalenceDomain regs stack mem mr

instance PEM.ExprMappable sym (EquivalenceDomain sym arch) where
  mapExpr sym f dom = do
    regs <- PEM.mapExpr sym f (eqDomainRegisters dom)
    stack <- PEM.mapExpr sym f (eqDomainStackMemory dom)
    mem <- PEM.mapExpr sym f (eqDomainGlobalMemory dom)
    mr <- PEM.mapExpr sym f (eqDomainMaxRegion dom)
    return $ EquivalenceDomain regs stack mem mr
