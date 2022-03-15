{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Pate.Equivalence.EquivalenceDomain (
    EquivalenceDomain(..)
  , RegisterDomain
  , mux
  , empty
  , registerInDomain
  , universalRegDomain
  , emptyRegDomain
  , nontrivialRegs
  , regDomainFromList
  ) where

import           Control.Lens ( (.~), (&) )
import           Data.Functor.Const
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableF as TF

import qualified What4.Interface as WI

import qualified Data.Macaw.CFG as MM

import qualified Pate.Solver as PS
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.ExprMappable as PEM
import qualified Pate.Register.Traversal as PRt

---------------------------------------------
-- Equivalence domain

-- | The domain of an equivalence problem: representing the state that is either
-- assumed (in a pre-domain) or proven (in a post-domain) to be equivalent.
data EquivalenceDomain sym arch where
  EquivalenceDomain ::
    { -- | Each register is considered to be in this domain if the given predicate is true.
      eqDomainRegisters :: RegisterDomain sym arch
      -- | The memory domain that is specific to stack variables.
    , eqDomainStackMemory :: PEM.MemoryDomain sym arch
      -- | The memory domain that is specific to non-stack (i.e. global) variables.
    , eqDomainGlobalMemory :: PEM.MemoryDomain sym arch
    }  -> EquivalenceDomain sym arch

type RegisterDomain sym arch = MM.RegState (MM.ArchReg arch) (Const (WI.Pred sym))

-- | Register domain that contains all registers
universalRegDomain ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  sym ->
  RegisterDomain sym arch
universalRegDomain sym = MM.mkRegState (\_ -> Const (WI.truePred sym))

-- | Register domain that contains no registers
emptyRegDomain ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  sym ->
  RegisterDomain sym arch
emptyRegDomain sym = MM.mkRegState (\_ -> Const (WI.falsePred sym))

regDomainFromList ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  WI.IsExprBuilder sym =>
  sym ->
  [(Some (MM.ArchReg arch), WI.Pred sym)] ->
  RegisterDomain sym arch
regDomainFromList sym = foldr (\(Some r, p) regs -> regs & (MM.boundValue r) .~ (Const p)) (emptyRegDomain sym)


nontrivialRegs ::
  forall sym arch.
  MM.RegisterInfo (MM.ArchReg arch) =>
  PS.ValidSym sym =>
  sym ->
  RegisterDomain sym arch ->
  [WI.Pred sym]
nontrivialRegs _sym regs = PRt.collapse (TF.fmapF go regs)
  where
    go :: Const (WI.Pred sym) t -> Const ([WI.Pred sym]) t
    go (Const p) = case WI.asConstantPred p of
      Just False -> Const []
      _ -> Const [p]

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
    regs <- PRt.zipWithRegStatesM (eqDomainRegisters domT) (eqDomainRegisters domF)
      (\_ (Const pT) (Const pF) -> Const <$> WI.baseTypeIte sym p pT pF)
    stack <- PEM.mux sym p (eqDomainStackMemory domT) (eqDomainStackMemory domF)
    mem <- PEM.mux sym p (eqDomainGlobalMemory domT) (eqDomainGlobalMemory domF)
    return $ EquivalenceDomain regs stack mem

registerInDomain ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  MM.ArchReg arch tp ->
  EquivalenceDomain sym arch ->
  WI.Pred sym
registerInDomain reg eqDom = getConst $ MM.getBoundValue reg (eqDomainRegisters eqDom)

empty :: (MM.RegisterInfo (MM.ArchReg arch), PS.ValidSym sym) => sym -> EquivalenceDomain sym arch
empty sym = EquivalenceDomain (emptyRegDomain sym) (PEM.empty sym) (PEM.empty sym)


instance PEM.ExprMappable sym (EquivalenceDomain sym arch) where
  mapExpr sym f stPred = do
    regs <- TF.traverseF (\(Const p) -> Const <$> f p) (eqDomainRegisters stPred)
    stack <- PEM.mapExpr sym f (eqDomainStackMemory stPred)
    mem <- PEM.mapExpr sym f (eqDomainGlobalMemory stPred)
    return $ EquivalenceDomain regs stack mem
