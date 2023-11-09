{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE PolyKinds #-}

module Pate.Equivalence.Condition (
    EquivalenceCondition(..)
  , RegisterCondition(..)
  , EquivConditionSpec
  , trueRegCond
  , fromLocationTraversable
  , universal
  , toPred
  , mux
  , merge
  , weaken
  , falseEqCondition
  , mergeRegCond
  , weakenRegCond
  ) where

import           Control.Lens ( (^.), (&), (.~) )
import qualified Control.Monad.IO.Class as IO
import           Data.Parameterized.Classes
import           Data.Functor.Const
import           Data.Parameterized.Some ( Some(..) )
import qualified What4.Interface as W4

import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as MM


import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.SimState as PS
import qualified Pate.Register.Traversal as PRt
import qualified Pate.Location as PL
import qualified What4.PredMap as WPM

import           Pate.TraceTree
import qualified Data.Kind as DK
import Control.Monad.Identity
import Pate.Equivalence.Error (SomeExpr, printSomeExprTruncated)
---------------------------------------------
-- Equivalence Condition

type EquivConditionSpec sym arch = PS.SimSpec sym arch (EquivalenceCondition sym arch)


mux ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m => 
  sym ->
  W4.Pred sym ->
  EquivalenceCondition sym arch v ->
  EquivalenceCondition sym arch v ->
  m (EquivalenceCondition sym arch v)
mux sym p condT condF = do
  mem <- WPM.mux sym p (eqCondMem condT) (eqCondMem condF)
  regs <- muxRegCond sym p (eqCondRegs condT) (eqCondRegs condF)
  let (PAS.NamedAsms mrT, PAS.NamedAsms mrF) = (eqCondMaxRegion condT, eqCondMaxRegion condF)
  mrCond <- PAS.NamedAsms <$> PAS.mux sym p mrT mrF
  let (PAS.NamedAsms pcT, PAS.NamedAsms pcF) = (eqCondExtraCond condT, eqCondExtraCond condF)
  pcond <- PAS.NamedAsms <$> PAS.mux sym p pcT pcF
  return $ EquivalenceCondition mem regs mrCond pcond

merge ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m => 
  sym ->
  EquivalenceCondition sym arch v ->
  EquivalenceCondition sym arch v ->
  m (EquivalenceCondition sym arch v)  
merge sym cond1 cond2 = do
  mem <- WPM.merge sym (eqCondMem cond1) (eqCondMem cond2)
  let regs = mergeRegCond (eqCondRegs cond1) (eqCondRegs cond2)
  let (PAS.NamedAsms mr1, PAS.NamedAsms mr2) = (eqCondMaxRegion cond1, eqCondMaxRegion cond2)
  let mrCond = PAS.NamedAsms $ mr1 <> mr2
  let (PAS.NamedAsms pc1, PAS.NamedAsms pc2) = (eqCondExtraCond cond1, eqCondExtraCond cond2)
  let pcond = PAS.NamedAsms $ pc1 <> pc2
  return $ EquivalenceCondition mem regs mrCond pcond


weaken ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m => 
  sym ->
  W4.Pred sym ->
  EquivalenceCondition sym arch v ->
  m (EquivalenceCondition sym arch v)  
weaken sym p cond = do
  mem <- WPM.weaken sym p (eqCondMem cond)
  regs <- weakenRegCond sym p (eqCondRegs cond)
  let (PAS.NamedAsms mr) = (eqCondMaxRegion cond)
  mrCond <- PAS.NamedAsms <$> PAS.weaken sym p mr
  let (PAS.NamedAsms pc) = (eqCondExtraCond cond)
  pcond <- PAS.NamedAsms <$> PAS.weaken sym p pc
  return $ EquivalenceCondition mem regs mrCond pcond

-- | Preconditions for graph nodes. These represent additional conditions
--   that must be true for the equivalence domain of the node to be considered
--   valid. Some of these conditions may be provable (i.e. all preceeding nodes
--   satisfy the condition), and some may require additional conditions to be
--   propagated.
data EquivalenceCondition sym arch (v :: PS.VarScope) =
    EquivalenceCondition
      { eqCondMem :: PMC.MemCellPred sym arch WPM.PredConjT
      , eqCondRegs :: RegisterCondition sym arch v
      , eqCondMaxRegion :: PAS.NamedAsms sym "maxRegion"
      , eqCondExtraCond :: PAS.NamedAsms sym "extraCond"
      -- ^ additional conditions
      }

falseEqCondition :: 
  W4.IsSymExprBuilder sym => 
  PA.ValidArch arch =>
  sym -> 
  EquivalenceCondition sym arch v
falseEqCondition sym = (universal sym) { eqCondExtraCond = PAS.NamedAsms $ PAS.fromPred (W4.falsePred sym)}

instance PEM.ExprMappable sym (EquivalenceCondition sym arch v) where
  mapExpr sym f (EquivalenceCondition a b c d) = EquivalenceCondition
    <$> PEM.mapExpr sym f a
    <*> PEM.mapExpr sym f b
    <*> PEM.mapExpr sym f c
    <*> PEM.mapExpr sym f d

instance PS.Scoped (EquivalenceCondition sym arch) where
  unsafeCoerceScope (EquivalenceCondition a b c d) = EquivalenceCondition a (PS.unsafeCoerceScope b) c d

instance (W4.IsSymExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationTraversable sym arch (EquivalenceCondition sym arch v) where
  traverseLocation sym cond f = PL.witherLocation sym cond (\loc p -> Just <$> f loc p)

instance (W4.IsSymExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationWitherable sym arch (EquivalenceCondition sym arch v) where
  witherLocation sym (EquivalenceCondition a b c d) f = 
    EquivalenceCondition 
    <$> PL.witherLocation sym a f 
    <*> PL.witherLocation sym b f
    <*> PL.witherLocation sym c f
    <*> PL.witherLocation sym d f

instance forall sym arch. IsTraceNode '(sym :: DK.Type,arch :: DK.Type) "eqcond" where
  type TraceNodeType '(sym,arch) "eqcond" = Some (EquivalenceCondition sym arch)
  -- cludge until we have a proper pretty printer
  type TraceNodeLabel "eqcond" = SomeExpr W4.BaseBoolType
  prettyNode someExpr (Some eqCond) = case eqCond of
    EquivalenceCondition{} -> PP.pretty someExpr
  nodeTags = [(Summary, \someExpr _ -> printSomeExprTruncated someExpr )
             ,(Simplified, \someExpr _ -> printSomeExprTruncated someExpr)
             ,(JSONTrace, \someExpr _ -> printSomeExprTruncated someExpr)
             ]
  jsonNode someExpr _ = 
    JSON.object 
      [ "trace_node_kind" JSON..= "eqcond"
      , "trace_node" JSON..= show (PP.pretty someExpr)
      ]

-- | A mapping from registers to a predicate representing an equality condition for
-- that specific register.
-- The conjunction of these predicates represents the assumption (as a precondition)
-- or assertion (as a postcondition) that all of the registers are equal with respect
-- to some equivalence domain.
-- FIXME: abstract this
newtype RegisterCondition sym arch (v :: PS.VarScope) =
  RegisterCondition { regCondPreds :: MM.RegState (MM.ArchReg arch) (Const (PAS.AssumptionSet sym)) }

muxRegCond ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m =>
  sym ->
  W4.Pred sym ->
  RegisterCondition sym arch v ->
  RegisterCondition sym arch v ->
  m (RegisterCondition sym arch v)  
muxRegCond sym p condT condF = do
  regCond <- PRt.zipWithRegStatesM (regCondPreds condT) (regCondPreds condF) $ \_ (Const asmT) (Const asmF) -> Const <$> PAS.mux sym p asmT asmF
  return $ RegisterCondition regCond

mergeRegCond ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  RegisterCondition sym arch v ->
  RegisterCondition sym arch v ->
  RegisterCondition sym arch v
mergeRegCond cond1 cond2 = runIdentity $ do
  regCond <- PRt.zipWithRegStatesM (regCondPreds cond1) (regCondPreds cond2) $ \_ (Const asm1) (Const asm2) -> Const <$> (return $ asm1 <> asm2)
  return $ RegisterCondition regCond

weakenRegCond ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m =>
  sym ->
  W4.Pred sym ->
  RegisterCondition sym arch v ->
  m (RegisterCondition sym arch v)
weakenRegCond sym p cond = IO.liftIO $ do
  regCond <- MM.traverseRegsWith (\_ (Const asm) -> Const <$> (PAS.weaken sym p asm)) (regCondPreds cond)
  return $ RegisterCondition regCond

instance PS.Scoped (RegisterCondition sym arch) where
  unsafeCoerceScope (RegisterCondition cond) = RegisterCondition cond

instance PEM.ExprMappable sym (RegisterCondition sym arch v) where
  mapExpr sym f (RegisterCondition cond) = RegisterCondition <$> MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) cond

trueRegCond ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  RegisterCondition sym arch v
trueRegCond _sym = RegisterCondition (MM.mkRegState (\_ -> mempty))

instance (MM.RegisterInfo (MM.ArchReg arch), W4.IsSymExprBuilder sym) => PL.LocationTraversable sym arch (RegisterCondition sym arch v) where
  traverseLocation sym body f = RegisterCondition <$>
    MM.traverseRegsWith (\r (Const asm) -> do
      p <- PAS.toPred sym asm
      f (PL.Location @"register" r) p >>= \ (_, p') -> return $ (Const (PAS.fromPred p'))
      ) (regCondPreds body)

instance (MM.RegisterInfo (MM.ArchReg arch), W4.IsSymExprBuilder sym) => PL.LocationWitherable sym arch (RegisterCondition sym arch v) where
  witherLocation sym body f = RegisterCondition <$>
    MM.traverseRegsWith (\r (Const asm) -> do
      p <- PAS.toPred sym asm
      f (PL.Location @"register" r) p >>= \case
        Just (_, p') -> return $ Const (PAS.fromPred p')
        Nothing -> return $ Const mempty
      ) (regCondPreds body)

-- | Domain that covers all of memory (i.e. no cells are excluded)
universal ::
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  EquivalenceCondition sym arch v
universal sym = EquivalenceCondition (WPM.empty WPM.PredConjRepr) (trueRegCond sym) mempty mempty


addCondition ::
  forall nm v k sym arch m.
  W4.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  PA.ValidArch arch =>
  sym -> 
  PL.Location sym arch nm (k :: PL.LocationK nm) ->
  W4.Pred sym ->
  EquivalenceCondition sym arch v ->
  m (EquivalenceCondition sym arch v)
addCondition sym l p cond = case l of
  PL.Register r  -> do
    let regPreds = regCondPreds (eqCondRegs cond)
    let Const asm = regPreds ^. MM.boundValue r
    
    let regPreds' = regPreds & (MM.boundValue r) .~ (Const (asm <> PAS.fromPred p))
    return $ cond { eqCondRegs = (RegisterCondition regPreds') }
  PL.Cell cell -> do
    let e = WPM.singleton WPM.PredConjRepr (Some cell) p
    memCond' <- IO.liftIO $ WPM.merge sym (eqCondMem cond) e
    return $ cond { eqCondMem = memCond' }
  PL.Named (PL.concreteSymbol @"maxRegion" -> Just Refl) -> do
    return $ cond { eqCondMaxRegion = (eqCondMaxRegion cond) <> (PAS.NamedAsms (PAS.fromPred p)) }
  PL.Named (PL.concreteSymbol @"extraCond" -> Just Refl) -> do
    return $ cond { eqCondExtraCond = (eqCondExtraCond cond) <> (PAS.NamedAsms (PAS.fromPred p)) }
  -- no support for stack base conditions
  PL.Named (PL.concreteSymbol @"stackBase" -> Just Refl) -> return $ cond
  _ -> IO.liftIO $ fail ("addCondition: unsupported location: " ++ PL.showLoc l)

toPred ::
  forall sym arch v m.
  W4.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  PA.ValidArch arch =>
  sym -> 
  EquivalenceCondition sym arch v ->
  m (W4.Pred sym)
toPred sym cond = PL.foldLocation @sym @arch sym cond (W4.truePred sym) (\cond_pred _loc p -> 
  IO.liftIO (W4.andPred sym cond_pred p))

fromLocationTraversable ::
  PL.LocationTraversable sym arch f =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IO.MonadIO m =>
  sym ->
  f ->
  (forall nm k. PL.Location sym arch nm k -> W4.Pred sym -> m (W4.Pred sym)) ->
  m (EquivalenceCondition sym arch v)
fromLocationTraversable sym a f = PL.foldLocation sym a (universal sym) (\cond loc p -> f loc p >>= \p' -> addCondition sym loc p' cond)
