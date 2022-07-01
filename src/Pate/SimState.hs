{-|
Module           : Pate.SimState
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Functionality for handling the inputs and outputs of crucible.
-}

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
{-# LANGUAGE LambdaCase #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}


module Pate.SimState
  ( -- simulator state
    SimState(..)
  , SimInput(..)
  , SimOutput(..)
  , type VarScope
  , Scoped(..)
  , SimSpec(..)
  , forSpec
  , viewSpec
  , viewSpecBody
  , unsafeCoerceSpecBody
  , SimBundle(..)
  , simInMem
  , simInRegs
  , simOutMem
  , simOutRegs
  , simPair
  , simInO
  , simInP
  , simOutO
  , simOutP
  -- variable binding
  , SimVars(..)
  , bindSpec
  -- assumption frames
  , AssumptionFrame(..)
  , isAssumedPred
  , exprBinding
  , bindingToFrame
  , macawRegBinding
  , frameAssume
  , getAssumedPred
  , rebindWithFrame
  , rebindWithFrame'
  , bundleOutVars
  ) where

import           GHC.Stack ( HasCallStack )
import qualified Data.Kind as DK

import           Control.Monad ( forM )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( Pair(..) )
import qualified Data.Parameterized.TraversableF as TF

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.PatchPair as PPa
import qualified Pate.SimulatorRegisters as PSR
import           What4.ExprHelpers
import qualified Data.Parameterized.SetF as SetF

------------------------------------
-- Crucible inputs and outputs

data VarScope

data SimState sym arch (v :: VarScope) (bin :: PBi.WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
  }

data SimInput sym arch v bin = SimInput
  {
    simInState :: SimState sym arch v bin
  , simInBlock :: PB.ConcreteBlock arch bin
  }


simInMem ::
  SimInput sym arch v bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simInMem = simMem . simInState

simInRegs ::
  SimInput sym arch v bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
simInRegs = simRegs . simInState


data SimOutput sym arch v bin = SimOutput
  {
    simOutState :: SimState sym arch v bin
  , simOutBlockEnd :: CS.RegValue sym (MCS.MacawBlockEndType arch)
  }

simOutMem ::
  SimOutput sym arch v bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simOutMem = simMem . simOutState

simOutRegs ::
  SimOutput sym arch v bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
simOutRegs = simRegs . simOutState




data AssumptionFrame sym where
  AssumptionFrame ::
    { asmPreds :: ExprSet sym W4.BaseBoolType
    -- | equivalence on sub-expressions. In the common case where an expression maps
    -- to a single expression (i.e. a singleton 'ExprSet') we can apply the rewrite
    -- inline.
    , asmBinds :: MapF.MapF (W4.SymExpr sym) (ExprSet sym)
    } -> AssumptionFrame sym

instance OrdF (W4.SymExpr sym) => Semigroup (AssumptionFrame sym) where
  asm1 <> asm2 = let
    preds = (asmPreds asm1) <> (asmPreds asm2)
    binds =
      MapF.mergeWithKey
        (\_ eset1 eset2 -> Just (eset1 <> eset2))
        id
        id
        (asmBinds asm1)
        (asmBinds asm2)
    in AssumptionFrame preds binds

instance OrdF (W4.SymExpr sym) => Monoid (AssumptionFrame sym) where
  mempty = AssumptionFrame mempty MapF.empty

-- | Lift an expression binding environment into an assumption frame
bindingToFrame ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  ExprBindings sym ->
  AssumptionFrame sym
bindingToFrame binds = AssumptionFrame { asmPreds = mempty, asmBinds = MapF.map SetF.singleton binds }

exprBinding ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  -- | source expression
  W4.SymExpr sym tp ->
  -- | target expression
  W4.SymExpr sym tp ->
  AssumptionFrame sym
exprBinding eSrc eTgt = case testEquality eSrc eTgt of
  Just Refl -> mempty
  _ -> mempty { asmBinds = (MapF.singleton eSrc (SetF.singleton eTgt)) }

macawRegBinding ::
  W4.IsSymExprBuilder sym =>
  MS.ToCrucibleType tp ~ MS.ToCrucibleType tp' =>
  sym ->
  -- | value to rebind
  PSR.MacawRegEntry sym tp ->
  -- | new value
  PSR.MacawRegEntry sym tp' ->
  IO (AssumptionFrame sym)
macawRegBinding sym var val = do
  case PSR.macawRegRepr var of
    CLM.LLVMPointerRepr _ -> do
      let CLM.LLVMPointer regVar offVar = PSR.macawRegValue var
      let CLM.LLVMPointer regVal offVal = PSR.macawRegValue val
      iRegVar <- W4.natToInteger sym regVar
      iRegVal <- W4.natToInteger sym regVal
      let regBind = exprBinding iRegVar iRegVal
      let offBind = exprBinding offVar offVal
      return (regBind <> offBind)
    CT.BoolRepr -> return $ exprBinding (PSR.macawRegValue var) (PSR.macawRegValue val)
    _ -> return mempty

frameAssume ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  W4.Pred sym ->
  AssumptionFrame sym
frameAssume p = AssumptionFrame (SetF.singleton p) MapF.empty

getUniqueBinding ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  AssumptionFrame sym ->
  W4.SymExpr sym tp ->
  Maybe (W4.SymExpr sym tp)
getUniqueBinding sym asm e = case MapF.lookup e (asmBinds asm) of
  Just es
    | SetF.size es == 1
    , [e'] <- SetF.toList es -> Just e'
  _ -> case W4.exprType e of
    W4.BaseBoolRepr | isAssumedPred asm e -> Just $ W4.truePred sym
    _ -> Nothing

-- | Compute a predicate that collects the individual assumptions in the frame, including
-- equality on all bindings.
getAssumedPred ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  sym ->
  AssumptionFrame sym ->
  IO (W4.Pred sym)
getAssumedPred sym asm = do
  bindsAsm <- fmap concat $ mapM assumeBinds (MapF.toList (asmBinds asm))
  let predList = SetF.toList $ (asmPreds asm) <> (SetF.fromList bindsAsm)
  allPreds sym predList
  where
    assumeBinds :: MapF.Pair (W4.SymExpr sym) (ExprSet sym) -> IO [W4.Pred sym]
    assumeBinds (MapF.Pair eSrc eTgts) = forM (SetF.toList eTgts) $ \eTgt ->
      W4.isEq sym eSrc eTgt

isAssumedPred ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  AssumptionFrame sym ->
  W4.Pred sym ->
  Bool
isAssumedPred frame asm = SetF.member asm (asmPreds frame)

-- | Explicitly rebind any known sub-expressions that are in the frame.
rebindWithFrame ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  AssumptionFrame sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame sym asm e = do
  cache <- freshVarBindCache
  rebindWithFrame' sym cache asm e

rebindWithFrame' ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  VarBindCache sym ->
  AssumptionFrame sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame' sym cache asm = rewriteSubExprs' sym cache (getUniqueBinding sym asm)


-- | Proof that the interpretation of 'f' is independent of the scope variable.
-- This is necessary since we do want to convert between scopes as a result of binding.
class Scoped f where
  unsafeCoerceScope :: forall v v'. f v -> f v'

data SimSpec sym arch (f :: VarScope -> DK.Type) where
  SimSpec :: forall sym arch f v.
    {
      specVars :: PPa.PatchPair (SimVars sym arch v)
    , specAsm :: W4.Pred sym
    , specBody :: f v
    } -> SimSpec sym arch f

-- | Project out the variables with an arbitrary scope
viewSpecVars ::
  SimSpec sym arch f ->
  (forall v. PPa.PatchPair (SimVars sym arch v) -> a) ->
  a
viewSpecVars (SimSpec vars _ _) f = f vars 

-- | Project out the body with an arbitrary scope
viewSpecBody ::
  SimSpec sym arch f ->
  (forall v. f v -> a) ->
  a
viewSpecBody (SimSpec _ _ body) f = f body

viewSpec ::
  SimSpec sym arch f ->
  (forall v. PPa.PatchPair (SimVars sym arch v) -> f v -> a) ->
  a
viewSpec (SimSpec vars _ body) f = f vars body

forSpec ::
  Applicative m =>
  SimSpec sym arch f ->
  (forall v. PPa.PatchPair (SimVars sym arch v) -> f v -> m (g v)) ->
  m (SimSpec sym arch g)
forSpec (SimSpec vars asm body) f = SimSpec <$> pure vars <*> pure asm <*> f vars body

-- | Unsafely coerce the body of a spec to have any scope.
-- After this is used, the variables in the resulting 'f' should
-- be rebound to actually be properly scoped to 'v'.
unsafeCoerceSpecBody ::
  Scoped f =>
  SimSpec sym arch f -> f v
unsafeCoerceSpecBody (SimSpec _ _ body) = unsafeCoerceScope body

-- | The symbolic inputs and outputs of an original vs. patched block slice.
data SimBundle sym arch v = SimBundle
  {
    simIn :: PPa.PatchPair (SimInput sym arch v)
  , simOut :: PPa.PatchPair (SimOutput sym arch v)
  }

bundleOutVars :: SimBundle sym arch v -> PPa.PatchPair (SimVars sym arch v)
bundleOutVars bundle = TF.fmapF (SimVars . simOutState) (simOut bundle)

simInO :: SimBundle sym arch v -> SimInput sym arch v PBi.Original
simInO = PPa.pOriginal . simIn

simInP :: SimBundle sym arch v -> SimInput sym arch v PBi.Patched
simInP = PPa.pPatched . simIn

simOutO :: SimBundle sym arch v -> SimOutput sym arch v PBi.Original
simOutO = PPa.pOriginal . simOut

simOutP :: SimBundle sym arch v -> SimOutput sym arch v PBi.Patched
simOutP = PPa.pPatched . simOut


simPair :: SimBundle sym arch v -> PPa.BlockPair arch
simPair bundle = TF.fmapF simInBlock (simIn bundle)

---------------------------------------
-- Variable binding


data SimVars sym arch v bin = SimVars
  {
    simVarState :: SimState sym arch v bin
  }

data MacawVarBind sym tp = MacawVarBind (PSR.MacawRegEntry sym tp) (PSR.MacawRegEntry sym tp)

mkVarBinds ::
  forall sym arch v bin.
  HasCallStack =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  SimVars sym arch v bin ->
  MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  IO (ExprBindings sym)
mkVarBinds sym simVars mem regs = do
  let
    memVar = MT.memState $ simMem $ simVarState simVars
    regVars = simRegs $ simVarState simVars
    regBinds =
      MapF.toList $
      MM.regStateMap $
      MM.zipWithRegState MacawVarBind regVars regs
  regVarBinds <- fmap concat $ forM regBinds $ \(MapF.Pair _r (MacawVarBind var val)) ->
     case PSR.macawRegRepr val of
       CLM.LLVMPointerRepr{} -> do
         CLM.LLVMPointer regionVar offVar <- return $ PSR.macawRegValue var
         CLM.LLVMPointer regionVal offVal <- return $ PSR.macawRegValue val
         regionVarI <- W4.natToInteger sym regionVar
         regionValI <- W4.natToInteger sym regionVal
         return $ [Pair regionVarI regionValI, Pair offVar offVal]
       CT.BoolRepr -> do
         boolVar <- return $ PSR.macawRegValue var
         boolVal <- return $ PSR.macawRegValue val
         return [Pair boolVar boolVal]
       CT.StructRepr Ctx.Empty -> return []
       repr -> error ("mkVarBinds: unsupported type " ++ show repr)
  mergeBindings sym (MT.mkMemoryBinding memVar mem) (MapF.fromList regVarBinds)

bindSpec ::
  forall sym arch s st fs f v.
  Scoped f =>
  PEM.ExprMappable sym (f v) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  PPa.PatchPair (SimVars sym arch v) ->
  SimSpec sym arch f ->
  IO (W4.Pred sym, f v)
bindSpec sym vals spec = do
  (bindsO, bindsP) <- PPa.forBinsC $ \get -> viewSpecVars spec $ \vars -> do
    let st = simVarState $ get vals
    mkVarBinds sym (get vars) (MT.memState $ simMem st) (simRegs st)
  binds <- mergeBindings sym bindsO bindsP
  cache <- freshVarBindCache
  let doRewrite = applyExprBindings' sym cache binds
  body <- PEM.mapExpr sym doRewrite (unsafeCoerceSpecBody spec)
  asm <- doRewrite (specAsm spec)
  return $ (asm, body)

------------------------------------
-- ExprMappable instances

instance PEM.ExprMappable sym (SimState sym arch v bin) where
  mapExpr sym f (SimState mem regs) = SimState
    <$> PEM.mapExpr sym f mem
    <*> MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) regs

instance PEM.ExprMappable sym (SimInput sym arch v bin) where
  mapExpr sym f (SimInput st blk) = SimInput
    <$> PEM.mapExpr sym f st
    <*> return blk

instance PEM.ExprMappable sym (SimOutput sym arch v bin) where
  mapExpr sym f (SimOutput out blkend) = SimOutput
    <$> PEM.mapExpr sym f out
    <*> PEM.mapExpr sym f blkend

instance PEM.ExprMappable sym (SimBundle sym arch v) where
  mapExpr sym f (SimBundle in_ out) = SimBundle
    <$> PEM.mapExpr sym f in_
    <*> PEM.mapExpr sym f out
