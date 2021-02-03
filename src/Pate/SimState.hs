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
  , SimSpec(..)
  , specMap
  , specMapList
  , attachSpec
  , SimBundle(..)
  , simInMem
  , simInRegs
  , simOutMem
  , simOutRegs
  , simPair
  -- variable binding
  , SimVars(..)
  , bindSpec
  , flatVars
  -- assumption frames
  , AssumptionFrame
  , exprBinding
  , macawRegBinding
  , frameAssume
  , getAssumedPred
  , rebindExpr
  , rebindWithFrame
  , rebindWithFrame'
  ) where

import           GHC.Stack ( HasCallStack )

import           Control.Monad ( forM )
import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT
import           What4.ExprHelpers

------------------------------------
-- Crucible inputs and outputs

data SimState sym arch (bin :: PT.WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
  }

data SimInput sym arch bin = SimInput
  {
    simInState :: SimState sym arch bin
  , simInBlock :: PT.ConcreteBlock arch bin
  }


simInMem ::
  SimInput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simInMem simIn = simMem $ simInState simIn

simInRegs ::
  SimInput sym arch bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
simInRegs simIn = simRegs $ simInState simIn


data SimOutput sym arch bin = SimOutput
  {
    simOutState :: SimState sym arch bin
  , simOutBlockEnd :: CS.RegValue sym (MS.MacawBlockEndType arch)
  }

simOutMem ::
  SimOutput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simOutMem simIn = simMem $ simOutState simIn

simOutRegs ::
  SimOutput sym arch bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
simOutRegs simIn = simRegs $ simOutState simIn


newtype ExprSet sym tp where
  ExprSet :: Set (AsOrd (W4.SymExpr sym) tp) -> ExprSet sym tp

data AsOrd f tp where
  AsOrd :: OrdF f => { unAsOrd :: f tp } -> AsOrd f tp

instance Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) = case compareF a b of
    EQF -> True
    _ -> False

instance Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

deriving instance Semigroup (ExprSet sym tp)
deriving instance Monoid (ExprSet sym tp)

singletonExpr :: OrdF (W4.SymExpr sym) => W4.SymExpr sym tp -> ExprSet sym tp
singletonExpr e = ExprSet (Set.singleton (AsOrd e))


data AssumptionFrame sym where
  AssumptionFrame ::
    { asmPreds :: [W4.Pred sym]
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

exprBinding ::
  W4.IsSymExprBuilder sym =>
  -- | source expression
  W4.SymExpr sym tp ->
  -- | target expression
  W4.SymExpr sym tp ->
  AssumptionFrame sym
exprBinding eSrc eTgt = case testEquality eSrc eTgt of
  Just Refl -> mempty
  _ -> mempty { asmBinds = (MapF.singleton eSrc (singletonExpr eTgt)) }

macawRegBinding ::
  W4.IsSymExprBuilder sym =>
  MS.ToCrucibleType tp ~ MS.ToCrucibleType tp' =>
  -- | value to rebind
  PSR.MacawRegEntry sym tp ->
  -- | new value
  PSR.MacawRegEntry sym tp' ->
  AssumptionFrame sym
macawRegBinding var val = do
  case PSR.macawRegRepr var of
    CLM.LLVMPointerRepr _ ->
      let
        CLM.LLVMPointer regVar offVar = PSR.macawRegValue var
        CLM.LLVMPointer regVal offVal = PSR.macawRegValue val
        regBind = exprBinding regVar regVal
        offBind = exprBinding offVar offVal
      in regBind <> offBind
    CT.BoolRepr -> exprBinding (PSR.macawRegValue var) (PSR.macawRegValue val)
    _ -> mempty

frameAssume ::
  W4.Pred sym ->
  AssumptionFrame sym
frameAssume p = AssumptionFrame [p] MapF.empty

getUniqueBinding ::
  W4.IsSymExprBuilder sym =>
  AssumptionFrame sym ->
  W4.SymExpr sym tp ->
  Maybe (W4.SymExpr sym tp)
getUniqueBinding asm e = case MapF.lookup e (asmBinds asm) of
  Just (ExprSet es)
    | Set.size es == 1
    , [AsOrd e'] <- Set.toList es -> Just e'
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
  allPreds sym ((asmPreds asm) ++ bindsAsm)
  where
    assumeBinds :: MapF.Pair (W4.SymExpr sym) (ExprSet sym) -> IO [W4.Pred sym]
    assumeBinds (MapF.Pair eSrc (ExprSet eTgts)) = do
      let eTgts' = map unAsOrd (Set.toList eTgts)
      forM eTgts' $ \eTgt -> W4.isEq sym eSrc eTgt

rebindExpr
  :: ( sym ~ W4B.ExprBuilder t st fs )
  => sym
  -> Ctx.Assignment (VarBinding sym) ctx
  -> W4.SymExpr sym tp
  -> IO (W4.SymExpr sym tp)
rebindExpr sym bindings expr =
  rebindWithFrame sym frame expr
  where
    frame = AssumptionFrame { asmPreds = []
                            , asmBinds = TFC.foldrFC addSingletonBinding MapF.empty bindings
                            }
    addSingletonBinding varBinding =
      MapF.insert (W4.varExpr sym (bindVar varBinding)) (singletonExpr (bindVal varBinding))

-- | Explicitly rebind any known sub-expressions that are in the frame.
rebindWithFrame ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  AssumptionFrame sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame sym asm e = do
  cache <- W4B.newIdxCache
  rebindWithFrame' sym cache asm e

rebindWithFrame' ::
  forall sym t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  AssumptionFrame sym ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame' sym cache asm e_outer = do
  let
    go :: forall tp'. W4B.Expr t tp' -> IO (W4B.Expr t tp')
    go e = W4B.idxCacheEval cache e $ case getUniqueBinding asm e of
      Just e' -> return e'
      _ -> case e of
        -- fixing a common trivial mux case
        W4B.AppExpr a0
          | (W4B.BaseIte _ _ cond eT eF) <- W4B.appExprApp a0
          , Just (W4B.BaseEq _ eT' eF') <- W4B.asApp cond
          , Just W4.Refl <- W4.testEquality eT eT'
          , Just W4.Refl <- W4.testEquality eF eF'
          -> go eF
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else W4B.sbMakeExpr sym a0'
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else W4B.sbNonceExpr sym a0'
        _ -> return e
  go e_outer

data SimSpec sym arch f = SimSpec
  {
    specVarsO :: SimVars sym arch PT.Original
  , specVarsP :: SimVars sym arch PT.Patched
  , specAsm :: W4.Pred sym
  , specBody :: f
  }

instance PEM.ExprMappable sym f => PEM.ExprMappable sym (SimSpec sym arch f) where
  mapExpr sym f spec = do
    -- it's not really obvious how to map the bound variables in general
    -- we're going to leave it up the clients to not clobber any relevant bindings
    --specVarsO' <- PEM.mapExpr sym f (specVarsO spec)
    --specVarsP' <- PEM.mapExpr sym f (specVarsP spec)
    specAsm' <- f (specAsm spec)
    specBody' <- PEM.mapExpr sym f (specBody spec)
    return $ SimSpec (specVarsO spec) (specVarsP spec) specAsm' specBody'

specMap :: (f -> g) -> SimSpec sym arch f -> SimSpec sym arch g
specMap f spec = spec { specBody = f (specBody spec) }

attachSpec :: SimSpec sym arch f -> g -> SimSpec sym arch g
attachSpec spec g = spec { specBody = g }

specMapList :: (f -> [g]) -> SimSpec sym arch f -> [SimSpec sym arch g]
specMapList f spec = map (\bodyelem -> spec { specBody = bodyelem} ) (f (specBody spec))

data SimBundle sym arch = SimBundle
  {
    simInO :: SimInput sym arch PT.Original
  , simInP :: SimInput sym arch PT.Patched
  , simOutO :: SimOutput sym arch PT.Original
  , simOutP :: SimOutput sym arch PT.Patched
  }

simPair :: SimBundle sym arch -> PT.PatchPair arch
simPair bundle = PT.PatchPair (simInBlock $ simInO bundle) (simInBlock $ simInP bundle)

---------------------------------------
-- Variable binding

data SimVars sym arch bin = SimVars
  {
    simVarMem :: MT.MemTraceVar sym (MM.ArchAddrWidth arch)
  , simVarRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegVar sym)
  , simVarState :: SimState sym arch bin
  }

flatVars ::
  SimVars sym arch bin -> [Some (W4.BoundVar sym)]
flatVars simVars =
  let
    regVarPairs =
      MapF.toList $
      MM.regStateMap $
      (simVarRegs simVars)
    regVars = concat $ map (\(MapF.Pair _ (PSR.MacawRegVar _ vars)) -> TFC.toListFC Some vars) regVarPairs
    MT.MemTraceVar memVar = simVarMem simVars
  in ((Some memVar):regVars)

flatVarBinds ::
  forall sym arch bin.
  HasCallStack =>
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimVars sym arch bin ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  IO [Some (VarBinding sym)]
flatVarBinds _sym simVars mem regs = do
  let
    regBinds =
      MapF.toList $
      MM.regStateMap $
      MM.zipWithRegState (\(PSR.MacawRegVar _ vars) val -> PSR.MacawRegVar val vars) (simVarRegs simVars) regs
  regVarBinds <- fmap concat $ forM regBinds $ \(MapF.Pair _ (PSR.MacawRegVar val vars)) -> do
    case PSR.macawRegRepr val of
      CLM.LLVMPointerRepr{} -> do
        CLM.LLVMPointer region off <- return $ PSR.macawRegValue val
        (Ctx.Empty Ctx.:> regVar Ctx.:> offVar) <- return $ vars
        return $ [Some (VarBinding regVar region), Some (VarBinding offVar off)]
      CT.BoolRepr -> do
        Ctx.Empty Ctx.:> var <- return vars
        return [Some (VarBinding var (PSR.macawRegValue val))]
      CT.StructRepr Ctx.Empty -> return []
      repr -> error ("flatVarBinds: unsupported type " ++ show repr)

  MT.MemTraceVar memVar <- return $ simVarMem simVars
  let memBind = VarBinding memVar (MT.memArr mem)   
  return $ ((Some memBind):regVarBinds)


bindSpec ::
  PEM.ExprMappable sym f =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym -> 
  SimState sym arch PT.Original ->
  SimState sym arch PT.Patched ->
  SimSpec sym arch f ->
  IO (W4.Pred sym, f)
bindSpec sym stO stP spec = do
  flatO <- flatVarBinds sym (specVarsO spec) (simMem stO) (simRegs stO)
  flatP <- flatVarBinds sym (specVarsP spec) (simMem stP) (simRegs stP)
  Some flatCtx <- return $ Ctx.fromList (flatO ++ flatP)
  body <- PEM.mapExpr sym (rebindExpr sym flatCtx) (specBody spec)
  asm <- rebindExpr sym flatCtx (specAsm spec)
  return $ (asm, body)

------------------------------------
-- ExprMappable instances

instance PEM.ExprMappable sym (SimState sym arch bin) where
  mapExpr sym f st = do
    simMem' <- PEM.mapExpr sym f $ simMem st
    simRegs' <- MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) $ simRegs st
    return $ SimState simMem' simRegs'

instance PEM.ExprMappable sym (SimInput sym arch bin) where
  mapExpr sym f simIn = do
    st <- PEM.mapExpr sym f (simInState simIn)
    return $ SimInput { simInState = st, simInBlock = (simInBlock simIn) }

instance PEM.ExprMappable sym (SimOutput sym arch bin) where
  mapExpr sym f simOut = do
    st <- PEM.mapExpr sym f (simOutState simOut)
    blend <- PEM.mapExpr sym f (simOutBlockEnd simOut)
    return $ SimOutput { simOutState = st, simOutBlockEnd = blend }

instance PEM.ExprMappable sym (SimBundle sym arch) where
  mapExpr sym f bundle = do
    simInO' <- PEM.mapExpr sym f $ simInO bundle
    simInP' <- PEM.mapExpr sym f $ simInP bundle
    simOutO' <- PEM.mapExpr sym f $ simOutO bundle
    simOutP' <- PEM.mapExpr sym f $ simOutP bundle
    return $ SimBundle simInO' simInP' simOutO' simOutP'

