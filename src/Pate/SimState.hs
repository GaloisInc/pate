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
  , specMapList
  , attachSpec
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
  , flatVars
  -- assumption frames
  , AssumptionFrame(..)
  , isAssumedPred
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

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.TraversableF as TF

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
import qualified Data.Parameterized.SetF as SetF

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
simInMem = simMem . simInState

simInRegs ::
  SimInput sym arch bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
simInRegs = simRegs . simInState


data SimOutput sym arch bin = SimOutput
  {
    simOutState :: SimState sym arch bin
  , simOutBlockEnd :: CS.RegValue sym (MS.MacawBlockEndType arch)
  }

simOutMem ::
  SimOutput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simOutMem = simMem . simOutState

simOutRegs ::
  SimOutput sym arch bin -> MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
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

rebindExpr ::
  forall sym t st fs ctx tp.
  ( sym ~ W4B.ExprBuilder t st fs )
  => sym
  -> Ctx.Assignment (VarBinding sym) ctx
  -> W4.SymExpr sym tp
  -> IO (W4.SymExpr sym tp)
rebindExpr sym bindings expr =
  rebindWithFrame sym frame expr
  where
    frame = AssumptionFrame { asmPreds = mempty
                            , asmBinds = TFC.foldrFC addSingletonBinding MapF.empty bindings
                            }
    addSingletonBinding varBinding =
      MapF.insert (bindVar varBinding) (SetF.singleton (bindVal varBinding))

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
    go e = W4B.idxCacheEval cache e $ do
      W4.setCurrentProgramLoc sym (W4B.exprLoc e)
      case getUniqueBinding sym asm e of
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
    specVars :: PT.PatchPair (SimVars sym arch)
  , specAsm :: W4.Pred sym
  , specBody :: f
  }


specVarsO :: SimSpec sym arch f -> SimVars sym arch PT.Original
specVarsO spec = PT.pOriginal $ specVars spec

specVarsP :: SimSpec sym arch f -> SimVars sym arch PT.Patched
specVarsP spec = PT.pPatched $ specVars spec

instance PEM.ExprMappable sym f => PEM.ExprMappable sym (SimSpec sym arch f) where
  mapExpr sym f spec = do
    -- it's not really obvious how to map the bound variables in general
    -- we're going to leave it up the clients to not clobber any relevant bindings
    --specVarsO' <- PEM.mapExpr sym f (specVarsO spec)
    --specVarsP' <- PEM.mapExpr sym f (specVarsP spec)
    specAsm' <- f (specAsm spec)
    specBody' <- PEM.mapExpr sym f (specBody spec)
    return $ SimSpec (specVars spec) specAsm' specBody'

instance Functor (SimSpec sym arch) where
  fmap f spec = spec { specBody = f (specBody spec) }

attachSpec :: SimSpec sym arch f -> g -> SimSpec sym arch g
attachSpec spec g = spec { specBody = g }

specMapList :: (f -> [g]) -> SimSpec sym arch f -> [SimSpec sym arch g]
specMapList f spec = map (\bodyelem -> spec { specBody = bodyelem} ) (f (specBody spec))

-- | The symbolic inputs and outputs of an original vs. patched block slice.
data SimBundle sym arch = SimBundle
  {
    simIn :: PT.PatchPair (SimInput sym arch)
  , simOut :: PT.PatchPair (SimOutput sym arch)
  }

simInO :: SimBundle sym arch -> SimInput sym arch PT.Original
simInO = PT.pOriginal . simIn

simInP :: SimBundle sym arch -> SimInput sym arch PT.Patched
simInP = PT.pPatched . simIn

simOutO :: SimBundle sym arch -> SimOutput sym arch PT.Original
simOutO = PT.pOriginal . simOut

simOutP :: SimBundle sym arch -> SimOutput sym arch PT.Patched
simOutP = PT.pPatched . simOut


simPair :: SimBundle sym arch -> PT.BlockPair arch
simPair bundle = TF.fmapF simInBlock (simIn bundle)

---------------------------------------
-- Variable binding

data SimVars sym arch bin = SimVars
  {
    simVarMem :: MT.MemTraceVar sym (MM.ArchAddrWidth arch)
  , simVarRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegVar sym)
  , simVarState :: SimState sym arch bin
  }

flatVars ::
  SimVars sym arch bin -> [Some (W4.SymExpr sym)]
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
  MM.RegisterInfo (MM.ArchReg arch) =>
  W4.IsExprBuilder sym =>
  sym ->
  SimVars sym arch bin ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  IO [Some (VarBinding sym)]
flatVarBinds sym simVars mem regs = do
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
        iRegion <- W4.natToInteger sym region
        return $ [Some (VarBinding regVar iRegion), Some (VarBinding offVar off)]
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
  mapExpr sym f (SimState mem regs) = SimState
    <$> PEM.mapExpr sym f mem
    <*> MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) regs

instance PEM.ExprMappable sym (SimInput sym arch bin) where
  mapExpr sym f (SimInput st blk) = SimInput
    <$> PEM.mapExpr sym f st
    <*> return blk

instance PEM.ExprMappable sym (SimOutput sym arch bin) where
  mapExpr sym f (SimOutput out blkend) = SimOutput
    <$> PEM.mapExpr sym f out
    <*> PEM.mapExpr sym f blkend

instance PEM.ExprMappable sym (SimBundle sym arch) where
  mapExpr sym f (SimBundle in_ out) = SimBundle
    <$> PEM.mapExpr sym f in_
    <*> PEM.mapExpr sym f out
