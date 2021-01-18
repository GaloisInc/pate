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
  ) where

import           GHC.Stack ( HasCallStack )

import           Control.Monad ( forM )

import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT

import qualified What4.Interface as W4

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


data SimSpec sym arch f = SimSpec
  {
    specVarsO :: SimVars sym arch PT.Original
  , specVarsP :: SimVars sym arch PT.Patched
  , specAsm :: W4.Pred sym
  , specBody :: f
  }



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
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
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

