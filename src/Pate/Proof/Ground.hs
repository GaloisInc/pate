{-|
Module           : Pate.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Presenting counter-examples to failed equivalence checks
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Proof.Ground 
  ( getInequivalenceResult
  , getCondEquivalenceResult
  , getPathCondition
  , groundMacawValue
  , groundProofTransformer
  , groundProofExpr
  ) where

import           GHC.Stack ( HasCallStack, callStack )

import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR

import qualified Data.Foldable as F
import           Data.Functor.Const ( Const(..) )
import           Data.Maybe (fromMaybe)
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import           Numeric.Natural ( Natural )

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.MuxTree as C

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Partial as W4P
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT
import           What4.ExprHelpers
import qualified What4.PathCondition as WPC

-- | Generate a structured counterexample for an equivalence
-- check from an SMT model.
-- Takes a symbolic 'PF.BlockSliceTransition' and grounds it according
-- to the model. Additionally, the given pre-domain and post-domains are
-- similarly grounded, so the counter-example contains which concrete locations
-- were assumed equivalent, and any concrete locations that are not equivalent
-- after the block slice transition.
getInequivalenceResult ::
  PEE.InequivalenceReason ->
  -- | pre-domain
  PF.ProofExpr (PFI.ProofSym sym arch) PF.ProofDomainType ->
  -- | post-domain
  PF.ProofExpr (PFI.ProofSym sym arch) PF.ProofDomainType ->
  -- | the transition that was attempted to be proven equivalent
  -- in the given domains
  PF.BlockSliceTransition (PFI.ProofSym sym arch) ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (PFI.InequivalenceResult arch)
getInequivalenceResult defaultReason pre post slice fn = do
  groundPre <- groundProofExpr fn pre
  groundPost <- groundProofExpr fn post
  gslice <- groundSlice fn slice
  let reason = fromMaybe defaultReason (getInequivalenceReason groundPost (PF.slBlockPostState gslice))
  return $ PFI.InequivalenceResult gslice groundPre groundPost reason


data Bindings sym tp where
  Bindings :: MapF.MapF (W4.SymExpr sym) W4G.GroundValueWrapper -> Bindings sym tp

instance OrdF (W4.SymExpr sym) => Semigroup (Bindings sym tp) where
  (Bindings m1) <> (Bindings m2) = Bindings $ MapF.mergeWithKey (\_ left _ -> Just left) id id m1 m2

instance OrdF (W4.SymExpr sym) => Monoid (Bindings sym tp) where
  mempty = Bindings MapF.empty

singleBinding ::
  W4.SymExpr sym tp ->
  SymGroundEvalFn sym ->
  EquivM sym arch (Bindings sym tp)
singleBinding e fn = do
  grnd <- execGroundFn fn e
  return $ Bindings $ MapF.singleton e (W4G.GVW grnd)

getCondEquivalenceResult ::
  forall sym arch.
  W4.Pred sym ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (PFI.CondEquivalenceResult sym arch)
getCondEquivalenceResult eqCond fn = withValid $ do
  cache <- W4B.newIdxCache
  let
    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Bindings sym tp2 -> EquivM sym arch (Bindings sym tp2)
    acc e binds = do
      Bindings binds' <- go e
      return $ binds <> (Bindings binds')

    go :: W4.SymExpr sym tp -> EquivM sym arch (Bindings sym tp)
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> case W4.exprType e of
        W4.BaseArrayRepr _ _ -> return mempty
        _ -> singleBinding e fn
      W4B.AppExpr a0 -> case W4B.appExprApp a0 of
        W4B.SelectArray _ _ idx -> do
          binds' <- singleBinding e fn
          binds'' <- TFC.foldrMFC acc mempty idx
          return $ binds' <> binds''
        app -> TFC.foldrMFC acc mempty app
      W4B.NonceAppExpr a0 -> TFC.foldrMFC acc mempty (W4B.nonceExprApp a0)
      _ -> return mempty
  Bindings binds <- go eqCond
  return $ PFI.CondEquivalenceResult { PFI.condEqExample = binds, PFI.condEqPred = eqCond }

getGenPathCondition ::
  forall sym  t st fs f.
  sym ~ W4B.ExprBuilder t st fs =>
  PEM.ExprMappable sym f =>
  sym ->
  W4G.GroundEvalFn t ->
  f ->
  IO (W4.Pred sym)
getGenPathCondition sym fn e = do
  let
    f :: forall tp'. W4.SymExpr sym tp' -> W4.Pred sym -> IO (W4.Pred sym)
    f e' cond = do
      cond' <- WPC.getPathCondition sym fn e'
      W4.andPred sym cond cond'
  
  PEM.foldExpr sym f e (W4.truePred sym)

traceBundle
  :: (HasCallStack)
  => SimBundle sym arch
  -> String
  -> EquivM sym arch ()
traceBundle bundle msg =
  emitEvent (PE.ProofTraceEvent callStack origAddr patchedAddr (T.pack msg))
  where
    origAddr = PB.concreteAddress (PS.simInBlock (PS.simInO bundle))
    patchedAddr = PB.concreteAddress (PS.simInBlock (PS.simInP bundle))

-- | Compute a domain that represents the path condition for
-- values which disagree in the given counter-example
getPathCondition ::
  forall sym arch.
  (MM.RegisterInfo (MM.ArchReg arch)) =>
  PS.SimBundle sym arch ->
  PF.BlockSliceState (PFI.ProofSym sym arch) ->
  PFI.SymDomain sym arch ->
  SymGroundEvalFn sym ->
  EquivM sym arch (PPa.PatchPairC (W4.Pred sym))
getPathCondition bundle slice dom fn = withSym $ \sym -> do
  groundDom <- groundProofExpr fn dom
  let
    getRegPath ::
      MM.ArchReg arch tp ->
      PF.BlockSliceRegOp (PFI.ProofSym sym arch) tp ->
      PPa.PatchPairC (W4.Pred sym) ->
      EquivM sym arch (PPa.PatchPairC (W4.Pred sym))
    getRegPath reg regOp paths = do
      case PFI.regInDomain groundDom reg of
        True -> do
          paths' <- withGroundEvalFn fn $ \fn' -> mapM (getGenPathCondition sym fn') (PF.slRegOpValues regOp)
          traceBundle bundle ("getPathCondition.getRegPath for " ++ showF reg)
          F.forM_ paths' $ \path' -> do
            traceBundle bundle ("  " ++ show (W4.printSymExpr path'))
          liftIO $ PPa.zipMPatchPairC paths paths' (W4.andPred sym)
        _ -> return paths

    getMemPath :: forall bin. PS.SimOutput sym arch bin -> EquivM sym arch (Const (W4.Pred sym) bin)
    getMemPath st = do
      let mem = MT.memArr $ PS.simOutMem st
      Const <$> (withGroundEvalFn fn $ \fn' -> getGenPathCondition sym fn' mem)

  let truePair = PPa.PatchPairC (W4.truePred sym) (W4.truePred sym)
  regPath <- PF.foldrMBlockStateLocs getRegPath (\_ _ -> return) truePair slice
  
  memPath <- PPa.toPatchPairC <$> TF.traverseF getMemPath (PS.simOut bundle)
  liftIO $ PPa.zipMPatchPairC regPath memPath (W4.andPred sym)


groundProofTransformer ::
  PA.ValidArch arch =>
  PT.ValidSym sym =>
  SymGroundEvalFn sym ->
  PF.ProofTransformer (EquivM_ sym arch) (PFI.ProofSym sym arch) (PFI.ProofGround arch)
groundProofTransformer fn = PF.ProofTransformer
  { PF.prfPredTrans = execGroundFn fn
  , PF.prfMemCellTrans = groundMemCell fn
  , PF.prfBVTrans = \(PFI.SymBV bv) -> groundBV fn bv
  , PF.prfExitTrans = \e ->
      PFI.GroundBlockExit <$> (groundBlockEndCase fn e) <*> (groundReturnPtr fn e)
  , PF.prfValueTrans = groundMacawValue fn
  , PF.prfContextTrans = \_ -> return ()
  , PF.prfCounterExampleTrans = return
  , PF.prfConditionTrans = \_ -> return ()
  , PF.prfConstraint = \a -> a
  }

groundSlice ::
  SymGroundEvalFn sym ->
  PF.BlockSliceTransition (PFI.ProofSym sym arch) ->
  EquivM sym arch (PF.BlockSliceTransition (PFI.ProofGround arch))
groundSlice fn = PF.transformBlockSlice (groundProofTransformer fn)


groundProofExpr ::
  SymGroundEvalFn sym ->
  PF.ProofExpr (PFI.ProofSym sym arch) tp ->
  EquivM sym arch (PF.ProofExpr (PFI.ProofGround arch) tp)
groundProofExpr fn = PF.transformProofExpr (groundProofTransformer fn)


isMemOpValid ::
  PA.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (PFI.GroundMemCell arch) (PF.BlockSliceMemOp (PFI.ProofGround arch)) -> Bool
isMemOpValid dom (MapF.Pair cell mop) =
  (not (PFI.cellInDomain dom cell)) || (not (PF.slMemOpCond mop)) || PF.slMemOpEquiv mop

isRegValid ::
  PA.ValidArch arch =>
  PFI.GroundDomain arch ->
  MapF.Pair (MM.ArchReg arch) (PF.BlockSliceRegOp (PFI.ProofGround arch)) -> Bool
isRegValid dom (MapF.Pair r rop) =
  (not (PFI.regInDomain dom r)) || PF.slRegOpEquiv rop

getInequivalenceReason ::
  PA.ValidArch arch =>
  PFI.GroundDomain arch ->
  PF.BlockSliceState (PFI.ProofGround arch) ->
  Maybe PEE.InequivalenceReason
getInequivalenceReason dom st =
  if | not $ all (isMemOpValid dom) (MapF.toList $ PF.slMemState st) -> Just PEE.InequivalentMemory
     | not $ all (isRegValid dom) (MapF.toList $ MM.regStateMap $ PF.slRegState st) -> Just PEE.InequivalentRegisters
     | otherwise -> Nothing


groundMuxTree ::
  SymGroundEvalFn sym ->
  C.MuxTree sym a ->
  EquivM sym arch a
groundMuxTree fn mt =
  withSym $ \sym ->
  IO.withRunInIO $ \runInIO -> do
    C.collapseMuxTree sym (\p a b -> do
                              p' <- runInIO (execGroundFn fn p)
                              return $ if p' then a else b) mt
groundBlockEndCase ::
  forall sym arch.
  SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch MS.MacawBlockEndCase
groundBlockEndCase fn blkend = withSym $ \sym -> do
  blkend_tree <- liftIO $ MS.blockEndCase (Proxy @arch) sym blkend
  groundMuxTree fn blkend_tree

groundBV ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (PFI.GroundBV w)
groundBV fn (CLM.LLVMPointer reg off) = withSym $ \sym -> do
  W4.BaseBVRepr w <- return $ W4.exprType off
  iReg <- liftIO $ W4.natToInteger sym reg
  greg <- execGroundFn fn iReg
  goff <- execGroundFn fn off
  regionTags <- getPointerTags fn iReg
  offTags <- getPointerTags fn off
  let integerToNat :: Integer -> Natural
      integerToNat i
        | i >= 0 = fromIntegral i
        | otherwise = fromIntegral (negate i)
  let gbv = PFI.mkGroundBV w (regionTags <> offTags) (integerToNat greg) goff
  return gbv

-- | Classify whether or not the given expression depends
-- on undefined pointers in the given model
getPointerTags ::
  forall sym arch tp.
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  EquivM sym arch MT.UndefPtrOpTags
getPointerTags fn e_outer = withValid $ withSym $ \sym -> do
  classify <- CMR.asks (MT.undefPtrClassify . envUndefPointerOps)
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> EquivM sym arch MT.UndefPtrOpTags
    go e = fmap getConst $ W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> Const <$> (liftIO $ MT.classifyExpr classify e)
      W4B.AppExpr a0 -> case W4B.appExprApp a0 of
        W4B.BaseIte _ _ cond eT eF -> fmap Const $ do
          cond_tags <- go cond
          branch_tags <- execGroundFn fn cond >>= \case
            True -> go eT
            False -> go eF
          return $ cond_tags <> branch_tags
        app -> TFC.foldrMFC acc mempty app
      W4B.NonceAppExpr a0 -> TFC.foldrMFC acc mempty (W4B.nonceExprApp a0)
      _ -> return mempty

    acc :: forall tp1 tp2. W4.SymExpr sym tp1 -> Const (MT.UndefPtrOpTags) tp2 -> EquivM sym arch (Const (MT.UndefPtrOpTags) tp2)
    acc e (Const tags) = do
      tags' <- go e
      return $ Const $ tags <> tags'

    resolveEq :: forall tp'.
      W4.SymExpr sym tp' ->
      W4.SymExpr sym tp' ->
      EquivM sym arch (Maybe Bool)
    resolveEq e1 e2 =
      Just <$> (execGroundFn fn =<< (liftIO $ W4.isEq sym e1 e2))

  go =<< resolveConcreteLookups sym resolveEq e_outer

groundLLVMPointer :: forall sym arch.
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (PFI.GroundLLVMPointer (MM.ArchAddrWidth arch))
groundLLVMPointer fn ptr = PFI.groundBVAsPointer <$> groundBV fn ptr


isStackCell ::
  PMC.MemCell sym arch w ->
  EquivM sym arch (W4.Pred sym)
isStackCell cell = withSym $ \sym -> do
  stackRegion <- CMR.asks envStackRegion
  let CLM.LLVMPointer region _ = PMC.cellPtr cell
  liftIO $ W4.natEq sym region stackRegion

groundMemCell :: forall sym arch w.
  SymGroundEvalFn sym ->
  PMC.MemCell sym arch w ->
  EquivM sym arch (PFI.GroundMemCell arch w)
groundMemCell fn cell = do
  gptr <- groundLLVMPointer fn $ PMC.cellPtr cell
  isStack <- isStackCell cell
  gIsStack <- execGroundFn fn isStack
  return $ PFI.GroundMemCell gptr (PMC.cellWidth cell) gIsStack

groundMacawValue ::
  SymGroundEvalFn sym ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (PFI.GroundMacawValue tp)
groundMacawValue fn e
  | CLM.LLVMPointerRepr _ <- PSR.macawRegRepr e
  , ptr <- PSR.macawRegValue e = do
    PFI.GroundMacawValue <$> groundBV fn ptr
  | CT.BoolRepr <- PSR.macawRegRepr e
  , val <- PSR.macawRegValue e = PFI.GroundMacawValue <$>  execGroundFn fn val
  | CT.StructRepr Ctx.Empty <- PSR.macawRegRepr e = PFI.GroundMacawValue <$> return ()
  | otherwise = throwHere $ PEE.UnsupportedRegisterType (Some $ PSR.macawRegRepr e)

groundReturnPtr ::
  forall sym arch.
  HasCallStack =>
  SymGroundEvalFn sym ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch (Maybe (PFI.GroundLLVMPointer (MM.ArchAddrWidth arch)))
groundReturnPtr fn blkend = case MS.blockEndReturn (Proxy @arch) blkend of
  W4P.PE p e -> execGroundFn fn p >>= \case
    True -> Just <$> groundLLVMPointer fn e
    False -> return Nothing
  W4P.Unassigned -> return Nothing
