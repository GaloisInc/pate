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

module Pate.Types
  ( DiscoveryConfig(..)
  , defaultDiscoveryCfg
  , PatchPair(..)
  , SimState(..)
  , SimInput(..)
  , simInMem
  , simInRegs
  , SimOutput(..)
  , simOutMem
  , simOutRegs
  , SimSpec(..)
  , SimBundle(..)
  , simPair
  , bindSpec
  , MemFootprints
  , MemFootprintsSpec
  , MemPred(..)
  , mapMemPred
  , memPredTrue
  , memPredFalse
  , SimVars(..)
  , flatVars
  , ExprMappable(..)
  , ExprImplyable(..)
  , ConcreteBlock(..)
  , BlockMapping(..)
  , BlockTarget(..)
  , ConcreteAddress(..)
  , BlockEntryKind(..)
  , MemCell(..)
  , MemCells(..)
  , StatePred(..)
  , StatePredSpec
  , EquivRelation(..)
  , MemEquivRelation(..)
  , RegEquivRelation(..)
  , absoluteAddress
  , addressAddOffset
  , concreteFromAbsolute
  , ParsedBlockMap(..)
  , ParsedFunctionMap
  , markEntryPoint

  , type WhichBinary
  , KnownBinary
  , Original
  , Patched
  , WhichBinaryRepr(..)
  , RegisterDiff(..)
  , ConcreteValue
  , GroundBV(..)
  , mkGroundBV
  , groundBVAsPointer
  , GroundLLVMPointer(..)
  , GroundMemOp(..)
  , SymGroundEvalFn(..)
  , execGroundFnIO
  , MemTraceDiff
  , MemOpDiff(..)
  , MacawRegEntry(..)
  , MacawRegVar(..)
  , macawRegEntry
  , InnerEquivalenceError(..)
  , InequivalenceReason(..)
  , EquivalenceError(..)
  , equivalenceError
  --- reporting
  , EquivalenceStatistics(..)
  , equivSuccess
  , InequivalenceResult(..)
  , ppRegDiff
  , ppEquivalenceError
  , ppEquivalenceStatistics
  , ppBlock
  , ppAbortedResult
  , ppLLVMPointer
  , ppPreRegs
  , ppDiff
  , ppMemDiff
  , showModelForExpr
 --- pre and post conditions
  , muxStatePred
  , getPostcondition
  , getPrecondition
  , impliesPrecondition
  , weakenEquivRelation
  , footPrintsToPred
  , addFootPrintsToPred
  , resolveCellEquiv
  , statePredFalse
  , flattenStatePred
  , memPredToList
  , listToMemPred
  , regPredRel
  , memPredPre
 --- term helpers
  , andM
  , iteM
  , impM
  , zipRegStates
  , rebindExpr
  , freshPtr
  , VarBinding(..)
  )
where

import           GHC.Stack
import           GHC.TypeNats

import           Control.Exception
import           Control.Monad ( foldM, forM )
import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.IO.Class as IO

import qualified Data.BitVector.Sized as BVS
import           Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import           Data.Maybe ( catMaybes )
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Traversable ( for )
import           Data.Typeable
import           Data.Foldable
import           Data.Monoid 
import           Numeric.Natural
import           Numeric

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context hiding ( replicate )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.Map as MapF

import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.Intrinsics as CS
import qualified Lang.Crucible.Utils.MuxTree as MX

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS

import qualified What4.Interface as W4

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G

import qualified Pate.Memory.MemTrace as MT

----------------------------------
-- Verification configuration
data DiscoveryConfig =
  DiscoveryConfig
    { cfgPairMain :: Bool
    -- ^ start by pairing the entry points of the binaries
    , cfgDiscoverFuns :: Bool
    -- ^ discover additional functions pairs during analysis
    }

defaultDiscoveryCfg :: DiscoveryConfig
defaultDiscoveryCfg = DiscoveryConfig True True


----------------------------------

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (Some (ParsedBlockMap arch)))


markEntryPoint ::
  MM.ArchSegmentOff arch ->
  ParsedBlockMap arch ids ->
  ParsedFunctionMap arch
markEntryPoint segOff blocks = M.singleton segOff (Some blocks) <$ getParsedBlockMap blocks

----------------------------------

newtype ConcreteAddress arch = ConcreteAddress (MM.MemAddr (MM.ArchAddrWidth arch))
  deriving (Eq, Ord)
deriving instance Show (ConcreteAddress arch)

data PatchPair arch = PatchPair
  { pOrig :: ConcreteBlock arch 'Original
  , pPatched :: ConcreteBlock arch 'Patched
  }
  deriving (Eq, Ord)

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (PatchPair arch) where
  show (PatchPair blk1 blk2) = ppBlock blk1 ++ " vs. " ++ ppBlock blk2


data SimState sym arch (bin :: WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
  }

data SimVars sym arch bin = SimVars
  {
    simVarMem :: MT.MemTraceVar sym (MM.ArchAddrWidth arch)
  , simVarRegs :: MM.RegState (MM.ArchReg arch) (MacawRegVar sym)
  , simVarState :: SimState sym arch bin
  }

data SimInput sym arch bin = SimInput
  {
    simInState :: SimState sym arch bin
  , simInBlock :: ConcreteBlock arch bin
  }


simInMem ::
  SimInput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simInMem simIn = simMem $ simInState simIn

simInRegs ::
  SimInput sym arch bin -> MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
simInRegs simIn = simRegs $ simInState simIn

data SimOutput sym arch bin = SimOutput
  {
    simOutState :: SimState sym arch bin
  , simOutExit :: MT.ExitClassifyImpl sym
  , simOutReturn :: CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch)))
  }

simOutMem ::
  SimOutput sym arch bin -> MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
simOutMem simIn = simMem $ simOutState simIn

simOutRegs ::
  SimOutput sym arch bin -> MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
simOutRegs simIn = simRegs $ simOutState simIn

data SimSpec sym arch f = SimSpec
  {
    specVarsO :: SimVars sym arch Original
  , specVarsP :: SimVars sym arch Patched
  , specAsm :: W4.Pred sym
  , specBody :: f
  }

data SimBundle sym arch = SimBundle
  {
    simInO :: SimInput sym arch Original
  , simInP :: SimInput sym arch Patched
  , simOutO :: SimOutput sym arch Original
  , simOutP :: SimOutput sym arch Patched
  }

simPair :: SimBundle sym arch -> PatchPair arch
simPair bundle = PatchPair (simInBlock $ simInO bundle) (simInBlock $ simInP bundle)

type MemFootprints sym arch = Set (MT.MemFootprint sym (MM.ArchAddrWidth arch))
type MemFootprintsSpec sym arch = SimSpec sym arch (MemFootprints sym arch)

data MemCell sym arch w where
  MemCell ::
    1 <= w =>
    { cellPtr :: CLM.LLVMPtr sym (MM.ArchAddrWidth arch)
    , cellWidth :: W4.NatRepr w
    } -> MemCell sym arch w

instance TestEquality (W4.SymExpr sym) => TestEquality (MemCell sym arch) where
  testEquality (MemCell (CLM.LLVMPointer reg1 off1) sz1) (MemCell (CLM.LLVMPointer reg2 off2) sz2)
   | Just Refl <- testEquality reg1 reg2
   , Just Refl <- testEquality off1 off2
   , Just Refl <- testEquality sz1 sz2
   = Just Refl
  testEquality _ _ = Nothing

instance OrdF (W4.SymExpr sym) => OrdF (MemCell sym arch) where
  compareF (MemCell (CLM.LLVMPointer reg1 off1) sz1) (MemCell (CLM.LLVMPointer reg2 off2) sz2) =
    lexCompareF reg1 reg2 $
     lexCompareF off1 off2 $
     compareF sz1 sz2

instance TestEquality (W4.SymExpr sym) => Eq (MemCell sym arch w) where
  stamp1 == stamp2 | Just Refl <- testEquality stamp1 stamp2 = True
  _ == _ = False

instance OrdF (W4.SymExpr sym) => Ord (MemCell sym arch w) where
  compare stamp1 stamp2  = toOrdering $ compareF stamp1 stamp2

newtype MemCells sym arch w = MemCells (Map (MemCell sym arch w) (W4.Pred sym))

mapCellPreds ::
  (W4.Pred sym -> IO (W4.Pred sym)) ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)
mapCellPreds f (MemCells stamps) = MemCells <$> mapM f stamps

data MemPred sym arch =
    MemPred
      { memPredLocs :: MapF.MapF W4.NatRepr (MemCells sym arch)
      -- ^ predicate status at these locations according to polarity
      , memPredPolarity :: W4.Pred sym
      -- ^ if true, then predicate is true at exactly the locations
      -- if false, then predicate is true everywhere but these locations
      }

mapMemPred ::
  forall sym arch m.
  Monad m =>
  W4.IsExprBuilder sym =>
  MemPred sym arch ->
  (forall w. 1 <= w => MemCell sym arch w -> W4.Pred sym -> m (W4.Pred sym)) ->
  m (MemPred sym arch)
mapMemPred memPred f = do
  let
    f' :: (forall w. MemCell sym arch w -> W4.Pred sym -> m (Maybe (W4.Pred sym)))
    f' cell@(MemCell{}) p = do
      p' <- f cell p
      case W4.asConstantPred p' of
        Just False -> return Nothing
        _ -> return $ Just p'
  locs <- TF.traverseF (\(MemCells cells) -> MemCells <$> M.traverseMaybeWithKey f' cells) (memPredLocs memPred)
  return $ memPred { memPredLocs = locs }

memPredToList ::
  MemPred sym arch ->
  [(Some (MemCell sym arch), W4.Pred sym)]
memPredToList memPred =
  concat $
  map (\(MapF.Pair _ (MemCells cells)) -> map (\(cell, p) -> (Some cell, p)) $ M.toList cells) $
  MapF.toList (memPredLocs memPred)

listToMemPred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  [(Some (MemCell sym arch), W4.Pred sym)] ->
  W4.Pred sym ->
  IO (MemPred sym arch)
listToMemPred sym cells pol = do
  let
    maps = map (\(Some cell, p) -> MapF.singleton (cellWidth cell) (MemCells (M.singleton cell p))) cells
  locs <- foldM (mergeMemCellsMap sym) MapF.empty maps
  return $ MemPred locs pol

mergeMemCells ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)  
mergeMemCells sym (MemCells cells1) (MemCells cells2) = do
  MemCells <$>
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\_ p1 p2 -> W4.orPred sym p1 p2))
      cells1
      cells2
                                                       
muxMemCells ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemCells sym arch w ->
  MemCells sym arch w ->
  IO (MemCells sym arch w)  
muxMemCells sym p (MemCells cellsT) (MemCells cellsF) = do
  notp <- W4.notPred sym p
  MemCells <$>
    M.mergeA
      (M.traverseMissing (\_ pT -> W4.andPred sym pT p))
      (M.traverseMissing (\_ pF -> W4.andPred sym pF notp)) 
      (M.zipWithAMatched (\_ p1 p2 -> W4.baseTypeIte sym p p1 p2))
      cellsT
      cellsF

muxMemCellsMap ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF f =>
  sym ->
  W4.Pred sym ->
  MapF.MapF f (MemCells sym arch) ->
  MapF.MapF f (MemCells sym arch) ->
  IO (MapF.MapF f (MemCells sym arch))  
muxMemCellsMap sym p cellsMapT cellsMapF = do
  notp <- W4.notPred sym p
  MapF.mergeWithKeyM
       (\_ cellsT cellsF -> Just <$> muxMemCells sym p cellsT cellsF)
       (TF.traverseF (mapCellPreds (W4.andPred sym p)))
       (TF.traverseF (mapCellPreds (W4.andPred sym notp)))
       cellsMapT
       cellsMapF

mergeMemCellsMap ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF f =>
  sym ->
  MapF.MapF f (MemCells sym arch) ->
  MapF.MapF f (MemCells sym arch) ->
  IO (MapF.MapF f (MemCells sym arch))  
mergeMemCellsMap sym cellsMap1 cellsMap2 = do
  MapF.mergeWithKeyM
       (\_ cells1 cells2 -> Just <$> mergeMemCells sym cells1 cells2)
       return
       return
       cellsMap1
       cellsMap2

muxMemPred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  W4.Pred sym ->
  MemPred sym arch ->
  MemPred sym arch ->
  IO (MemPred sym arch)
muxMemPred sym p predT predF = do
  pol <- W4.baseTypeIte sym p (memPredPolarity predT) (memPredPolarity predF)
  locs <- muxMemCellsMap sym p (memPredLocs predT) (memPredLocs predF)
  return $ MemPred locs pol

-- | True if this cell is logically equivalent to any cell in the given
-- collection
inCells ::
  forall sym arch w.
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemCell sym arch w ->
  MemCells sym arch w ->
  IO (W4.Pred sym) 
inCells sym cell (MemCells cells) =
  case M.lookup cell cells of
    Just cond | Just True <- W4.asConstantPred cond -> return $ W4.truePred sym
    _ -> go (W4.falsePred sym) (M.toList cells)
  where
    go :: W4.Pred sym -> [(MemCell sym arch w, W4.Pred sym)] -> IO (W4.Pred sym)
    go p ((cell', cond) : cells') = do
      eqPtrs <- MT.llvmPtrEq sym (cellPtr cell) (cellPtr cell')
      case W4.asConstantPred eqPtrs of
        Just True | Just True <- W4.asConstantPred cond -> return $ W4.truePred sym
        Just False -> go p cells'
        _ -> do
          matches <- W4.andPred sym eqPtrs cond
          p' <- W4.orPred sym p matches
          go p' cells'
    go p [] = return p

memPredAt ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemPred sym arch ->
  MemCell sym arch w ->
  IO (W4.Pred sym)
memPredAt sym mempred stamp = do
  isInLocs <- case MapF.lookup (cellWidth stamp) (memPredLocs mempred) of
    Just stamps -> inCells sym stamp stamps
    Nothing -> return $ W4.falsePred sym
  W4.isEq sym isInLocs (memPredPolarity mempred)

-- | Trivial predicate that is true on all of memory
memPredTrue :: W4.IsExprBuilder sym => sym -> MemPred sym arch
memPredTrue sym = MemPred MapF.empty (W4.falsePred sym)

-- | Predicate that is false on all of memory
memPredFalse :: W4.IsExprBuilder sym => sym -> MemPred sym arch
memPredFalse sym = MemPred MapF.empty (W4.truePred sym)

-- instance TestEquality (W4.SymExpr sym) => Eq (MemPred sym arch) where
--   (MemPred locs1 pol1) == (MemPred locs2 pol2) =
--     locs1 == locs2 && pol1 == pol2

-- instance OrdF (W4.SymExpr sym) => Ord (MemPred sym arch) where
--   compare (MemPred locs1 pol1) (MemPred locs2 pol2) =
--     compare locs1 locs2 <>
--     compare pol1 pol2

data StatePred sym arch =
  StatePred
    { predRegs :: Map (Some (MM.ArchReg arch)) (W4.Pred sym)
    -- ^ predicate is considered false on missing entries
    , predStack :: MemPred sym arch
    , predMem :: MemPred sym arch
    }

type StatePredSpec sym arch = SimSpec sym arch (StatePred sym arch)

muxStatePred ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  W4.Pred sym ->
  StatePred sym arch ->
  StatePred sym arch ->
  IO (StatePred sym arch)
muxStatePred sym p predT predF = do
  notp <- W4.notPred sym p
  regs <- M.mergeA
    (M.traverseMissing (\_ pT -> W4.andPred sym pT p))
    (M.traverseMissing (\_ pF -> W4.andPred sym pF notp)) 
    (M.zipWithAMatched (\_ p1 p2 -> W4.baseTypeIte sym p p1 p2))
    (predRegs predT)
    (predRegs predF)  
  stack <- muxMemPred sym p (predStack predT) (predStack predF)
  mem <- muxMemPred sym p (predMem predT) (predMem predF)
  return $ StatePred regs stack mem

statePredFalse :: W4.IsExprBuilder sym => sym -> StatePred sym arch
statePredFalse sym = StatePred M.empty (memPredFalse sym) (memPredFalse sym)

-- impliesStatePred ::
--   W4.IsExprBuilder sym =>
--   OrdF (W4.SymExpr sym) =>
--   OrdF (MM.ArchReg arch) =>
--   sym ->  
--   W4.Pred sym ->
--   StatePred sym arch ->
--   IO (StatePred sym arch)
-- impliesStatePred sym asm stPred = muxStatePred sym asm stPred (statePredTrue sym)


-- instance (TestEquality (W4.SymExpr sym), TestEquality (MM.ArchReg arch))  => Eq (StatePred sym arch) where
--   (StatePred regs1 stack1 mem1) == (StatePred regs2 stack2 mem2) =
--     regs1 == regs2 && stack1 == stack2 && mem1 == mem2

-- instance (OrdF (W4.SymExpr sym), OrdF (MM.ArchReg arch)) => Ord (StatePred sym arch) where
--   compare (StatePred regs1 stack1 mem1) (StatePred regs2 stack2 mem2) =
--     compare regs1 regs2 <>
--     compare stack1 stack2 <>
--     compare mem1 mem2

newtype MemEquivRelation sym arch =
  MemEquivRelation { applyMemEquivRelation :: (forall w. MemCell sym arch w -> CLM.LLVMPtr sym (8 W4.* w) -> CLM.LLVMPtr sym (8 W4.* w) -> IO (W4.Pred sym)) }


newtype RegEquivRelation sym arch =
  RegEquivRelation { applyRegEquivRelation :: (forall tp. MM.ArchReg arch tp -> MacawRegEntry sym tp -> MacawRegEntry sym tp -> IO (W4.Pred sym)) }


data EquivRelation sym arch =
  EquivRelation
    { eqRelRegs :: RegEquivRelation sym arch
    , eqRelStack :: MemEquivRelation sym arch
    , eqRelMem :: MemEquivRelation sym arch
    }


footPrintsToPred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemFootprints sym arch ->
  W4.Pred sym ->
  IO (MemPred sym arch)
footPrintsToPred sym foots polarity = do
  locs <- fmap catMaybes $ forM (S.toList foots) $ \(MT.MemFootprint ptr w dir cond) -> do
    polarityMatches <- case dir of
      MT.Read -> return $ W4.truePred sym
      MT.Write -> return $ W4.falsePred sym
    cond' <- W4.andPred sym polarityMatches (MT.getCond sym cond)
    case W4.asConstantPred cond' of
      Just False -> return Nothing
      _ -> return $ Just (Some (MemCell ptr w), cond')
  listToMemPred sym locs polarity

addFootPrintsToPred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  MemFootprints sym arch ->
  MemPred sym arch ->
  IO (MemPred sym arch)
addFootPrintsToPred sym foots memPred = do
  memPred' <- footPrintsToPred sym foots (memPredPolarity memPred)
  memLocs' <- mergeMemCellsMap sym (memPredLocs memPred) (memPredLocs memPred')
  return $ memPred { memPredLocs = memLocs' }

memPredPost ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch Original ->
  SimOutput sym arch Patched ->
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
memPredPost sym outO outP memEq memPred = do
  iteM sym (return $ (memPredPolarity memPred))
    (positiveMemPred sym stO stP memEq memPred) negativePolarity
  where
    stO = simOutState outO
    stP = simOutState outP
    
    memO = simOutMem outO
    memP = simOutMem outP

    -- | Cell equivalence that is conditional on whether or not this
    -- cell is in the domain of the given predicate
    resolveCell ::
      MemCell sym arch w ->
      W4.Pred sym ->
      IO (W4.Pred sym)
    resolveCell cell cond = do
      impM sym (memPredAt sym memPred cell) $
        resolveCellEquiv sym stO stP memEq cell cond

    -- | For the negative case, we need to consider the domain of the state itself -
    -- we assure that all writes are equivalent when they have not been excluded
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      footO <- MT.traceFootprint sym (MT.memSeq $ memO)
      footP <- MT.traceFootprint sym (MT.memSeq $ memP)
      let foot = S.union footO footP
      footCells <- memPredToList <$> footPrintsToPred sym foot (W4.falsePred sym)
      foldr (\(Some cell, cond) -> andM sym (resolveCell cell cond)) (return $ W4.truePred sym) footCells

positiveMemPred :: 
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch Original ->
  SimState sym arch Patched ->  
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
positiveMemPred sym stO stP memEq memPred = do
  let
    memCells = memPredToList memPred
    resolveCellPos = resolveCellEquiv sym stO stP memEq
  foldr (\(Some cell, cond) -> andM sym (resolveCellPos cell cond)) (return $ W4.truePred sym) memCells

resolveCellEquiv ::
  forall sym arch w.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch Original ->
  SimState sym arch Patched ->  
  MemEquivRelation sym arch ->
  MemCell sym arch w ->
  W4.Pred sym ->
  IO (W4.Pred sym)
resolveCellEquiv sym stO stP eqRel cell@(MemCell{})  cond = do
  let repr = MM.BVMemRepr (cellWidth cell) MM.BigEndian
  val1 <- MT.readMemArr sym memO (cellPtr cell) repr
  val2 <- MT.readMemArr sym memP (cellPtr cell) repr      
  impM sym (return cond) $ applyMemEquivRelation eqRel cell val1 val2
  where
    memO = simMem stO
    memP = simMem stP

freshPtr ::
  W4.IsSymExprBuilder sym =>
  1 <= w =>
  sym ->
  W4.NatRepr w ->
  IO (CLM.LLVMPtr sym (8 W4.* w))
freshPtr sym w
  | bvwidth <- W4.natMultiply (W4.knownNat @8) w
  , W4.LeqProof <- MT.mulMono (W4.knownNat @8) w
  , tyrepr <- W4.BaseBVRepr bvwidth = do
    off <- W4.freshConstant sym W4.emptySymbol tyrepr
    reg <- W4.freshConstant sym W4.emptySymbol W4.BaseNatRepr
    return $ CLM.LLVMPointer reg off
    
-- | Compute a precondition that is sufficiently strong to imply the given
-- equivalence relation on the given domain for the given input state
-- This predicate is meant to be *assumed* true.
memPredPre ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimInput sym arch Original ->
  SimInput sym arch Patched ->
  MemEquivRelation sym arch ->
  MemPred sym arch ->
  IO (W4.Pred sym)
memPredPre sym inO inP memEq memPred  = do
  iteM sym (return $ (memPredPolarity memPred))
    (positiveMemPred sym stO stP memEq memPred) negativePolarity
  where
    stO = simInState inO
    stP = simInState inP
    
    memO = simInMem inO
    memP = simInMem inP

    -- | Conditionally write a fresh value to the given memory location
    -- FIXME: update for when memory model supports regions
    freshWrite ::
      MemCell sym arch w ->
      W4.Pred sym ->
      MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
      IO (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))
    freshWrite cell@(MemCell{}) cond mem = do
      let
        ptr = cellPtr cell
        repr = MM.BVMemRepr (cellWidth cell) MM.BigEndian
      case W4.asConstantPred cond of
        Just False -> return mem
        _ -> do
          CLM.LLVMPointer _ fresh <- MT.readMemArr sym memP ptr repr
          --CLM.LLVMPointer _ original <- MT.readMemArr sym memO ptr repr
          --val <- W4.baseTypeIte sym cond fresh original
          mem' <- MT.writeMemArr sym mem ptr repr fresh
          mem'' <- W4.baseTypeIte sym cond (MT.memArr mem') (MT.memArr mem)
          return $ mem { MT.memArr = mem'' }

    -- | For the negative case, we assume that the patched trace is equivalent
    -- to the original trace with arbitrary modifications to excluded addresses
    negativePolarity :: IO (W4.Pred sym)
    negativePolarity = do
      mem' <- foldM (\mem' (Some cell, cond) -> freshWrite cell cond mem') memO (memPredToList memPred)
      W4.isEq sym (MT.memArr mem') (MT.memArr memP)

regPredRel ::
  forall sym arch.
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimState sym arch Original ->
  SimState sym arch Patched ->
  RegEquivRelation sym arch ->
  Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  IO (W4.Pred sym)
regPredRel sym stO stP regEquiv regPred  = do
  let
    regsO = simRegs stO
    regsP = simRegs stP
    regRel r p =
      impM sym (return p) $ applyRegEquivRelation regEquiv r (regsO ^. MM.boundValue r) (regsP ^. MM.boundValue r)
  foldr (\(Some r, p) -> andM sym (regRel r p)) (return $ W4.truePred sym) (M.toList regPred)

statePredPre ::
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimInput sym arch Original ->
  SimInput sym arch Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
statePredPre sym inO inP eqRel stPred  = do
  let
    stO = simInState inO
    stP = simInState inP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (predRegs stPred) 
    stacksEq = memPredPre sym inO inP (eqRelStack eqRel) (predStack stPred) 
    memEq = memPredPre sym inO inP (eqRelMem eqRel) (predMem stPred) 
  andM sym regsEq (andM sym stacksEq memEq)

statePredPost ::
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimOutput sym arch Original ->
  SimOutput sym arch Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
statePredPost sym outO outP eqRel stPred  = do
  let
    stO = simOutState outO
    stP = simOutState outP
    
    regsEq = regPredRel sym stO stP (eqRelRegs eqRel) (predRegs stPred) 
    stacksEq = memPredPost sym outO outP (eqRelStack eqRel) (predStack stPred) 
    memEq = memPredPost sym outO outP (eqRelMem eqRel) (predMem stPred) 
  andM sym regsEq (andM sym stacksEq memEq)

zipRegStates :: Monad m
             => MM.RegisterInfo r
             => MM.RegState r f
             -> MM.RegState r g
             -> (forall u. r u -> f u -> g u -> m h)
             -> m [h]
zipRegStates regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> Const <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  return $ map (\(MapF.Pair _ (Const v)) -> v) $ MapF.toList $ MM.regStateMap regs'

iteM ::
  W4.IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  m (W4.Pred sym) ->
  m (W4.SymExpr sym tp) ->
  m (W4.SymExpr sym tp) ->
  m (W4.SymExpr sym tp)
iteM sym p fT fF = do
  p' <- p
  case W4.asConstantPred p' of
    Just True -> fT
    Just False -> fF
    Nothing -> do
      fT' <- fT
      fF' <- fF
      IO.liftIO $ W4.baseTypeIte sym p' fT' fF'

impM ::
  W4.IsExprBuilder sym =>
  sym ->
  IO (W4.Pred sym) ->
  IO (W4.Pred sym) ->
  IO (W4.Pred sym)
impM sym pPre pPost = do
  pPre' <- pPre
  case W4.asConstantPred pPre' of
    Just True -> pPost
    Just False -> return $ W4.truePred sym
    _ -> do
      pPost' <- pPost
      W4.impliesPred sym pPre' pPost'
  
andM ::
  W4.IsExprBuilder sym =>
  sym ->
  IO (W4.Pred sym) ->
  IO (W4.Pred sym) ->
  IO (W4.Pred sym)
andM sym p1 p2 = do
  p1' <- p1
  case W4.asConstantPred p1' of
    Just True -> p2
    Just False -> return $ W4.falsePred sym
    _ -> do
      p2' <- p2
      W4.andPred sym p1' p2'


weakenEquivRelation ::
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  sym ->
  StatePred sym arch ->
  EquivRelation sym arch ->
  EquivRelation sym arch
weakenEquivRelation sym stPred eqRel =
  let
    regsFn = RegEquivRelation $ \r v1 v2 -> do
      case M.lookup (Some r) (predRegs stPred) of
        Just cond ->
          impM sym (return cond) $
            applyRegEquivRelation (eqRelRegs eqRel) r v1 v2
        Nothing -> return $ W4.truePred sym
    stackFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (memPredAt sym (predStack stPred) cell) $
        applyMemEquivRelation (eqRelStack eqRel) cell v1 v2
    memFn = MemEquivRelation $ \cell v1 v2 -> do
      impM sym (memPredAt sym (predMem stPred) cell) $
        applyMemEquivRelation (eqRelMem eqRel) cell v1 v2
  in EquivRelation regsFn stackFn memFn

-- | Resolve a domain predicate and equivalence relation into a precondition
getPrecondition ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)
getPrecondition sym bundle eqRel stPred = do
  statePredPre sym (simInO bundle) (simInP bundle) eqRel stPred

-- | True if the first precondition implies the second under the given
-- equivalence relation
impliesPrecondition ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimInput sym arch Original ->
  SimInput sym arch Patched ->
  EquivRelation sym arch ->
  StatePred sym arch ->
  StatePred sym arch ->
  IO (W4.Pred sym)  
impliesPrecondition sym inO inP eqRel stPredAsm stPredConcl = do
  asm <- statePredPre sym inO inP eqRel stPredAsm
  concl <- statePredPre sym inO inP eqRel stPredConcl
  W4.impliesPred sym asm concl

-- | Drop conditionals where possible, strengthening the predicate
flattenStatePred ::
  forall sym arch.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  StatePred sym arch ->
  IO (StatePred sym arch)  
flattenStatePred sym stPred = do
  let
    triviallyTrue :: W4.Pred sym -> W4.Pred sym
    triviallyTrue p = case W4.asConstantPred p of
      Just False ->  W4.falsePred sym
      _ -> W4.truePred sym

    filterFalse :: W4.Pred sym -> Maybe (W4.Pred sym)
    filterFalse p = case W4.asConstantPred p of
      Just False -> Nothing
      _ -> Just p
      
    triviallyFalse :: W4.Pred sym -> W4.Pred sym
    triviallyFalse p = case W4.asConstantPred p of
      Just True -> W4.truePred sym
      _ -> W4.falsePred sym
      
    predRegs' = M.mapMaybe (filterFalse . triviallyTrue) (predRegs stPred)
  predStack' <- mapMemPred (predStack stPred) (\_ p -> iteM sym (return $ memPredPolarity $ predStack stPred) (return $ triviallyTrue p) (return $ triviallyFalse p))
  predMem' <- mapMemPred (predMem stPred) (\_ p -> iteM sym (return $ memPredPolarity $ predMem stPred) (return $ triviallyTrue p) (return $ triviallyFalse p)) 
  return $ StatePred predRegs' predStack' predMem'


-- | Resolve a domain predicate and equivalence relation into a postcondition and associated
-- structured equivalence relation (for reporting counterexamples)
getPostcondition ::
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  OrdF (MM.ArchReg arch) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimBundle sym arch ->
  EquivRelation sym arch ->
  StatePred sym arch ->  
  IO (EquivRelation sym arch, W4.Pred sym)
getPostcondition sym bundle eqRel stPred = do
  post <- statePredPost sym (simOutO bundle) (simOutP bundle) eqRel stPred
  return (weakenEquivRelation sym stPred eqRel, post)

-- newtype ArchPtr sym arch = ArchPtr (CLM.LLVMPtr sym (MM.ArchAddrWidth arch))

-- instance W4.IsSymExprBuilder sym => Eq (ArchPtr sym arch) where
--   (ArchPtr (CLM.LLVMPointer reg1 off1)) == (ArchPtr (CLM.LLVMPointer reg2 off2))
--     | Just Refl <- testEquality reg1 reg2
--     , Just Refl <- testEquality off1 off2
--     = True
--   _ == _ = False

-- instance W4.IsSymExprBuilder sym => Ord (ArchPtr sym arch) where
--   compare (ArchPtr (CLM.LLVMPointer reg1 off1)) (ArchPtr (CLM.LLVMPointer reg2 off2)) =
--     toOrdering $ lexCompareF reg1 reg2 (compareF off1 off2)

data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

-- | Map from the start of original blocks to patched block addresses
newtype BlockMapping arch = BlockMapping (M.Map (ConcreteAddress arch) (ConcreteAddress arch))


-- | The way this block is entered dictates the initial equivalence relation we can assume
data BlockEntryKind arch =
    BlockEntryInitFunction
    -- ^ block starts a new function
  | BlockEntryPostFunction
    -- ^ block is an intermediate point in a function, after a function call
  | BlockEntryPostArch
    -- ^ block is an intermediate point in a function, after an arch function call
  | BlockEntryJump
    -- ^ block was entered by an arbitrary jump
    -- problems
  deriving (Eq, Ord, Show)

data ConcreteBlock arch (bin :: WhichBinary) =
  ConcreteBlock { concreteAddress :: ConcreteAddress arch
                , concreteBlockEntry :: BlockEntryKind arch
                , blockBinRepr :: WhichBinaryRepr bin
                }

instance TestEquality (ConcreteBlock arch) where
  testEquality (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    case testEquality binrepr1 binrepr2 of
      Just Refl | addr1 == addr2 && entry1 == entry2 -> Just Refl
      _ -> Nothing

instance Eq (ConcreteBlock arch bin) where
  blk1 == blk2 | Just Refl <- testEquality blk1 blk2 = True
  _ == _ = False

instance OrdF (ConcreteBlock arch) where
  compareF (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    lexCompareF binrepr1 binrepr2 $ fromOrdering $
      compare addr1 addr2 <>
      compare entry1 entry2

instance Ord (ConcreteBlock arch bin) where
  compare blk1 blk2 = toOrdering $ compareF blk1 blk2

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (ConcreteBlock arch bin) where
  show blk = ppBlock blk

--blockSize :: ConcreteBlock arch -> Int
--blockSize = concreteBlockSize

absoluteAddress :: (MM.MemWidth (MM.ArchAddrWidth arch)) => ConcreteAddress arch -> MM.MemWord (MM.ArchAddrWidth arch)
absoluteAddress (ConcreteAddress memAddr) = absAddr
  where
    Just absAddr = MM.asAbsoluteAddr memAddr

addressAddOffset :: (MM.MemWidth (MM.ArchAddrWidth arch))
                 => ConcreteAddress arch
                 -> MM.MemWord (MM.ArchAddrWidth arch)
                 -> ConcreteAddress arch
addressAddOffset (ConcreteAddress memAddr) memWord =
  ConcreteAddress (MM.incAddr (fromIntegral memWord) memAddr)

concreteFromAbsolute :: (MM.MemWidth (MM.ArchAddrWidth arch))
                     => MM.MemWord (MM.ArchAddrWidth arch)
                     -> ConcreteAddress arch
concreteFromAbsolute = ConcreteAddress . MM.absoluteAddr

----------------------------------

data GroundBV n where
  GroundBV :: W4.NatRepr n -> BVS.BV n -> GroundBV n
  GroundLLVMPointer :: GroundLLVMPointer n -> GroundBV n
  deriving Eq

instance Show (GroundBV n) where
  show = ppGroundBV

groundBVWidth :: GroundBV n -> W4.NatRepr n
groundBVWidth gbv = case gbv of
  GroundBV nr _ -> nr
  GroundLLVMPointer ptr -> ptrWidth ptr

instance TestEquality GroundBV where
  testEquality bv bv' = case testEquality (groundBVWidth bv) (groundBVWidth bv') of
    Just Refl | bv == bv' -> Just Refl
    _ -> Nothing

instance OrdF GroundBV where
  compareF (GroundBV w bv) (GroundBV w' bv') =
    lexCompareF w w' $ fromOrdering $ compare bv bv'
  compareF (GroundLLVMPointer ptr) (GroundLLVMPointer ptr') = compareF ptr ptr'
  compareF (GroundBV _ _) _ = LTF
  compareF (GroundLLVMPointer _) _ = GTF

instance Ord (GroundBV n) where
  compare bv bv' = toOrdering (compareF bv bv')

data GroundLLVMPointer n where
  GroundLLVMPointerC ::
      { ptrWidth :: W4.NatRepr n
      , ptrRegion :: Natural
      , ptrOffset :: BVS.BV n
      } -> GroundLLVMPointer n
  deriving Eq

instance TestEquality GroundLLVMPointer where
  testEquality ptr ptr'
    | Just Refl <- testEquality (ptrWidth ptr) (ptrWidth ptr')
    , ptr == ptr'
    = Just Refl
  testEquality _ _ = Nothing


instance OrdF GroundLLVMPointer where
  compareF (GroundLLVMPointerC w reg off) (GroundLLVMPointerC w' reg' off') =
    lexCompareF w w' $ joinOrderingF (fromOrdering $ compare reg reg') (fromOrdering $ compare off off')

instance Show (GroundLLVMPointer n) where
  show ptr = ppLLVMPointer ptr

mkGroundBV :: forall n.
  W4.NatRepr n ->
  Natural ->
  BVS.BV n ->
  GroundBV n
mkGroundBV nr reg bv = case reg > 0 of
 True -> GroundLLVMPointer $ GroundLLVMPointerC nr reg bv
 False -> GroundBV nr bv

groundBVAsPointer :: GroundBV n -> GroundLLVMPointer n
groundBVAsPointer gbv = case gbv of
  GroundLLVMPointer ptr -> ptr
  GroundBV w bv -> GroundLLVMPointerC w 0 bv

type family ConcreteValue (tp :: CC.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundBV w
type instance ConcreteValue (CC.MaybeType (CLM.LLVMPointerType w)) = Maybe (GroundBV w)

data RegisterDiff arch tp where
  RegisterDiff :: ShowF (MM.ArchReg arch) =>
    { rReg :: MM.ArchReg arch tp
    , rTypeRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , rPreOriginal :: ConcreteValue (MS.ToCrucibleType tp)
    , rPrePatched :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostOriginal :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostPatched :: ConcreteValue (MS.ToCrucibleType tp)
    , rPostEquivalent :: Bool
    , rDiffDescription :: String
    } -> RegisterDiff arch tp

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (W4B.ExprBuilder scope solver fs)

execGroundFnIO ::
  SymGroundEvalFn sym -> 
  W4.SymExpr sym tp ->
  IO (W4G.GroundValue tp)
execGroundFnIO (SymGroundEvalFn (W4G.GroundEvalFn fn)) = fn



----------------------------------
data GroundMemOp arch where
  GroundMemOp :: forall arch w.
    { gAddress :: GroundLLVMPointer (MM.ArchAddrWidth arch)
    , gCondition :: Bool
    , gValue_ :: GroundBV w
    } -> GroundMemOp arch

gValue :: GroundMemOp arch -> Some GroundBV
gValue (GroundMemOp { gValue_ = v}) = Some v

instance Eq (GroundMemOp arch) where
  (GroundMemOp addr cond v) == (GroundMemOp addr' cond' v')
    | Just Refl <- testEquality addr addr'
    , Just Refl <- testEquality v v'
    = cond == cond'
  _ == _ = False
      
instance Ord (GroundMemOp arch) where
  compare (GroundMemOp addr cond v) (GroundMemOp addr' cond' v') =
    case compare cond cond' of
      LT -> LT
      GT -> GT
      EQ -> toOrdering $ lexCompareF addr addr' $ compareF v v'

deriving instance Show (GroundMemOp arch)

data MemOpDiff arch = MemOpDiff
  { mIsRead :: Bool
  , mOpOriginal :: GroundMemOp arch
  , mOpRewritten :: GroundMemOp arch
  , mIsValid :: Bool
  , mDesc :: String
  } deriving (Eq, Ord, Show)

type MemTraceDiff arch = [MemOpDiff arch]

----------------------------------

data MacawRegEntry sym tp where
  MacawRegEntry ::
    { macawRegRepr :: CC.TypeRepr (MS.ToCrucibleType tp)
    , macawRegValue :: CS.RegValue sym (MS.ToCrucibleType tp)
    } ->
    MacawRegEntry sym tp       

data MacawRegVar sym tp where
  MacawRegVar ::
    { macawVarEntry :: MacawRegEntry sym tp
    , macawVarBVs :: Assignment (W4.BoundVar sym) (CrucBaseTypes (MS.ToCrucibleType tp))
    } ->
    MacawRegVar sym tp

type family CrucBaseTypes (tp :: CC.CrucibleType) :: Ctx W4.BaseType
type instance CrucBaseTypes (CLM.LLVMPointerType w) = (CC.EmptyCtx CC.::> W4.BaseNatType CC.::> W4.BaseBVType w)


instance CC.ShowF (W4.SymExpr sym) => Show (MacawRegEntry sym tp) where
  show (MacawRegEntry repr v) = case repr of
    CLM.LLVMPointerRepr{} | CLM.LLVMPointer rg bv <- v -> CC.showF rg ++ ":" ++ CC.showF bv
    _ -> "macawRegEntry: unsupported"

macawRegEntry :: CS.RegEntry sym (MS.ToCrucibleType tp) -> MacawRegEntry sym tp
macawRegEntry (CS.RegEntry repr v) = MacawRegEntry repr v

--------------------

data EquivalenceStatistics = EquivalenceStatistics
  { numPairsChecked :: Int
  , numEquivalentPairs :: Int
  , numPairsErrored :: Int
  } deriving (Eq, Ord, Read, Show)

instance Semigroup EquivalenceStatistics where
  EquivalenceStatistics checked total errored <> EquivalenceStatistics checked' total' errored' = EquivalenceStatistics
    (checked + checked')
    (total + total')
    (errored + errored')

instance Monoid EquivalenceStatistics where
  mempty = EquivalenceStatistics 0 0 0


equivSuccess :: EquivalenceStatistics -> Bool
equivSuccess (EquivalenceStatistics checked total errored) = errored == 0 && checked == total

data InequivalenceReason =
    InequivalentRegisters
  | InequivalentMemory
  | InvalidCallPair
  | InvalidPostState
  | PostRelationUnsat
  deriving (Eq, Ord, Show)

type ExitCaseDiff = (MT.ExitCase, MT.ExitCase)
type ReturnAddrDiff arch = (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch)), (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch))))

data InequivalenceResult arch =
  InequivalentResults
    { diffMem :: MemTraceDiff arch
    , diffExit :: ExitCaseDiff
    , diffRegs :: MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
    , diffRetAddr :: ReturnAddrDiff arch
    , diffReason :: InequivalenceReason
    }



instance Show (InequivalenceResult arch) where
  show _ = "InequivalenceResult"

----------------------------------

data WhichBinary = Original | Patched deriving (Bounded, Enum, Eq, Ord, Read, Show)

type Original = 'Original
type Patched = 'Patched

data WhichBinaryRepr (bin :: WhichBinary) where
  OriginalRepr :: WhichBinaryRepr 'Original
  PatchedRepr :: WhichBinaryRepr 'Patched

instance TestEquality WhichBinaryRepr where
  testEquality repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> Just Refl
    (PatchedRepr, PatchedRepr) -> Just Refl
    _ -> Nothing

instance OrdF WhichBinaryRepr where
  compareF repr1 repr2 = case (repr1, repr2) of
    (OriginalRepr, OriginalRepr) -> EQF
    (PatchedRepr, PatchedRepr) -> EQF
    (OriginalRepr, PatchedRepr) -> LTF
    (PatchedRepr, OriginalRepr) -> GTF

instance Show (WhichBinaryRepr bin) where
  show OriginalRepr = "Original"
  show PatchedRepr = "Patched"

instance KnownRepr WhichBinaryRepr Original where
  knownRepr = OriginalRepr

instance KnownRepr WhichBinaryRepr Patched where
  knownRepr = PatchedRepr

type KnownBinary (bin :: WhichBinary) = KnownRepr WhichBinaryRepr bin

----------------------------------

-- Expression binding


rebindExpr ::
  W4.IsSymExprBuilder sym =>
  sym ->
  Assignment (VarBinding sym) ctx ->
  W4.SymExpr sym tp ->
  IO (W4.SymExpr sym tp)
rebindExpr sym binds expr = do
  let vars = TFC.fmapFC bindVar binds
  let vals = TFC.fmapFC bindVal binds
  fn <- W4.definedFn sym W4.emptySymbol vars expr W4.AlwaysUnfold
  W4.applySymFn sym fn vals

class ExprMappable sym f where
  mapExpr ::
    W4.IsSymExprBuilder sym =>
    sym ->
    (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
    f ->
    IO f

class ExprImplyable sym f where
  implyExpr ::
    W4.IsSymExprBuilder sym =>
    sym ->
    W4.Pred sym ->
    f ->
    IO f

data VarBinding sym tp =
  VarBinding
   {
     bindVar :: W4.BoundVar sym tp
   , bindVal :: W4.SymExpr sym tp
   }

flatVars ::
  SimVars sym arch bin -> [Some (W4.BoundVar sym)]
flatVars simVars =
  let
    regVarPairs =
      MapF.toList $
      MM.regStateMap $
      (simVarRegs simVars)
    regVars = concat $ map (\(MapF.Pair _ (MacawRegVar _ vars)) -> TFC.toListFC Some vars) regVarPairs
    MT.MemTraceVar memVar = simVarMem simVars
  in ((Some memVar):regVars)

flatVarBinds ::
  forall sym arch bin.
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ->
  SimVars sym arch bin ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (MacawRegEntry sym) ->
  IO [Some (VarBinding sym)]
flatVarBinds _sym simVars mem regs = do
  let
    regBinds =
      MapF.toList $
      MM.regStateMap $
      MM.zipWithRegState (\(MacawRegVar _ vars) val -> MacawRegVar val vars) (simVarRegs simVars) regs
  regVarBinds <- fmap concat $ forM regBinds $ \(MapF.Pair _ (MacawRegVar val vars)) -> do
    case macawRegRepr val of
      CLM.LLVMPointerRepr{} -> do
        CLM.LLVMPointer region off <- return $ macawRegValue val
        (Ctx.Empty Ctx.:> regVar Ctx.:> offVar) <- return $ vars
        return $ [Some (VarBinding regVar region), Some (VarBinding offVar off)]
      _ -> fail "flatVarBinds: unsupported type"

  MT.MemTraceVar memVar <- return $ simVarMem simVars
  let memBind = VarBinding memVar (MT.memArr mem)   
  return $ ((Some memBind):regVarBinds)

bindSpec ::
  ExprMappable sym f =>
  W4.IsSymExprBuilder sym =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym -> 
  SimState sym arch Original ->
  SimState sym arch Patched ->
  SimSpec sym arch f ->
  IO (W4.Pred sym, f)
bindSpec sym stO stP spec = do
  flatO <- flatVarBinds sym (specVarsO spec) (simMem stO) (simRegs stO)
  flatP <- flatVarBinds sym (specVarsP spec) (simMem stP) (simRegs stP)
  Some flatCtx <- return $ Ctx.fromList (flatO ++ flatP)
  body <- mapExpr sym (rebindExpr sym flatCtx) (specBody spec)
  asm <- rebindExpr sym flatCtx (specAsm spec)
  return $ (asm, body)



-- instance ExprMappable sym (EquivRelation sym arch) where
--   mapExpr sym f eqRel = case eqRel of
--     EquivRelationEqMem asm predRegs_ -> do
--       asm' <- f asm
--       predRegs' <- mapM f predRegs_
--       return $ EquivRelationEqMem asm' predRegs'
--     EquivRelationPred stPred -> EquivRelationPred <$> mapExpr sym f stPred

-- instance ExprImplyable sym (EquivRelation sym arch) where
--   implyExpr sym asm = \case
--     EquivRelationEqMem asm' regsEq -> do
--       asm'' <- W4.andPred sym asm asm'
--       return $ EquivRelationEqMem asm'' regsEq
--     EquivRelationPred stPred -> EquivRelationPred <$> implyExpr sym asm stPred

-- instance ExprMappable sym (StatePred sym arch) where
--   mapExpr = mapExprStatePred

-- instance ExprImplyable sym (StatePred sym arch) where
--   implyExpr sym asm stPred = do
--     regs <- mapM (W4.impliesPred sym asm) (predRegs stPred)
--     mem <- mapM (W4.impliesPred sym asm) (predMem stPred)
--     return $ StatePred regs mem


instance ExprMappable sym (MT.MemOpCondition sym) where
  mapExpr _sym f = \case
    MT.Conditional p -> MT.Conditional <$> f p
    MT.Unconditional -> return MT.Unconditional

instance ExprMappable sym (MT.MemOp sym w) where
  mapExpr sym f = \case
    MT.MemOp ptr dir cond w val endian -> do
      ptr' <- mapExprPtr sym f ptr
      val' <- mapExprPtr sym f val
      cond' <- mapExpr sym f cond
      return $ MT.MemOp ptr' dir cond' w val' endian
    MT.MergeOps p seq1 seq2 -> do
      p' <- f p
      seq1' <- traverse (mapExpr sym f) seq1
      seq2' <- traverse (mapExpr sym f) seq2
      return $ MT.MergeOps p' seq1' seq2'

instance ExprMappable sym (MT.MemTraceImpl sym w) where
  mapExpr sym f mem = do
    memSeq' <- traverse (mapExpr sym f) $ MT.memSeq mem
    memArr' <- f $ MT.memArr mem
    return $ MT.MemTraceImpl memSeq' memArr'

instance ExprMappable sym (MacawRegEntry sym tp) where
  mapExpr sym f entry = do
    case macawRegRepr entry of
      CLM.LLVMPointerRepr{} -> do
        val' <- mapExprPtr sym f $ macawRegValue entry
        return $ entry { macawRegValue = val' }
      _ -> fail "mapExpr: unsupported macaw type"

instance ExprMappable sym (SimState sym arch bin) where
  mapExpr sym f st = do
    simMem' <- mapExpr sym f $ simMem st
    simRegs' <- MM.traverseRegsWith (\_ -> mapExpr sym f) $ simRegs st
    return $ SimState simMem' simRegs'

instance ExprMappable sym (SimInput sym arch bin) where
  mapExpr sym f simIn = do
    st <- mapExpr sym f (simInState simIn)
    return $ simIn { simInState = st }

instance ExprMappable sym (SimOutput sym arch bin) where
  mapExpr sym f simOut = do
    st <- mapExpr sym f (simOutState simOut)
    ret <- traverse (mapExprPtr sym f) $ simOutReturn simOut
    return $ simOut { simOutState = st, simOutReturn = ret }

instance ExprMappable sym (MT.MemFootprint sym arch) where
  mapExpr sym f (MT.MemFootprint ptr w dir cond) = do
    ptr' <- mapExprPtr sym f ptr
    cond' <- mapExpr sym f cond
    return $ MT.MemFootprint ptr' w dir cond'

instance ExprMappable sym (SimBundle sym arch) where
  mapExpr sym f bundle = do
    simInO' <- mapExpr sym f $ simInO bundle
    simInP' <- mapExpr sym f $ simInP bundle
    simOutO' <- mapExpr sym f $ simOutO bundle
    simOutP' <- mapExpr sym f $ simOutP bundle
    return $ SimBundle simInO' simInP' simOutO' simOutP'

instance ExprMappable sym (MemCell sym arch w) where
  mapExpr sym f (MemCell ptr w) = do
    ptr' <- mapExprPtr sym f ptr
    return $ MemCell ptr' w

instance OrdF (W4.SymExpr sym) => ExprMappable sym (MemCells sym arch w) where
  mapExpr sym f (MemCells cells) = do
    maps <- forM (M.toList cells) $ \(cell, p) -> do
      cell' <- mapExpr sym f cell
      p' <- f p
      return $ MemCells $ M.singleton cell' p'
    foldM (mergeMemCells sym) (MemCells M.empty) maps

instance ExprMappable sym (MemPred sym arch) where
  mapExpr sym f memPred = do
    locs <- MapF.traverseWithKey (\_ -> mapExpr sym f) (memPredLocs memPred)
    pol <- f (memPredPolarity memPred)
    return $ MemPred locs pol

instance ExprMappable sym (StatePred sym arch) where
  mapExpr sym f stPred = do
    regs <- mapM f (predRegs stPred)
    stack <- mapExpr sym f (predStack stPred)
    mem <- mapExpr sym f (predMem stPred)
    return $ StatePred regs stack mem

mapExprPtr ::
  forall sym w.
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
  CLM.LLVMPtr sym w ->
  IO (CLM.LLVMPtr sym w)  
mapExprPtr _sym f (CLM.LLVMPointer reg off) = do
  reg' <- f reg
  off' <- f off
  return $ CLM.LLVMPointer reg' off'  

-- mapExprStatePred ::
--   forall sym arch.
--   W4.IsSymExprBuilder sym =>
--   sym ->
--   (forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)) ->
--   StatePred sym arch ->
--   IO (StatePred sym arch)
-- mapExprStatePred sym f stPred = do
--   regs <- mapM f (predRegs stPred)
--   let mergePreds ::
--         IO (W4.Pred sym) ->
--         IO (W4.Pred sym) ->
--         IO (W4.Pred sym)
--       mergePreds p1 p2 = do
--         p1' <- p1
--         p2' <- p2
--         W4.andPred sym p1' p2'
--   mem <- mapM go (M.assocs (predMem stPred))
--   memMap <- sequenceA $ M.fromListWith mergePreds mem
--   return $ StatePred regs memMap
--   where
--     go ::
--       (ArchPtr sym arch, W4.Pred sym) ->
--       IO (ArchPtr sym arch, IO (W4.Pred sym))
--     go (ArchPtr (CLM.LLVMPointer reg off), p) = do
--       reg' <- f reg
--       off' <- f off
--       return $ (ArchPtr (CLM.LLVMPointer reg' off'), f p)

-----------------------------

data InnerEquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
  | UnsupportedArchitecture
  | UnsupportedRegisterType (Some CC.TypeRepr)
  | SymbolicExecutionFailed String -- TODO: do something better
  | InconclusiveSAT
  | NoUniqueFunctionOwner (IM.Interval (ConcreteAddress arch)) [MM.ArchSegmentOff arch]
  | LookupNotAtFunctionStart (ConcreteAddress arch)
  | StrangeBlockAddress (MM.ArchSegmentOff arch)
  -- starting address of the block, then a starting and ending address bracketing a range of undiscovered instructions
  | UndiscoveredBlockPart (ConcreteAddress arch) (ConcreteAddress arch) (ConcreteAddress arch)
  | NonConcreteParsedBlockAddress (MM.ArchSegmentOff arch)
  | BlockExceedsItsSegment (MM.ArchSegmentOff arch) (MM.ArchAddrWord arch)
  | BlockEndsMidInstruction
  | BlockStartsEarly (MM.ArchAddrWord arch) (MM.ArchAddrWord arch)
  | PrunedBlockIsEmpty
  | MemOpConditionMismatch
  | UnexpectedBlockKind String
  | UnexpectedMultipleEntries [MM.ArchSegmentOff arch] [MM.ArchSegmentOff arch]
  | forall ids. InvalidBlockTerminal (MD.ParsedTermStmt arch ids)
  | MissingPatchPairResult (PatchPair arch)
  | EquivCheckFailure String -- generic error
  | ImpossibleEquivalence
  | AssumedFalse
  | BlockExitMismatch
  | InvalidSMTModel
  | UnexpectedNonBoundVar
  | UnsatisfiableAssumptions
  | InequivalentError (InequivalenceResult arch)
deriving instance MS.SymArchConstraints arch => Show (InnerEquivalenceError arch)

data EquivalenceError arch =
  EquivalenceError
    { errWhichBinary :: Maybe (Some WhichBinaryRepr)
    , errStackTrace :: Maybe CallStack
    , errEquivError :: InnerEquivalenceError arch
    }
instance MS.SymArchConstraints arch => Show (EquivalenceError arch) where
  show e = unlines $ catMaybes $
    [ fmap (\(Some b) -> "For " ++ show b ++ " binary") (errWhichBinary e)
    , fmap (\s -> "At " ++ prettyCallStack s) (errStackTrace e)
    , Just (show (errEquivError e))
    ]

instance (Typeable arch, MS.SymArchConstraints arch) => Exception (EquivalenceError arch)

equivalenceError :: InnerEquivalenceError arch -> EquivalenceError arch
equivalenceError err = EquivalenceError
  { errWhichBinary = Nothing
  , errStackTrace = Nothing
  , errEquivError = err
  }
----------------------------------

ppEquivalenceStatistics :: EquivalenceStatistics -> String
ppEquivalenceStatistics (EquivalenceStatistics checked equiv err) = unlines
  [ "Summary of checking " ++ show checked ++ " pairs:"
  , "\t" ++ show equiv ++ " equivalent"
  , "\t" ++ show (checked-equiv-err) ++ " inequivalent"
  , "\t" ++ show err ++ " skipped due to errors"
  ]

ppEquivalenceError ::
  MS.SymArchConstraints arch =>
  ShowF (MM.ArchReg arch) =>
  EquivalenceError arch -> String
ppEquivalenceError err | (InequivalentError ineq)  <- errEquivError err = case ineq of
  InequivalentResults traceDiff exitDiffs regDiffs _retDiffs reason -> "x\n" ++ ppReason reason ++ "\n" ++ ppExitCaseDiff exitDiffs ++ "\n" ++ ppPreRegs regDiffs ++ ppMemTraceDiff traceDiff ++ ppDiffs regDiffs
ppEquivalenceError err = "-\n\t" ++ show err ++ "\n" -- TODO: pretty-print the error


ppReason :: InequivalenceReason -> String
ppReason r = "\tEquivalence Check Failed: " ++ case r of
  InequivalentRegisters -> "Final registers diverge."
  InequivalentMemory -> "Final memory states diverge."
  InvalidCallPair -> "Unexpected next IPs."
  InvalidPostState -> "Post state is invalid."
  PostRelationUnsat -> "Post-equivalence relation cannot be satisifed"

ppExitCaseDiff :: ExitCaseDiff -> String
ppExitCaseDiff (eO, eP) | eO == eP = "\tBlock Exited with " ++ ppExitCase eO
ppExitCaseDiff (eO, eP) =
  "\tBlocks have different exit conditions: "
  ++ ppExitCase eO ++ " (original) vs. "
  ++ ppExitCase eP ++ " (rewritten)"

ppExitCase :: MT.ExitCase -> String
ppExitCase ec = case ec of
  MT.ExitCall -> "function call"
  MT.ExitReturn -> "function return"
  MT.ExitArch -> "syscall"
  MT.ExitUnknown -> "unknown"

ppMemTraceDiff :: MemTraceDiff arch -> String
ppMemTraceDiff diffs = "\tTrace of memory operations:\n" ++ concatMap ppMemOpDiff (toList diffs)

ppMemOpDiff :: MemOpDiff arch -> String
ppMemOpDiff diff
  | shouldPrintMemOp diff
  =  "\t\t" ++ ppDirectionVerb (mIsRead diff) ++ " "
  ++ ppGroundMemOp (mIsRead diff) (mOpOriginal diff)
  ++ (if mOpOriginal diff == mOpRewritten diff
      then ""
      else
        " (original) vs. " ++ ppGroundMemOp (mIsRead diff) (mOpRewritten diff) ++ " (rewritten)"
         ++ "\n" ++ mDesc diff
     )
  ++ "\n"
ppMemOpDiff _ = ""

shouldPrintMemOp :: MemOpDiff arch -> Bool
shouldPrintMemOp diff =
  mOpOriginal diff /= mOpRewritten diff ||
  gCondition (mOpOriginal diff) ||
  gCondition (mOpRewritten diff)

ppGroundMemOp :: Bool -> GroundMemOp arch -> String
ppGroundMemOp isRead op
  | Some v <- gValue op
  =  ppGroundBV v
  ++ " " ++ ppDirectionPreposition isRead ++ " "
  ++ ppLLVMPointer (gAddress op)
  ++ if gCondition op
     then ""
     else " (skipped)"

ppDirectionVerb :: Bool -> String
ppDirectionVerb True = "read"
ppDirectionVerb False = "wrote"

ppDirectionPreposition :: Bool -> String
ppDirectionPreposition True = "from"
ppDirectionPreposition False = "to"

ppEndianness :: MM.Endianness -> String
ppEndianness MM.BigEndian = "→"
ppEndianness MM.LittleEndian = "←"

ppPreRegs ::
  HasCallStack =>
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
  -> String
ppPreRegs diffs = "\tInitial registers of a counterexample:\n" ++ case TF.foldMapF ppPreReg diffs of
  (Sum 0, s) -> s
  (Sum n, s) -> s ++ "\t\t(and " ++ show n ++ " other all-zero slots)\n"

ppPreReg ::
  HasCallStack =>
  RegisterDiff arch tp ->
  (Sum Int, String)
ppPreReg diff = case rTypeRepr diff of
  CLM.LLVMPointerRepr _
    | GroundBV _ obv <- rPreOriginal diff
    , GroundBV _ pbv <- rPrePatched diff ->
      case (BVS.asUnsigned obv, BVS.asUnsigned pbv) of
        (0, 0) -> (1, "")
        _ | obv == pbv -> (0, ppSlot diff ++ ppGroundBV (rPreOriginal diff) ++ "\n")
        _ -> (0, ppSlot diff ++ ppGroundBV (rPreOriginal diff) ++ "(original) vs. " ++ ppGroundBV (rPrePatched diff) ++ "\n")
  CLM.LLVMPointerRepr _
    | GroundLLVMPointer optr <- rPreOriginal diff
    , GroundLLVMPointer pptr <- rPrePatched diff ->
      case optr == pptr of
        True -> (0, ppSlot diff ++ ppLLVMPointer optr ++ "\n")
        False -> (0, ppSlot diff ++ ppLLVMPointer optr ++ "(original) vs. " ++ ppLLVMPointer pptr ++ "\n")

  _ -> (0, ppSlot diff ++ "unsupported register type in precondition pretty-printer\n")

ppDiffs ::
  MS.SymArchConstraints arch =>
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch) ->
  String
ppDiffs diffs =
  "\tFinal IPs: "
  ++ ppGroundBV (rPostOriginal (diffs ^. MM.curIP))
  ++ " (original) vs. "
  ++ ppGroundBV (rPostPatched (diffs ^. MM.curIP))
  ++ " (rewritten)\n"
  ++ "\tMismatched resulting registers:\n" ++ TF.foldMapF ppDiff diffs

ppDiff ::
  RegisterDiff arch tp ->
  String
ppDiff diff | rPostEquivalent diff = ""
ppDiff diff = ppSlot diff ++ case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> ""
    ++ ppGroundBV (rPostOriginal diff)
    ++ " (original) vs. "
    ++ ppGroundBV (rPostPatched diff)
    ++ " (rewritten)\n"
    ++ rDiffDescription diff
    ++ "\n\n"
  _ -> "unsupported register type in postcondition comparison pretty-printer\n"

ppRegEntry :: SymGroundEvalFn sym -> MacawRegEntry sym tp -> IO String
ppRegEntry fn (MacawRegEntry repr v) = case repr of
  CLM.LLVMPointerRepr _ | CLM.LLVMPointer _ offset <- v -> showModelForExpr fn offset
  _ -> return "Unsupported register type"


showModelForPtr :: forall sym w.
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  IO String
showModelForPtr fn (CLM.LLVMPointer reg off) = do
  regStr <- showModelForExpr fn reg
  offStr <- showModelForExpr fn off
  return $ "Region:\n" ++ regStr ++ "\n" ++ offStr

ppMemDiff ::
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym ptrW ->
  CLM.LLVMPtr sym w ->
  CLM.LLVMPtr sym w ->
  IO String
ppMemDiff fn ptr val1 val2 = do
  ptrStr <- showModelForPtr fn ptr
  val1Str <- showModelForPtr fn val1
  val2Str <- showModelForPtr fn val2
  return $ "Pointer: " ++ ptrStr ++ "\nValue (original)" ++ val1Str ++ "\nValue (patched)" ++ val2Str

ppRegDiff ::
  SymGroundEvalFn sym ->
  MacawRegEntry sym tp ->
  MacawRegEntry sym tp ->
  IO String
ppRegDiff fn reg1 reg2 = do
  origStr <- ppRegEntry fn reg1
  patchedStr <- ppRegEntry fn reg2
  return $ "Original: \n" ++ origStr ++ "\n\nPatched: \n" ++ patchedStr

ppSlot ::
  RegisterDiff arch tp
  -> String
ppSlot (RegisterDiff { rReg = reg })  = "\t\tslot " ++ (pad 4 . showF) reg ++ ": "

ppGroundBV :: GroundBV w -> String
ppGroundBV gbv = case gbv of
  GroundBV w bv -> BVS.ppHex w bv
  GroundLLVMPointer ptr -> ppLLVMPointer ptr

ppLLVMPointer :: GroundLLVMPointer w -> String
ppLLVMPointer (GroundLLVMPointerC bitWidthRepr reg offBV) = ""
  ++ pad 3 (show reg)
  ++ "+0x"
  ++ padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")
  where
    off = BVS.asUnsigned offBV
    bitWidth = W4.natValue bitWidthRepr

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> String
ppBlock b = ""
  -- 100k oughta be enough for anybody
  -- ++ pad 6 (show (blockSize b))
  -- ++ " bytes at "
  ++ show (absoluteAddress (concreteAddress b))

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"


padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

pad :: Int -> String -> String
pad = padWith ' '


--------------------------------

freeExprTerms :: forall sym t st fs tp.
  sym ~ W4B.ExprBuilder t st fs =>
  W4.SymExpr sym tp ->
  IO (Set (Some (W4.SymExpr sym)))
freeExprTerms expr = do
  cache <- W4B.newIdxCache
  let
    go :: forall tp'. W4.SymExpr sym tp' -> IO (Const (Set (Some (W4.SymExpr sym))) tp')
    go e = W4B.idxCacheEval cache e $ case e of
      W4B.BoundVarExpr _ -> return $ Const $ S.singleton (Some e)
      W4B.AppExpr appExpr -> do
        TFC.foldrMFC (collect @tp') mempty $ W4B.appExprApp appExpr
      W4B.NonceAppExpr naeE | W4B.FnApp fn args <- W4B.nonceExprApp naeE ->
        case W4B.symFnInfo fn of
          W4B.UninterpFnInfo _ _ -> return $ Const $ S.singleton (Some e)
          W4B.DefinedFnInfo _ _ _ -> TFC.foldrMFC (collect @tp') mempty args
          _ -> return $ mempty
      _ -> return $ mempty
    collect ::
      forall tp'' tp'.
      W4.SymExpr sym tp' ->
      Const (Set (Some (W4.SymExpr sym))) tp'' ->
      IO (Const (Set (Some (W4.SymExpr sym))) tp'')
    collect e (Const s) = do
      Const s' <- go e
      return $ Const $ S.union s s'
  getConst <$> go expr


showModelForExpr :: forall sym tp.
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  IO String
showModelForExpr fn@(SymGroundEvalFn _) expr = do
  freeTerms <- freeExprTerms expr
  v <- execGroundFnIO fn expr
  let
    s = "Expression: " ++ show expr ++ "\n" ++
        "Value: " ++ showGroundValue (W4.exprType expr) v ++ "\n" ++
        "Environment:"

  foldM go s freeTerms
  where
    go :: String -> Some (W4.SymExpr sym)  -> IO String
    go s (Some e) = do
      gv <- execGroundFnIO fn e
      return $ s ++ "\n" ++ show e ++ " :== " ++ showGroundValue (W4.exprType e) gv

showGroundValue ::
  W4.BaseTypeRepr tp ->
  W4G.GroundValue tp ->
  String
showGroundValue repr gv = case repr of
  W4.BaseBoolRepr -> show gv
  W4.BaseBVRepr w -> BVS.ppHex w gv
  W4.BaseNatRepr -> show gv
  _ -> "Unsupported ground value"

