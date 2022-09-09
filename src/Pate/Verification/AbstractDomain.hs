{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Pate.Verification.AbstractDomain
  ( AbstractDomain(..)
  , AbstractDomainSpec
  , AbsRange(..)
  , AbstractDomainVals(..)
  , WidenLocs(..)
  , DomainKind(..)
  , emptyDomainVals
  , groundToAbsRange
  , extractAbsRange
  , widenAbsDomainVals
  , initAbsDomainVals
  , absDomainValsToPred
  , absDomainToPrecond
  , absDomainValsToPostCond
  , ppAbstractDomain
  , noAbsVal
  ) where

import qualified Prettyprinter as PP

import           Control.Monad ( forM, unless )
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Writer as CMW
import           Control.Lens ( (^.) )

import           Data.Functor.Const
import qualified Data.Set as S
import           Data.Set ( Set )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.List as PL

import qualified What4.Interface as W4
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Concrete as W4C

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT
import           Lang.Crucible.Backend (IsSymInterface)

import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.AbsDomain.AbsState as MAS

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PB
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Location as PL
import qualified Pate.MemCell as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PR
import qualified Pate.SimState as PS
import qualified Pate.Solver as PSo
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Register.Traversal as PRt
import qualified Pate.ExprMappable as PEM
import           Pate.Panic
import           Pate.TraceTree

import qualified What4.PredMap as WPM

-- | Defining abstract domains which propagate forwards during strongest
-- postcondition analysis.
-- The critical domain information is the equality domain (a 'PED.EquivalenceDomain'
-- indicating which memory locations are equivalent between the original and patched programs)
-- Additional information constraining viable values is also stored independently for each
-- program in 'AbstractDomainVals'
-- TODO: propagate scope to inner types
data AbstractDomain sym arch (v :: PS.VarScope) where
  AbstractDomain ::
    { absDomEq :: PED.EquivalenceDomain sym arch
      -- ^ specifies which locations are equal between the original vs. patched programs
    , absDomVals :: PPa.PatchPair (AbstractDomainVals sym arch)
      -- ^ specifies independent constraints on the values for the original and patched programs
    } -> AbstractDomain sym arch v

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationWitherable sym arch (AbstractDomain sym arch bin) where
  witherLocation sym (AbstractDomain a b) f = AbstractDomain <$> PL.witherLocation sym a f <*> PL.witherLocation sym b f


-- | An 'AbstractDomain' that is closed under a symbolic machine state via
-- 'SimSpec'.
-- In general, a 'SimSpec' serves as a lambda abstraction over the variables representing
-- the machine state in the subterms of any type (as defined by the term traversal
-- in 'Pate.ExprMappable'). In essence, this represents a function from a 'SimState' to
-- an 'PED.EquivalenceDomain' (applied via 'bindSpec').
--
-- The variables in a 'AbstractDomain' are instantiated in two different contexts:
--    1. When used as an *assumed* pre-domain, variables are instantiated to the initial *free*
--       variables of the slice.
--    2. When used as a *target* post-domain, variables are instantiated to terms representing
--       the final values of the slice.
-- For example: a domain could say @r1[r2_O != 0, r2_P > 2]@ (i.e. register @r1@ is in the domain if
-- the value in @r2@ is nonzero in the original program and greater than two in the patched program).
-- A slice contains two major components: a fully symbolic initial state (i.e. a 'SimInput') and
-- a resulting final state (i.e. a 'SimOutput').
-- Assume the slice under analysis simply assigns @1@ to @r2@ in both programs.
--
-- When instantiated as a pre-domain, we simply assign r2_O and r2_P to the free variables
-- representing the initial state of the slice.
-- When instantiated as a post-domain, we instantiate @r2_O@ and @r2_P@ to @1@, resulting in
-- an 'PED.EquivalenceDomain' that looks like @r1[1 != 0, 1 > 2]@. Since this condition is false,
-- @r1@ is excluded from the resulting instantiated domain.

type AbstractDomainSpec sym arch = PS.SimSpec sym arch (AbstractDomain sym arch)

instance PS.Scoped (AbstractDomain sym arch) where
  unsafeCoerceScope (AbstractDomain a b) = AbstractDomain a b

-- | Defining the known range for a given location. Currently this is either a constant
-- value or an unconstrained value.
data AbsRange (tp :: W4.BaseType) where
  AbsIntConstant :: Integer -> AbsRange W4.BaseIntegerType
  AbsBVConstant :: 1 W4.<= w => W4.NatRepr w -> BV.BV w -> AbsRange (W4.BaseBVType w)
  AbsBoolConstant :: Bool -> AbsRange W4.BaseBoolType
  AbsUnconstrained :: W4.BaseTypeRepr tp -> AbsRange tp

groundToAbsRange :: W4.BaseTypeRepr tp -> W4G.GroundValue tp -> AbsRange tp
groundToAbsRange repr v = case repr of
  W4.BaseIntegerRepr -> AbsIntConstant v
  W4.BaseBVRepr w -> AbsBVConstant w v
  W4.BaseBoolRepr -> AbsBoolConstant v
  _ -> AbsUnconstrained repr


absRangeRepr :: AbsRange tp -> W4.BaseTypeRepr tp
absRangeRepr r = case r of
  AbsIntConstant{} -> W4.BaseIntegerRepr
  AbsBVConstant w _ -> W4.BaseBVRepr w
  AbsBoolConstant{} -> W4.BaseBoolRepr
  AbsUnconstrained repr -> repr


instance PP.Pretty (AbsRange tp) where
  pretty ab = case ab of
    AbsIntConstant i -> PP.pretty i
    AbsBVConstant w bv -> W4C.ppConcrete (W4C.ConcreteBV w bv)
    AbsBoolConstant b -> PP.pretty b
    AbsUnconstrained _ -> "⊤"

instance Show (AbsRange tp) where
  show ab = show (PP.pretty ab)

instance TestEquality AbsRange where
  testEquality r1 r2 = case (r1, r2) of
    (AbsIntConstant i1, AbsIntConstant i2) | i1 == i2 -> Just Refl
    (AbsBVConstant w1 bv1, AbsBVConstant w2 bv2)
      | Just Refl <- testEquality w1 w2, bv1 == bv2 -> Just Refl
    (AbsBoolConstant b1, AbsBoolConstant b2) | b1 == b2 -> Just Refl
    (AbsUnconstrained repr1, AbsUnconstrained repr2) -> testEquality repr1 repr2
    _ -> Nothing

instance Eq (AbsRange tp) where
  r1 == r2 = case testEquality r1 r2 of
    Just Refl -> True
    Nothing -> False

-- | Find an 'AbsRange' that represents the intersection of two ranges.
-- In the case where the ranges don't intersect (e.g. they represent two different
-- constant values), the resulting range is unconstrained.
combineAbsRanges :: AbsRange tp -> AbsRange tp -> AbsRange tp
combineAbsRanges r1 r2 = if r1 == r2 then r1 else AbsUnconstrained (absRangeRepr r1)

-- | An abstract value keyed on the macaw type, which defines an independent
-- 'AbsRange' for each component base expression (i.e. for a pointer there is a separate
-- range for the region and offset).
data MacawAbstractValue sym (tp :: MT.Type) where
  MacawAbstractValue ::
      { macawAbsVal :: Ctx.Assignment AbsRange (PSR.CrucBaseTypes (MS.ToCrucibleType tp))
      }
      -> MacawAbstractValue sym tp
  deriving Eq


ppMacawAbstractValue :: MT.TypeRepr tp -> MacawAbstractValue sym tp -> PP.Doc a
ppMacawAbstractValue repr v = case repr of
  MT.BVTypeRepr _w |
    MacawAbstractValue (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs) <- v ->
      PP.pretty regAbs PP.<> "+" PP.<> PP.pretty offsetAbs
  MT.BoolTypeRepr | MacawAbstractValue (Ctx.Empty Ctx.:> bAbs) <- v -> PP.pretty bAbs
  _ -> ""

-- | An abstract value for a pointer, with a separate 'AbsRange' for the region and offset.
data MemAbstractValue sym w where
  MemAbstractValue :: MacawAbstractValue sym (MT.BVType (8 W4.* w)) -> MemAbstractValue sym w


-- | Mapping from locations to abstract values.
data AbstractDomainVals sym arch (bin :: PB.WhichBinary) where
  AbstractDomainVals ::
    { absRegVals :: MM.RegState (MM.ArchReg arch) (MacawAbstractValue sym)
    , absMemVals :: MapF.MapF (PMC.MemCell sym arch) (MemAbstractValue sym)
    , absMaxRegion :: AbsRange W4.BaseIntegerType
    } -> AbstractDomainVals sym arch bin


mergeMemValMaps ::
  OrdF k =>
  MapF.MapF k (MemAbstractValue sym) ->
  MapF.MapF k (MemAbstractValue sym) ->
  MapF.MapF k (MemAbstractValue sym)
mergeMemValMaps m1 m2 = MapF.mergeWithKey (\_ (MemAbstractValue v1) (MemAbstractValue v2) -> Just $ MemAbstractValue (combineAbsVals v1 v2)) id id m1 m2

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationWitherable sym arch (AbstractDomainVals sym arch bin) where
  witherLocation sym vals f = do
     rs <- MM.traverseRegsWith (\r v -> f (PL.Register r) (W4.truePred sym) >>= \case
                           Just _ -> return v
                           Nothing -> return $ noAbsVal (MT.typeRepr r)) (absRegVals vals)
     ms <- forM (MapF.toList (absMemVals vals)) $ \(MapF.Pair (cell@PMC.MemCell{}) v) -> do
       f (PL.Cell cell) (W4.truePred sym) >>= \case
         Just (PL.Cell cell', _) -> return $ MapF.singleton cell' v
         Nothing -> return $ MapF.empty
     let ms' = foldr mergeMemValMaps MapF.empty ms
     return $ AbstractDomainVals rs ms' (absMaxRegion vals)


emptyDomainVals :: PA.ValidArch arch => AbstractDomainVals sym arch bin
emptyDomainVals = AbstractDomainVals
  { absRegVals = MM.mkRegState (\r -> noAbsVal (MT.typeRepr r))
  , absMemVals = MapF.empty
  , absMaxRegion = AbsUnconstrained knownRepr
  }

-- | Intersect the 'AbsRange' entries for each of the components of
-- the given abstract values using 'combineAbsRanges'. 
combineAbsVals ::
  MacawAbstractValue sym tp ->
  MacawAbstractValue sym tp ->
  MacawAbstractValue sym tp
combineAbsVals abs1 abs2 = MacawAbstractValue $
  Ctx.zipWith combineAbsRanges (macawAbsVal abs1) (macawAbsVal abs2)

-- | True if the given abstract value contains no constraints.
isUnconstrained ::
  MacawAbstractValue sym tp -> Bool
isUnconstrained absv = TFC.foldrFC (\v b -> b && case v of { AbsUnconstrained{} -> True; _ -> False} ) True (macawAbsVal absv)

noAbsVal :: MT.TypeRepr tp -> MacawAbstractValue sym tp
noAbsVal repr = case repr of
  MT.BVTypeRepr n ->
    MacawAbstractValue (Ctx.Empty
                        Ctx.:> AbsUnconstrained W4.BaseIntegerRepr
                        Ctx.:> AbsUnconstrained (W4.BaseBVRepr n))
  MT.BoolTypeRepr -> MacawAbstractValue (Ctx.Empty Ctx.:> AbsUnconstrained W4.BaseBoolRepr)
  MT.TupleTypeRepr PL.Nil -> MacawAbstractValue Ctx.Empty
  _ -> panic Solver "noAbsVal" ["Unexpected type for abstract domain"]

-- | Traverse the component expressions of the given 'PSR.MacawRegEntry' and construct
-- a 'MacawAbstractValue' by computing an 'AbsRange' for each component using the given function.
getAbsVal ::
  Monad m =>
  IO.MonadIO m =>
  W4.IsExprBuilder sym =>
  sym ->
  (forall tp'. W4.SymExpr sym tp' -> m (AbsRange tp')) ->
  PSR.MacawRegEntry sym tp ->
  m (MacawAbstractValue sym tp)
getAbsVal _sym f e = case PSR.macawRegRepr e of
  CLM.LLVMPointerRepr{} -> do
    CLM.LLVMPointer region offset <- return $ PSR.macawRegValue e
    regAbs <- f (W4.natToIntegerPure region)
    offsetAbs <- f offset
    return $ MacawAbstractValue (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs)
  CT.BoolRepr -> do
    bAbs <- f (PSR.macawRegValue e)
    return $ MacawAbstractValue (Ctx.Empty Ctx.:> bAbs)
  CT.StructRepr Ctx.Empty -> return $ MacawAbstractValue Ctx.Empty
  _ -> panic Solver "getAbsVal" ["Unexpected type for abstract domain"]

-- | Information about what locations were widened
-- TOOD: add scope
data WidenLocs sym arch =
  WidenLocs
    (Set (Some (MM.ArchReg arch)))
    (Set (Some (PMC.MemCell sym arch)))

instance (W4.IsSymExprBuilder sym, PA.ValidArch arch) => Show (WidenLocs sym arch) where
  show (WidenLocs regs cells) =
    unlines $
      [ unwords (map show (S.toList regs)) ] ++
      [ show (PMC.ppCell c)
      | Some c <- S.toList cells
      ]

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Semigroup (WidenLocs sym arch) where
  (WidenLocs r1 m1) <> (WidenLocs r2 m2) = WidenLocs (r1 <> r2) (m1 <> m2)

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Monoid (WidenLocs sym arch) where
  mempty = WidenLocs mempty mempty

-- | From the result of symbolic execution (in 'PS.SimOutput') we extract any abstract domain
-- information that we can establish for the registers, memory reads and memory writes.
initAbsDomainVals ::
  forall sym arch bin v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  PE.EquivContext sym arch ->
  (forall tp. W4.SymExpr sym tp -> m (AbsRange tp)) ->
  PS.SimOutput sym arch v bin ->
  AbstractDomainVals sym arch bin {- ^ values from pre-domain -} ->
  m (AbstractDomainVals sym arch bin)
initAbsDomainVals sym eqCtx f stOut preVals = do
  foots <- fmap S.toList $ IO.liftIO $ MT.traceFootprint sym (PS.simOutMem stOut)
  -- NOTE: We need to include any cells from the pre-domain to ensure that we
  -- propagate forward any value constraints for memory that is not accessed in this
  -- slice
  let cells = (S.toList . S.fromList) $ map (\(MT.MemFootprint ptr w _dir _cond end) -> Some (PMC.MemCell ptr w end)) foots ++ (MapF.keys $ absMemVals preVals)
  memVals <- fmap MapF.fromList $ forM cells $ \(Some cell) -> do
    absVal <- getMemAbsVal cell
    return (MapF.Pair cell absVal)
  regVals <- MM.traverseRegsWith getRegAbsVal (PS.simOutRegs stOut)
  mr <- f (PS.unSE $ PS.simMaxRegion $ (PS.simOutState stOut))
  return (AbstractDomainVals regVals memVals mr)
  where
    getMemAbsVal ::
      PMC.MemCell sym arch w ->
      m (MemAbstractValue sym w)
    getMemAbsVal cell = do
      val <- IO.liftIO $ PMC.readMemCell sym (PS.simOutMem stOut) cell
      MemAbstractValue <$> getAbsVal sym f (PSR.ptrToEntry val)

    getRegAbsVal ::
      MM.ArchReg arch tp ->
      PSR.MacawRegEntry sym tp ->
      m (MacawAbstractValue sym tp)
    getRegAbsVal r e = case PR.registerCase (PE.eqCtxHDR eqCtx) (PSR.macawRegRepr e) r of
      -- don't include these in the abstract value domain
      PR.RegIP -> return $ noAbsVal (MT.typeRepr r)
      PR.RegSP -> return $ noAbsVal (MT.typeRepr r)
      PR.RegDedicated{} -> return $ noAbsVal (MT.typeRepr r)
      -- for bitvector registers, we don't need to include them
      -- if we don't have a constraint on their offset
      PR.RegBV -> do
        v <- getAbsVal sym f e
        case MT.typeRepr r of
          MT.BVTypeRepr _ |
            MacawAbstractValue (Ctx.Empty Ctx.:> _ Ctx.:> AbsUnconstrained _) <- v -> return $ noAbsVal (MT.typeRepr r)
          _ -> return v
      _ -> getAbsVal sym f e

-- | Convert the abstract domain from an expression into an equivalent 'AbsRange'
-- TODO: Currently this only extracts concrete values
extractAbsRange ::
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.SymExpr sym tp ->
  AbsRange tp
extractAbsRange _sym e = case W4.asConcrete e of
  Just (W4C.ConcreteInteger i) -> AbsIntConstant i
  Just (W4C.ConcreteBV w bv) -> AbsBVConstant w bv
  Just (W4C.ConcreteBool b) -> AbsBoolConstant b
  _ -> AbsUnconstrained (W4.exprType e)

widenAbsDomainVals' ::
  forall sym arch bin v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  AbstractDomainVals sym arch bin {- ^ existing abstract domain that this is augmenting -} ->
  (forall tp. W4.SymExpr sym tp -> m (AbsRange tp)) ->
  PS.SimOutput sym arch v bin ->
  m (AbstractDomainVals sym arch bin, WidenLocs sym arch)
widenAbsDomainVals' sym prev f stOut = CMW.runWriterT $ do
  memVals <- MapF.traverseMaybeWithKey relaxMemVal (absMemVals prev)
  regVals <- PRt.zipWithRegStatesM (absRegVals prev) (PS.simOutRegs stOut) relaxRegVal
  mr' <- CMW.lift $ f (PS.unSE $ PS.simMaxRegion $ (PS.simOutState stOut))
  return $ AbstractDomainVals regVals memVals (combineAbsRanges (absMaxRegion prev) mr')

  where
    getMemAbsVal ::
      PMC.MemCell sym arch w ->
      m (MemAbstractValue sym w)
    getMemAbsVal cell = do
      val <- IO.liftIO $ PMC.readMemCell sym (PS.simOutMem stOut) cell
      MemAbstractValue <$> getAbsVal sym f (PSR.ptrToEntry val)

    relaxMemVal ::
      PMC.MemCell sym arch w ->
      MemAbstractValue sym w {- ^ previous abstract value -} ->
      CMW.WriterT (WidenLocs sym arch) m (Maybe (MemAbstractValue sym w))
    relaxMemVal cell (MemAbstractValue absValPrev) = case isUnconstrained absValPrev of
      True -> return Nothing
      False -> do
        MemAbstractValue absValNew <- CMW.lift $ getMemAbsVal cell
        let absValCombined = combineAbsVals absValNew absValPrev
        unless (absValCombined == absValPrev) $ CMW.tell (WidenLocs mempty (S.singleton (Some cell)))
        case isUnconstrained absValCombined of
          True -> return Nothing
          False -> return $ Just $ MemAbstractValue absValCombined
        
    relaxRegVal ::
      MM.ArchReg arch tp ->
      MacawAbstractValue sym tp {- ^ previous abstract value -} ->
      PSR.MacawRegEntry sym tp ->
      CMW.WriterT (WidenLocs sym arch) m (MacawAbstractValue sym tp)
    relaxRegVal reg absValPrev v = case isUnconstrained absValPrev of
      True -> return absValPrev
      False -> do
        absValNew <- CMW.lift $ getAbsVal sym f v
        let absValCombined = combineAbsVals absValNew absValPrev
        unless (absValCombined == absValPrev) $ CMW.tell (WidenLocs (S.singleton (Some reg)) mempty)
        return absValCombined

widenAbsDomainVals ::
  forall sym arch v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  sym ->
  AbstractDomain sym arch v {- ^ existing abstract domain that this is augmenting -} ->
  (forall tp. W4.SymExpr sym tp -> m (AbsRange tp)) ->
  PS.SimBundle sym arch v ->
  m (AbstractDomain sym arch v, Maybe (WidenLocs sym arch))
widenAbsDomainVals sym prev f bundle = do
  let (PPa.PatchPair absValsO absValsP) = absDomVals prev
  (absValsO', locsO) <- widenAbsDomainVals' sym absValsO f (PS.simOutO bundle)
  (absValsP', locsP) <- widenAbsDomainVals' sym absValsP f (PS.simOutP bundle)
  return $ (prev { absDomVals = PPa.PatchPair absValsO' absValsP' }, Just $ locsO <> locsP)


applyAbsRange ::
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.SymExpr sym tp ->
  AbsRange tp ->
  IO (PAS.AssumptionSet sym)
applyAbsRange sym e rng = case rng of
  AbsIntConstant i -> do
    i' <- W4.intLit sym i
    return $ PAS.exprBinding e i'
  AbsBVConstant w bv -> do
    bv' <- W4.bvLit sym w bv
    return $ PAS.exprBinding e bv'
  AbsBoolConstant True -> return $ PAS.exprBinding e (W4.truePred sym)
  AbsBoolConstant False -> return $ PAS.exprBinding e (W4.falsePred sym)
  AbsUnconstrained{} -> return mempty

absDomainValToAsm ::
  W4.IsSymExprBuilder sym =>
  sym ->
  PE.EquivContext sym arch ->
  PSR.MacawRegEntry sym tp ->
  Maybe (MAS.AbsValue (MM.ArchAddrWidth arch) tp) {- ^ the abstract value of this location according to macaw ('Maybe' because this is only available for registers in pre-domains) -} ->
  MacawAbstractValue sym tp {- ^ the abstract value computed for this location in an earlier widening iteration -} ->
  IO (PAS.AssumptionSet sym)
absDomainValToAsm sym eqCtx e mAbs (MacawAbstractValue absVal) = case PSR.macawRegRepr e of
  CLM.LLVMPointerRepr{} -> do
    CLM.LLVMPointer region offset <- return $ PSR.macawRegValue e
    (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs) <- return $ absVal
    let regionInt = W4.natToIntegerPure region
    -- Override the region with the stack region if the macaw value
    -- domain thinks this is a stack slot
    let regAbs' = case mAbs of
          Just (MAS.StackOffsetAbsVal{}) ->
            (extractAbsRange sym . W4.natToIntegerPure) $ PE.eqCtxStackRegion eqCtx
          _ -> regAbs
    regFrame <- applyAbsRange sym regionInt regAbs'
    offFrame <- applyAbsRange sym offset offsetAbs

    return $ regFrame <> offFrame
  CT.BoolRepr -> do
    b <- return $ PSR.macawRegValue e
    (Ctx.Empty Ctx.:> bAbs) <- return $ absVal
    applyAbsRange sym b bAbs
  CT.StructRepr Ctx.Empty -> return mempty
  _ -> panic Solver "applyAbsDomainVal" ["Unexpected type for abstract domain"]


-- | Construct an 'PS.AssumptionSet' asserting
-- that the values in the given initial state
-- ('PS.SimInput') are necessarily in the given abstract domain
absDomainValsToAsm ::
  forall sym arch v bin.
  sym ->
  PE.EquivContext sym arch ->
  PS.SimState sym arch v bin ->
  Maybe (MAS.AbsBlockState (MC.ArchReg arch)) {- ^ abstract block state according to macaw -} ->
  AbstractDomainVals sym arch bin ->
  IO (PAS.AssumptionSet sym)
absDomainValsToAsm sym eqCtx st absBlockSt vals = PE.eqCtxConstraints eqCtx $ do
  memFrame <- MapF.foldrMWithKey accumulateCell mempty (absMemVals vals)
  regFrame <- fmap PRt.collapse $ PRt.zipWithRegStatesM (PS.simRegs st) (absRegVals vals) $ \r val absVal -> do
    mAbsVal <- case absBlockSt of
      Just ast -> return $ Just ((ast ^. MAS.absRegState) ^. (MM.boundValue r))
      Nothing -> return Nothing
    Const <$> absDomainValToAsm sym eqCtx val mAbsVal absVal
  mrFrame <- IO.liftIO $ applyAbsRange sym (PS.unSE $ PS.simMaxRegion st) (absMaxRegion vals)
  return $ memFrame <> regFrame <> mrFrame
  where
    accumulateCell ::
      PMC.MemCell sym arch w ->
      MemAbstractValue sym w ->
      PAS.AssumptionSet sym ->
      IO (PAS.AssumptionSet sym)
    accumulateCell cell (MemAbstractValue absVal) frame = PE.eqCtxConstraints eqCtx $ do
      val <- IO.liftIO $ PMC.readMemCell sym (PS.simMem st) cell
      frame' <- absDomainValToAsm sym eqCtx (PSR.ptrToEntry val) Nothing absVal
      return $ frame <> frame'

absDomainValsToPostCond ::
  forall sym arch v bin.
  sym ->
  PE.EquivContext sym arch ->
  PS.SimState sym arch v bin ->
  Maybe (MAS.AbsBlockState (MC.ArchReg arch)) {- ^ abstract block state according to macaw -} ->
  AbstractDomainVals sym arch bin ->
  IO (PE.StatePostCondition sym arch v)
absDomainValsToPostCond sym eqCtx st absBlockSt vals = PE.eqCtxConstraints eqCtx $ do
  cells <- mapM (\(MapF.Pair cell v) -> mkCell cell v) (MapF.toList (absMemVals vals))
  memCond' <- WPM.fromList sym WPM.PredConjRepr cells

  stackCond <- fmap WPM.dropUnit $ WPM.traverse memCond' $ \(Some c) p -> do
    let CLM.LLVMPointer cellRegion _ = PMC.cellPtr c
    cond <- W4.natEq sym cellRegion stackRegion
    W4.impliesPred sym cond p

  memCond <- fmap WPM.dropUnit $ WPM.traverse memCond' $ \(Some c) p -> do
    let CLM.LLVMPointer cellRegion _ = PMC.cellPtr c
    cond <- W4.natEq sym cellRegion stackRegion >>= W4.notPred sym
    W4.impliesPred sym cond p

  regFrame <- PRt.zipWithRegStatesM (PS.simRegs st) (absRegVals vals) $ \r val absVal -> do
    mAbsVal <- case absBlockSt of
      Just ast -> return $ Just ((ast ^. MAS.absRegState) ^. (MM.boundValue r))
      Nothing -> return Nothing
    Const <$> absDomainValToAsm sym eqCtx val mAbsVal absVal

  maxRegionCond <- applyAbsRange sym (PS.unSE (PS.simMaxRegion st)) (absMaxRegion vals)
  return $ PE.StatePostCondition (PE.RegisterCondition regFrame) (PE.MemoryCondition stackCond) (PE.MemoryCondition memCond) maxRegionCond
  where
    stackRegion = PE.eqCtxStackRegion eqCtx

    mkCell ::
      PMC.MemCell sym arch w ->
      MemAbstractValue sym w ->
      IO (Some (PMC.MemCell sym arch), W4.Pred sym)
    mkCell cell (MemAbstractValue absVal) = PE.eqCtxConstraints eqCtx $ do
      val <- IO.liftIO $ PMC.readMemCell sym (PS.simMem st) cell
      p <- PAS.toPred sym =<<
        absDomainValToAsm sym eqCtx (PSR.ptrToEntry val) Nothing absVal
      return $ (Some cell, p)

-- | Construct a 'W4.Pred' asserting
-- that the values in the given initial state
-- ('PS.SimInput') are necessarily in the given abstract domain
absDomainValsToPred ::
  forall sym arch v bin.
  W4.IsSymExprBuilder sym =>
  MapF.OrdF (W4.SymExpr sym) =>
  MC.RegisterInfo (MC.ArchReg arch) =>
  sym ->
  PE.EquivContext sym arch ->
  PS.SimState sym arch v bin ->
  Maybe (MAS.AbsBlockState (MC.ArchReg arch)) {- ^ abstract block state according to macaw -} ->
  AbstractDomainVals sym arch bin ->
  IO (W4.Pred sym)
absDomainValsToPred sym eqCtx st absBlockSt vals = do
  asm <- absDomainValsToAsm sym eqCtx st absBlockSt vals
  PAS.toPred sym asm

-- | Construct a 'W4.Pred' asserting that the given
-- abstract domain holds in the pre-state of the given
-- bundle: i.e. the initial original and patched states are  equal
-- up to the equivalence domain, and known constraints on
-- values are initially satisfied.
-- This is intended to be assumed to initially hold when verifying the given
-- 'PS.SimBundle'
absDomainToPrecond ::
  IsSymInterface sym =>
  PA.ValidArch arch =>
  sym ->
  PE.EquivContext sym arch ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  IO (PAS.AssumptionSet sym)
absDomainToPrecond sym eqCtx bundle d = PE.eqCtxConstraints eqCtx $ do
  eqInputs <- PE.getPredomain sym bundle eqCtx (absDomEq d)
  eqInputsPred <- PE.preCondAssumption sym (PS.simInO bundle) (PS.simInP bundle) eqCtx eqInputs
  valsPred <- do
    (predO, predP) <- PPa.forBinsC $ \get -> do
      let absBlockState = PS.simInAbsState (get $ PS.simIn bundle)
      absDomainValsToAsm sym eqCtx (PS.simInState $ get $ PS.simIn bundle) (Just absBlockState) (get $ absDomVals d)
    return $ (predO <> predP)
  return $ (eqInputsPred <> valsPred)
  --PAS.augment sym eqInputsPred valsPred


instance PEM.ExprMappable sym (AbstractDomainVals sym arch bin) where
  mapExpr sym f (AbstractDomainVals regVals memVals mr) = do
    memVals' <- forM (MapF.toAscList memVals) $ \(MapF.Pair cell v) -> do
      cell' <- PEM.mapExpr sym f cell
      return $ MapF.Pair cell' v
    return $ AbstractDomainVals regVals (MapF.fromList memVals') mr

instance PEM.ExprMappable sym (AbstractDomain sym arch v) where
  mapExpr sym f d = do
    domEq <- PEM.mapExpr sym f (absDomEq d)
    vals <- PEM.mapExpr sym f (absDomVals d)
    return $ AbstractDomain domEq vals

ppAbstractDomainVals ::
  forall sym arch bin a.
  ( PA.ValidArch arch
  , W4.IsSymExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  AbstractDomainVals sym arch bin ->
  PP.Doc a
ppAbstractDomainVals d =
  let
    regs =
      [ "== Registers ==" ] ++
      [ PP.pretty s PP.<+> "-->" PP.<+> (ppMacawAbstractValue (MT.typeRepr reg) v)
      | MapF.Pair reg v <- MapF.toList (MM.regStateMap (absRegVals d))
      , Just s <- [PA.fromRegisterDisplay $ PA.displayRegister reg]
      , False <- [isUnconstrained v]
      ]
    mem =
      [ "== Memory ==" ] ++
      [ PMC.viewCell cell $ PMC.ppCell cell PP.<+> "-->" PP.<+> (ppMacawAbstractValue (MT.BVTypeRepr (PMC.bytesRepr cell)) v)
      | MapF.Pair (cell) (MemAbstractValue v) <- MapF.toList (absMemVals d)
      , False <- [isUnconstrained v]
      ]
  in PP.vsep (regs ++ mem)

ppAbstractDomain ::
  forall sym arch v a.
  ( PA.ValidArch arch
  , W4.IsSymExprBuilder sym
  , ShowF (MM.ArchReg arch)
  ) =>
  (W4.Pred sym -> PP.Doc a) ->
  AbstractDomain sym arch v ->
  PP.Doc a
ppAbstractDomain ppPred d =
  PP.vsep $
  [ "== Equivalence Domain =="
  , PED.ppEquivalenceDomain ppPred (absDomEq d)
  , "== Original Value Constraints =="
  , ppAbstractDomainVals (PPa.pOriginal $ absDomVals d)
  , "== Patched Value Constraints =="
  , ppAbstractDomainVals (PPa.pPatched $ absDomVals d)
  ]


data DomainKind = Predomain | Postdomain | ExternalPostDomain
  deriving (Eq, Ord, Show)


instance (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "domain" where
  type TraceNodeType '(sym,arch) "domain" = Some (AbstractDomain sym arch)
  type TraceNodeLabel "domain" = DomainKind
  
  prettyNode (Some absDom) = ppAbstractDomain (\_ -> "") absDom
  nodeTags = [("symbolic", \_ -> "<TODO: domain symbolic summary>")]
