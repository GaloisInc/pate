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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImpredicativeTypes #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Verification.AbstractDomain
  ( AbstractDomain(..)
  , AbstractDomainSpec
  , AbsRange(..)
  , AbstractDomainVals(..)
  , WidenLocs(..)
  , locsToRegsCells
  , DomainKind(..)
  , EventSequence(..)
  , emptyEvents
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
  , domainValsToAbsState
  , singletonDomain
  , zipSingletonDomains
  , widenAbsDomainEqMetaData
  , GetAbsRange
  , mkGetAbsRange
  , batchGetAbsRange
  , getAbsRange
  , getAbsRange1
  ) where

import qualified Prettyprinter as PP

import           Control.Monad.Trans ( lift )
import           Control.Monad ( forM, unless )
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.Writer as CMW
import           Control.Lens ( (^.), (&), (.~) )

import           Data.Functor.Const
import qualified Data.Set as S
import           Data.Set ( Set )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.Pair (fstPair)
import           Data.Parameterized.Classes
import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.List as PL
import           Data.Proxy

import qualified What4.Interface as W4
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Concrete as W4C

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.Simulator.SymSequence (SymSequence, nilSymSequence)

import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.AbsDomain.AbsState as MAS

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PB
import qualified Pate.Block as PBl
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.Condition as PEC
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
import Data.Parameterized (knownSymbol)
import qualified What4.JSON as W4S
import           Data.Aeson ( (.=) )
import qualified Data.Aeson as JSON
import qualified Data.IORef as IO
import qualified Data.Functor.Product as Product

type instance PL.LocationK "memevent" = ()
type instance PL.LocationK "absrange" = W4.BaseType
-- workaround for type families bug
$(return [])
type instance PL.AsK "absrange" tp1 = tp1
type instance PL.AsK "memevent" tp1 = tp1

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
    , absDomEvents :: PPa.PatchPair (EventSequence sym arch)
      -- ^ events that have been accumulated as part of single-sided analysis
      --   should be emptied at synchronization points when the original and patched
      --   sequences are compared for equality
    } -> AbstractDomain sym arch v

instance forall sym arch v. (PSo.ValidSym sym, PA.ValidArch arch) => W4S.W4Serializable sym (AbstractDomain sym arch v) where
  w4Serialize abs_dom = do
    eq_dom <- W4S.w4Serialize (absDomEq abs_dom)
    return $ JSON.object [ "eq_domain" .= eq_dom, "val_domain" .= JSON.String "TODO" ]

instance forall sym arch. (PSo.ValidSym sym, PA.ValidArch arch) => W4S.W4SerializableF sym (AbstractDomain sym arch)


-- | Restrict an abstract domain to a single binary.
singletonDomain ::
  PPa.PatchPairM m =>
  PB.WhichBinaryRepr bin ->
  AbstractDomain sym arch v ->
  m (AbstractDomain sym arch v)
singletonDomain bin d = do
  vals <- PPa.toSingleton bin (absDomVals d)
  evs <- PPa.toSingleton bin (absDomEvents d)
  -- NOTE: the equivalence domain is not separated by patched vs. original entries,
  -- and so we pass it through here unmodified. However it now may contain unbound variables, since
  -- we will have dropped them from the scope.
  -- It's not immediately clear what extra information about these values we would need to propagate.
  return $ AbstractDomain (absDomEq d) vals evs

-- | Zip a pair of abstract domains (original and patched, in any order) into a
--   pair domain.
zipSingletonDomains ::
  PPa.PatchPairM m =>
  CMW.MonadIO m =>
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
  sym ->
  AbstractDomain sym arch v ->
  AbstractDomain sym arch v ->
  m (AbstractDomain sym arch v)
zipSingletonDomains sym d1 d2 = do
  -- resulting equivalence domain is the "intersection" of the input domains
  -- (i.e. the smallest set of values now known to be equivalent)
  d <- CMW.liftIO $ PED.intersect sym (absDomEq d1) (absDomEq d2)
  vals <- PPa.zip (absDomVals d1) (absDomVals d2)
  evs <- PPa.zip (absDomEvents d1) (absDomEvents d2)
  return $ AbstractDomain d vals evs

data EventSequence sym arch (bin :: PB.WhichBinary) =
    EventSequence (SymSequence sym (MT.MemEvent sym (MM.ArchAddrWidth arch)))
  -- ^ partial sequence to handle expressions which could not be re-scoped


instance PEM.ExprMappable sym (EventSequence sym arch bin) where
  mapExpr sym f (EventSequence s) = EventSequence <$> PEM.mapExpr sym f s

emptyEvents :: 
  IO.MonadIO m =>
  sym ->
  m (EventSequence sym arch bin)
emptyEvents sym = EventSequence <$> (IO.liftIO $ nilSymSequence sym)


{-
instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationWitherable sym arch (AbstractDomain sym arch bin) where
  witherLocation sym evs f = case evs of
    NoDeferredEvents -> return NoDeferredEvents
    DeferredEventSequence bin seq -> 
    AbstractDomain <$> PL.witherLocation sym a f <*> PL.witherLocation sym b f


instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationTraversable sym arch (AbstractDomain sym arch bin) where
  traverseLocation sym x f = PL.witherLocation sym x (\loc p -> Just <$> f loc p)

instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym), PA.ValidArch arch) => PL.LocationWitherable sym arch (AbstractDomain sym arch bin) where
  witherLocation sym (AbstractDomain a b) f = AbstractDomain <$> PL.witherLocation sym a f <*> PL.witherLocation sym b f
-}

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
  unsafeCoerceScope (AbstractDomain a b c) = AbstractDomain a b c

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
  testEquality r1 r2 = case compareF r1 r2 of
    EQF -> Just Refl
    _ -> Nothing

instance Eq (AbsRange tp) where
  r1 == r2 = case testEquality r1 r2 of
    Just Refl -> True
    Nothing -> False

instance OrdF AbsRange where
  compareF r1 r2 = case (r1, r2) of
    (AbsIntConstant i1, AbsIntConstant i2) -> fromOrdering $ compare i1 i2
    (AbsBVConstant w1 bv1, AbsBVConstant w2 bv2) ->
      lexCompareF w1 w2 $ (fromOrdering $ compare bv1 bv2)
    (AbsBoolConstant b1, AbsBoolConstant b2) -> fromOrdering $ compare b1 b2
    (AbsUnconstrained repr1, AbsUnconstrained repr2) -> compareF repr1 repr2
    (AbsUnconstrained{}, _) -> GTF
    (_, AbsUnconstrained{}) -> LTF
    _ -> compareF (absRangeRepr r1) (absRangeRepr r2)

instance Ord (AbsRange tp) where
  compare r1 r2 = toOrdering $ compareF r1 r2

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
         Just (cell', _) -> return $ MapF.singleton cell' v
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
    (Set (PL.SomeLocation sym arch))

locsToRegsCells :: (W4.IsSymExprBuilder sym, PA.ValidArch arch) => WidenLocs sym arch -> (Set (Some (MM.ArchReg arch)), Set (Some (PMC.MemCell sym arch)))
locsToRegsCells (WidenLocs locsSet) = 
  let 
    locs = S.toList locsSet
    regs = [ Some r | PL.SomeLocation l <- locs, PL.Register r <- [l] ]
    cells = [ Some c | PL.SomeLocation l <- locs, PL.Cell c <- [l] ]
  in (S.fromList regs, S.fromList cells)

instance (W4.IsSymExprBuilder sym, PA.ValidArch arch) => Show (WidenLocs sym arch) where
  show (locsToRegsCells -> (regs, cells)) =
    unlines $
      [ unwords (map show (S.toList regs)) ] ++
      [ show (PMC.ppCell c)
      | Some c <- S.toList cells
      ]

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Semigroup (WidenLocs sym arch) where
  (WidenLocs locs1) <> (WidenLocs locs2) = WidenLocs (locs1 <> locs2)

instance (OrdF (W4.SymExpr sym), PA.ValidArch arch) => Monoid (WidenLocs sym arch) where
  mempty = WidenLocs mempty

joinMemCellAbsValues ::
  W4.IsSymExprBuilder sym =>
  MapF.MapF (PMC.MemCell sym arch)  (MemAbstractValue s) ->
  MapF.MapF (PMC.MemCell sym arch)  (MemAbstractValue s) ->
  MapF.MapF (PMC.MemCell sym arch)  (MemAbstractValue s)
joinMemCellAbsValues = MapF.mergeWithKey 
 (\_cell (MemAbstractValue v1) (MemAbstractValue v2) -> Just $ MemAbstractValue $ combineAbsVals v1 v2) 
 id 
 id

-- Track if we ever write a concrete value to a given cell
collapseMemCellVals :: 
  forall sym arch.
  W4.IsSymExprBuilder sym => 
  [MapF.Pair (PMC.MemCell sym arch) (MemAbstractValue sym)] -> 
  MapF.MapF (PMC.MemCell sym arch) (Const (Bool, Bool))
collapseMemCellVals = foldr go MapF.empty
  where
    go :: MapF.Pair (PMC.MemCell sym arch)  (MemAbstractValue s) -> MapF.MapF (PMC.MemCell sym arch) (Const (Bool, Bool)) -> MapF.MapF (PMC.MemCell sym arch) (Const (Bool, Bool)) 
    go (MapF.Pair k (MemAbstractValue (MacawAbstractValue (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs)))) m = 
      MapF.insertWith (\(Const (a,b)) (Const (c, d)) -> Const (a || c, b || d)) k 
        (Const (case regAbs of AbsUnconstrained{} -> False; _ -> True, case offsetAbs of AbsUnconstrained{} -> False; _ -> True)) m


-- | From the result of symbolic execution (in 'PS.SimOutput') we extract any abstract domain
-- information that we can establish for the registers, memory reads and memory writes.
initAbsDomainVals ::
  forall sym arch e bin v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  IsTreeBuilder '(sym, arch) e m =>
  sym ->
  PE.EquivContext sym arch ->
  GetAbsRange sym m ->
  PS.SimOutput sym arch v bin ->
  AbstractDomainVals sym arch bin {- ^ values from pre-domain -} ->
  m (AbstractDomainVals sym arch bin)
initAbsDomainVals sym eqCtx getAbs stOut preVals = do
  traceOps <- fmap S.toList $ IO.liftIO $ MT.traceFootprintOps sym (PS.simOutMem stOut)
  -- NOTE: We need to include any cells from the pre-domain to ensure that we
  -- propagate forward any value constraints for memory that is not accessed in this
  -- slice
  let prevCells = (S.toList . S.fromList) $ map fstPair $ filter (\(MapF.Pair _ (MemAbstractValue v)) -> not (isUnconstrained v)) (MapF.toList (absMemVals preVals))

  regVals <- subTree @"loc" "Initial Domain 1" $ do
    MM.traverseRegsWith (\r v -> subTrace (PL.SomeLocation (PL.Register r)) $ getRegAbsVal r v) (PS.simOutRegs stOut)
  
  memPreVals <- subTree @"loc" "Initial Domain 2" $ do
    -- collect models for any cells in the abstract domain with known
    -- concrete values first
    forM prevCells $ \(Some cell) -> subTrace (PL.SomeLocation (PL.Cell cell)) $ do
        absVal <- getMemAbsVal cell
        return $ MapF.Pair cell absVal
    
  -- next we check if the written value was actually concrete, otherwise we can skip these writes
  memTracePrevVals <- subTree @"loc" "Initial Domain 3" $ fmap collapseMemCellVals $ forM traceOps $ \mop@(MT.MemOp ptr _dir _cond (w :: MT.NatRepr w) _val end) -> do
    let cell = PMC.MemCell ptr w end
    subTrace (PL.SomeLocation (PL.Cell cell)) $ getMemOpAbsVal mop
  
  memTraceVals <- subTree @"loc" "Initial Domain 4" $  
    MapF.traverseWithKey (\cell (Const (b1, b2)) -> subTrace (PL.SomeLocation (PL.Cell cell)) $ getCellWithPrevAbsVal cell b1 b2) memTracePrevVals

  let memVals = joinMemCellAbsValues (MapF.fromList memPreVals) memTraceVals

  mr <- subTree @"loc" "Initial Domain 5" $  subTrace (PL.SomeLocation (PL.Named (knownSymbol @"maxRegion"))) $ f (PS.unSE $ PS.simMaxRegion $ (PS.simOutState stOut))
  return (AbstractDomainVals regVals memVals mr)
  where
    f :: forall tp. W4.SymExpr sym tp -> m (AbsRange tp)
    f = getAbsRange1 getAbs

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

    getMemOpAbsVal ::
      MT.MemOp sym (MC.ArchAddrWidth arch) ->
      m (MapF.Pair (PMC.MemCell sym arch) (MemAbstractValue sym))
    getMemOpAbsVal (MT.MemOp ptr _dir _cond (w :: MT.NatRepr w) val end) = do
      let CLM.LLVMPointer region offset = val
      regAbs <- f (W4.natToIntegerPure region)
      offsetAbs <- f offset
      return $ MapF.Pair cell (MemAbstractValue $ MacawAbstractValue (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs))

      where
        cell :: PMC.MemCell sym arch w
        cell = PMC.MemCell ptr w end

    -- extract a final abstract value from a first-pass check
    getCellWithPrevAbsVal ::
      PMC.MemCell sym arch w ->
      Bool ->
      Bool ->
      m (MemAbstractValue sym w)
    getCellWithPrevAbsVal cell regMaybeConcrete offMaybeConcrete = do
      CLM.LLVMPointer mem_region mem_offset <- IO.liftIO $ PMC.readMemCell sym (PS.simOutMem stOut) cell
      -- we avoid checking the actual memory model for concrete values if we didn't originally
      -- write/read a concrete value, since it's unlikely to succeed (outside of strange memory aliasing cases)
      -- since this is an under-approximation it's safe to just leave them as unconstrained
      memRegAbs <- case regMaybeConcrete of
        False -> return $ AbsUnconstrained W4.BaseIntegerRepr
        True -> f (W4.natToIntegerPure mem_region)

      memOffsetAbs <- case offMaybeConcrete of
        False -> return $ AbsUnconstrained (W4.exprType mem_offset)
        True -> f mem_offset
      
      return $ MemAbstractValue $ MacawAbstractValue (Ctx.Empty Ctx.:> memRegAbs Ctx.:> memOffsetAbs)

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
  let maxRegioncombined = combineAbsRanges (absMaxRegion prev) mr'
  unless (maxRegioncombined == (absMaxRegion prev)) $ addLoc (PL.Named (knownSymbol @"maxRegion"))
  return $ AbstractDomainVals regVals memVals maxRegioncombined
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
        unless (absValCombined == absValPrev) $ CMW.tell (WidenLocs (S.singleton (PL.SomeLocation (PL.Cell cell))))
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
        unless (absValCombined == absValPrev) $ CMW.tell (WidenLocs (S.singleton (PL.SomeLocation (PL.Register reg))))
        return absValCombined



widenAbsDomainVals ::
  forall sym arch v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  PPa.PatchPairM m =>
  sym ->
  AbstractDomain sym arch v {- ^ existing abstract domain that this is augmenting -} ->
  (forall tp. W4.SymExpr sym tp -> m (AbsRange tp)) ->
  PS.SimBundle sym arch v ->
  m (AbstractDomain sym arch v, Maybe (WidenLocs sym arch))
widenAbsDomainVals sym prev f bundle = do
  (absVals', locs) <- PPa.forBins2 $ \bin -> do
    absVals <- PPa.get bin $ absDomVals prev
    out <- PPa.get bin $ PS.simOut bundle
    (absVals', locs) <- widenAbsDomainVals' sym absVals f out
    return $ (absVals', Const locs)

  locs' <- PPa.catBins $ \bin -> PPa.getC bin locs

  return $ (prev {absDomVals = absVals'}, Just locs')

addLoc :: (PA.ValidArch arch, W4.IsSymExprBuilder sym, Monad m) => PL.Location sym arch nm k -> CMW.WriterT (WidenLocs sym arch) m ()
addLoc l = CMW.tell (WidenLocs (S.singleton (PL.SomeLocation l)))

widenAbsDomainEqMetaData ::
  forall sym arch v m.
  Monad m =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PA.ValidArch arch =>
  PPa.PatchPairM m =>
  sym ->
  PS.SimScope sym arch v ->
  AbstractDomain sym arch v {- ^ existing abstract domain that this is augmenting -} ->
  (forall tp. W4.SymExpr sym tp -> m (W4.SymExpr sym tp)) {- grounding -} ->
  PS.SimBundle sym arch v ->
  m (AbstractDomain sym arch v, Maybe (WidenLocs sym arch))
widenAbsDomainEqMetaData sym scope prev f bundle = do
  let (oPostState, pPostState) = PS.asStatePair scope (PS.simOut bundle) PS.simOutState
  mrO <- PEM.mapExpr sym f (PS.simMaxRegion oPostState)
  mrP <- PEM.mapExpr sym f (PS.simMaxRegion pPostState)

  let initAbsEq = absDomEq prev
  mrInDom <- PL.namedPred sym =<< (PEM.mapExpr sym f (PED.eqDomainMaxRegion initAbsEq))
  
  (absEq', locs) <- CMW.runWriterT $ do
    case (mrO == mrP) of
      True -> return initAbsEq
      -- max region is not in the domain in this counter-example, so 
      -- this can't be the source of an inequality
      False | Just False <- W4.asConstantPred mrInDom -> return initAbsEq
      False -> do
        addLoc $ PL.namedPredLoc (PED.eqDomainMaxRegion initAbsEq)
        return $ initAbsEq { PED.eqDomainMaxRegion = PL.knownNamedPred (W4.falsePred sym) }
  return $ (prev { absDomEq = absEq' }, Just locs)

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

macawAbsValueToAbsValue ::
  PA.ValidArch arch =>
  f arch ->
  MT.TypeRepr tp ->
  MacawAbstractValue sym tp ->
  MAS.AbsValue (MM.ArchAddrWidth arch) tp
macawAbsValueToAbsValue _ repr (MacawAbstractValue absVal) = case repr of
  MT.BVTypeRepr{} | (Ctx.Empty Ctx.:> regAbs Ctx.:> offsetAbs) <- absVal ->
    case (regAbs, offsetAbs) of
      (AbsIntConstant 0, AbsBVConstant _w i) -> MAS.FinSet (S.singleton (BV.asUnsigned i))
      -- FIXME: add StackOffset and CodePointers here
      _ -> MAS.TopV
  MT.BoolTypeRepr | (Ctx.Empty Ctx.:> bAbs) <- absVal ->
    case bAbs of
      AbsBoolConstant b -> MAS.BoolConst b
      _ -> MAS.TopV
  _ -> MAS.TopV


domainValsToAbsState ::
  forall sym arch bin.
  PA.ValidArch arch =>
  AbstractDomainVals sym arch bin ->
  PBl.AbsStateOverride arch
domainValsToAbsState d =
  MapF.mapMaybeWithKey  (\r _ ->
    let
      macawVal = (absRegVals d) ^. MM.boundValue r
    in case macawAbsValueToAbsValue (Proxy @arch) (MT.typeRepr r) macawVal of
      MAS.TopV -> Nothing
      v | PA.discoveryRegister r -> Just v
      _ -> Nothing
    ) (MM.archRegSet @(MM.ArchReg arch))

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

  maxRegionCond <- PAS.NamedAsms <$> applyAbsRange sym (PS.unSE (PS.simMaxRegion st)) (absMaxRegion vals)
  -- No value assumptions about the stack base
  stackBaseCond <- return $ PAS.NamedAsms mempty

  return $ PE.StatePostCondition (PEC.RegisterCondition regFrame) (PE.MemoryCondition stackCond) (PE.MemoryCondition memCond) maxRegionCond stackBaseCond
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
  PS.SimScope sym arch v ->
  PE.EquivContext sym arch ->
  PS.SimBundle sym arch v ->
  AbstractDomain sym arch v ->
  IO (PAS.AssumptionSet sym)
absDomainToPrecond sym scope eqCtx bundle d = PE.eqCtxConstraints eqCtx $ do
  eqInputs <- PE.getPredomain sym scope bundle eqCtx (absDomEq d)
  eqInputsPred <- PE.preCondAssumption sym scope (PS.simIn bundle) eqCtx eqInputs
  valsPred <- PPa.runPatchPairT $ PPa.catBins $ \bin -> do
    input <- PPa.get bin (PS.simIn bundle)
    let absBlockState = PS.simInAbsState input
    absDomVals' <- PPa.get bin (absDomVals d)
    lift $ absDomainValsToAsm sym eqCtx (PS.simInState input) (Just absBlockState) absDomVals'
  return $ (eqInputsPred <> valsPred)

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
    events <- PEM.mapExpr sym f (absDomEvents d)
    return $ AbstractDomain domEq vals events

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
  , PED.ppEquivalenceDomain ppPred (\r -> fmap PP.pretty (PA.fromRegisterDisplay (PA.displayRegister r))) (absDomEq d)
  ] ++
  (PPa.catBinsPure $ \bin -> do
    vals <- PPa.get bin (absDomVals d)
    let header = "==" PP.<+> PP.pretty bin PP.<+> "Value Constraints" PP.<+> "=="
    return $ [header, ppAbstractDomainVals vals])

instance (PA.ValidArch arch, W4.IsSymExprBuilder sym) => Show (AbstractDomain sym arch v) where
  show a = show (ppAbstractDomain (\_ -> "") a)

data DomainKind = Predomain | Postdomain | ExternalPostDomain
  deriving (Eq, Ord, Show)


ppDomainKind ::
  DomainKind -> PP.Doc a
ppDomainKind = \case
  Predomain -> "Predomain"
  Postdomain -> "Intermediate postdomain"
  ExternalPostDomain -> "Postdomain"

instance JSON.ToJSON DomainKind where
  toJSON dk = JSON.toJSON (show dk)

instance W4S.W4Serializable sym DomainKind

instance (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "domain" where
  type TraceNodeType '(sym,arch) "domain" = Some (AbstractDomain sym arch)
  type TraceNodeLabel "domain" = DomainKind
  
  prettyNode lbl (Some absDom) = ppDomainKind lbl PP.<> PP.line PP.<> ppAbstractDomain (\_ -> "") absDom
  nodeTags = [(Summary, \lbl _ -> ppDomainKind lbl),
              (Simplified, \lbl _ -> ppDomainKind lbl),
              ("symbolic", \lbl (Some absDom) -> ppDomainKind lbl PP.<> PP.line PP.<> ppAbstractDomain W4.printSymExpr absDom),
              (Simplified_Detail, \lbl (Some absDom) -> 
                    PP.vsep
                      [ ppDomainKind lbl
                      , PED.ppEquivalenceDomain (\_ -> "") (\r -> fmap PP.pretty (PA.fromRegisterDisplay (PA.displayRegister r))) (absDomEq absDom)
                      ])
             ]
  jsonNode sym lbl (Some abs_dom) = do 
    abs_dom_json <- W4S.w4ToJSON sym abs_dom
    return $ JSON.object [ "abstract_domain" .= abs_dom_json, "kind" .= (show lbl) ]

-- simplified variant of domain trace node
-- currently only displays equivalence domain
instance (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "simpledomain" where
  type TraceNodeType '(sym,arch) "simpledomain" = Some (AbstractDomain sym arch)
  type TraceNodeLabel "simpledomain" = DomainKind
  
  prettyNode lbl (Some absDom) =
    PP.vsep
      [ PP.pretty (show lbl)
      , PED.ppEquivalenceDomain (\_ -> "") (\r -> fmap PP.pretty (PA.fromRegisterDisplay (PA.displayRegister r))) (absDomEq absDom)
      ]
  nodeTags = [(Summary, \lbl _ -> ppDomainKind lbl),
              (Simplified, \lbl _ -> ppDomainKind lbl)]


-- MemEvent location (should be moved to MemTrace)
instance PL.IsLocation sym arch "memevent" where
  type LocationType sym arch "memevent" = Const (MT.MemEvent sym (MM.ArchAddrWidth arch))
  type Valid sym arch "memevent" = (PSo.ValidSym sym, PA.ValidArch arch)
  mapLocExpr sym f r = PEM.mapExpr sym f r
  prettyLoc (Const r) = MT.prettyMemEvent r
  ordFLoc a@(Const x) b@(Const y) = PL.withUnitEq a b $ fromOrdering (compare x y)

pattern MemEvent :: 
  forall sym arch nm k. () => (PL.Valid sym arch nm, nm ~ "memevent") => 
  MT.MemEvent sym (MM.ArchAddrWidth arch) -> 
  PL.Location sym arch nm (k :: (PL.LocationK nm))
pattern MemEvent r <- ((\l -> PL.asProof @"memevent" l) -> PL.LocPrf (Const r))
  where
    MemEvent r = PL.Location @"memevent" (Const r)

instance (PSo.ValidSym sym, PA.ValidArch arch) => PL.LocationWitherable sym arch (EventSequence sym arch bin) where
  witherLocation sym (EventSequence s) f =
      EventSequence <$> (PEM.updateFilterSeq sym $ \x -> do
        f (MemEvent x) (W4.truePred sym) >>= \case
          Just ((Const x'), p') -> return $ (Just x', p')
          Nothing -> return $ (Nothing, W4.falsePred sym)) s

newtype GetAbsRange sym m = GetAbsRange { getAbsRange :: forall ctx. Ctx.Assignment (W4.SymExpr sym) ctx -> m (Ctx.Assignment AbsRange ctx) }


-- FIXME: Move this to Parameterized

data WithEmbedding v ctx = forall sub. WithEmbedding (Ctx.CtxEmbedding sub ctx) (v sub)

type MaybeF f = PPa.LiftF Maybe f

-- Strip the 'Nothing' results from an 'Assignment'
flattenMaybeCtx ::
  Ctx.Assignment (MaybeF f) ctx ->
  (WithEmbedding (Ctx.Assignment f) ctx)
flattenMaybeCtx = \case
  Ctx.Empty -> WithEmbedding (Ctx.CtxEmbedding Ctx.zeroSize Ctx.Empty) Ctx.Empty
  xs Ctx.:> x | WithEmbedding embed xs' <- flattenMaybeCtx xs -> case x of
    PPa.LiftF (Just x') -> WithEmbedding (Ctx.extendEmbeddingBoth embed) (xs' Ctx.:> x')
    PPa.LiftF Nothing -> WithEmbedding (Ctx.extendEmbeddingRight embed) xs'

dropEmbedding :: Ctx.CtxEmbedding (sub Ctx.::> tp) ctx -> Ctx.CtxEmbedding sub ctx
dropEmbedding (Ctx.CtxEmbedding sz (idxs Ctx.:> _)) = Ctx.CtxEmbedding sz idxs

reverseEmbedding :: 
  Ctx.CtxEmbedding sub ctx ->
  Ctx.Assignment f sub ->
  Ctx.Assignment (MaybeF f) ctx
reverseEmbedding embed@(Ctx.CtxEmbedding sz idxs) asn = case (idxs, asn) of
    (Ctx.Empty, Ctx.Empty) -> Ctx.replicate sz (PPa.LiftF Nothing)
    (_ Ctx.:> idx, asn' Ctx.:> x') -> 
      let res = reverseEmbedding (dropEmbedding embed) asn'
      in  res & (ixF idx) .~ PPa.LiftF (Just x')

mapMaybeCtx :: 
  forall f g ctx m.
  Monad m =>
  (forall sub_ctx. Ctx.CtxEmbedding sub_ctx ctx -> Ctx.Assignment f sub_ctx -> m (Ctx.Assignment g sub_ctx)) ->
  Ctx.Assignment (MaybeF f) ctx ->
  m (Ctx.Assignment (MaybeF g) ctx)
mapMaybeCtx f asn | WithEmbedding embed asn' <- flattenMaybeCtx asn = do
  asn'' <- f embed asn'
  return $ reverseEmbedding embed asn''

partitionCtx ::
  Monad m =>
  (forall tp. f tp -> m (Either (g tp) (h tp))) ->
  Ctx.Assignment f ctx ->
  m (Ctx.Assignment (MaybeF g) ctx, Ctx.Assignment (MaybeF h) ctx)
partitionCtx part = \case
  Ctx.Empty -> return (Ctx.Empty, Ctx.Empty)
  xs Ctx.:> x -> part x >>= \case
    Left g -> partitionCtx part xs >>= \(gs,hs) -> return (gs Ctx.:> PPa.LiftF (Just g), hs Ctx.:> PPa.LiftF Nothing)
    Right h -> partitionCtx part xs >>= \(gs,hs) -> return (gs Ctx.:> PPa.LiftF Nothing, hs Ctx.:> PPa.LiftF (Just h))


mkGetAbsRange :: 
  forall m sym.
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  (forall ctx. Ctx.Assignment (W4.SymExpr sym) ctx -> m (Ctx.Assignment AbsRange ctx)) ->
  m (GetAbsRange sym m)
mkGetAbsRange f = do
  (cache :: IO.IORef (MapF.MapF (W4.SymExpr sym) (AbsRange)))  <- IO.liftIO $ IO.newIORef MapF.empty
  let 
    getCache :: forall tp. W4.SymExpr sym tp -> m (Either (W4.SymExpr sym tp) (AbsRange tp))
    getCache e = do
      m <- IO.liftIO $ IO.readIORef cache
      case MapF.lookup e m of
        Just a -> return $ Right a
        Nothing -> return $ Left e

  return $ GetAbsRange $ \es -> do
    (es_uncached, as_cached) <- partitionCtx getCache es
    as_result <- mapMaybeCtx (\_ -> f) es_uncached
    let 
      go :: forall tp. MaybeF AbsRange tp -> MaybeF AbsRange tp -> AbsRange tp
      go a b = case (a, b) of
          (PPa.LiftF (Just a'), _) -> a'
          (_, PPa.LiftF (Just a')) -> a'
          _ -> error $ "mapMaybeCtx: impossible 'Nothing' result"
    return $ Ctx.zipWith go as_result as_cached

getAbsRange1 :: Monad m => GetAbsRange sym m -> (forall tp. W4.SymExpr sym tp -> m (AbsRange tp))
getAbsRange1 f = (\e -> getAbsRange f (Ctx.singleton e) >>= \case (Ctx.Empty Ctx.:> a) -> return a)

-- | Batch the concretization of many values at once, given a function 'f' that
--   uses a 'GetAbsRange' multiple times to concretize many individual expressions.
--
--   This runs the given 'f' twice, once with a dummy 'GetAbsRange' in order to collect
--   the values that need to be concretized. Once collected, they are all concretized
--   at once, and then these concrete values are used on the second run of 'f'.
batchGetAbsRange :: 
  forall sym m a.
  IO.MonadIO m => 
  W4.IsSymExprBuilder sym =>
  GetAbsRange sym m -> 
  (GetAbsRange sym m -> m a) -> 
  m a
batchGetAbsRange mkabs f = do
  (ref :: IO.IORef (MapF.MapF (W4.SymExpr sym) (PPa.LiftF Maybe AbsRange)))  <- IO.liftIO $ IO.newIORef MapF.empty
  let 
    dummy1 :: forall tp. W4.SymExpr sym tp -> m (AbsRange tp)
    dummy1 e = do
      IO.liftIO $ IO.modifyIORef ref (MapF.insert e (PPa.LiftF Nothing))
      return $ AbsUnconstrained (W4.exprType e)

    dummy :: GetAbsRange sym m
    dummy = GetAbsRange $ TFC.traverseFC dummy1
  _ <- f dummy
  m <- IO.liftIO $ IO.readIORef ref
  Some ctx <- return $ Ctx.fromList (MapF.keys m)
  ctx' <- getAbsRange mkabs ctx

  to_exprs1 <- Ctx.traverseWithIndex (\idx v -> return $ Product.Pair v (ctx' Ctx.! idx)) ctx
  let 
    to_exprs :: MapF.MapF (W4.SymExpr sym) AbsRange
    to_exprs = MapF.fromList $ TFC.toListFC (\(Product.Pair v a) -> MapF.Pair v a) to_exprs1

    cached1 :: forall tp. W4.SymExpr sym tp -> m (AbsRange tp)
    cached1 e = case MapF.lookup e to_exprs of
      Just a -> return a 
      Nothing -> getAbsRange1 mkabs e

    cached :: GetAbsRange sym m
    cached = GetAbsRange $ TFC.traverseFC cached1
  
  f cached


