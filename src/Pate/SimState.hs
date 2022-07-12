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
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}


module Pate.SimState
  ( -- simulator state
    SimState(..)
  , StackBase(..)
  , SimInput(..)
  , SimOutput(..)
  , type VarScope
  , SimScope
  , scopeAsm
  , scopeVars
  , Scoped(..)
  , ScopedExpr
  , unSE
  , scopedExprMap
  , liftScope0
  , liftScope2
  , concreteScope
  , SimSpec
  , freshSimSpec
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
  , ExprRewrite
  , getExprRewrite
  , applyExprRewrite
  -- assumption frames
  , AssumptionSet
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
import           Data.Proxy

import qualified Control.Monad.IO.Class as IO
import           Control.Monad ( forM )
import           Control.Monad ( forM )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( Pair(..) )
import qualified Data.Parameterized.TraversableF as TF
import           Data.Functor.Const
import           Data.List ( find )

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.AbsDomain.AbsState as MAS

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT

import qualified What4.Interface as W4
import qualified What4.Concrete as W4
import qualified What4.Expr.Builder as W4B

import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.PatchPair as PPa
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimulatorRegisters as PSR
import           What4.ExprHelpers
import qualified Data.Parameterized.SetF as SetF

------------------------------------
-- Crucible inputs and outputs

-- | Points to the base of the stack. In any given context this will always be
-- "free" as the base of the stack is always abstract, but it is rebound to account
-- for changes to the stack pointer when moving between scopes.
type StackBase sym arch v = ScopedExpr sym (W4.BaseBVType (MM.ArchAddrWidth arch)) v

data SimState sym arch (v :: VarScope) (bin :: PBi.WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
  , simStackBase :: StackBase sym arch v
  }

data SimInput sym arch v bin = SimInput
  {
    simInState :: SimState sym arch v bin
  , simInBlock :: PB.ConcreteBlock arch bin
  , simInAbsState :: MAS.AbsBlockState (MM.ArchReg arch)
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




data AssumptionSet sym (v :: VarScope) where
  AssumptionSet ::
    { asmPreds :: ExprSet sym W4.BaseBoolType
    -- | equivalence on sub-expressions. In the common case where an expression maps
    -- to a single expression (i.e. a singleton 'ExprSet') we can apply the rewrite
    -- inline.
    , asmBinds :: MapF.MapF (W4.SymExpr sym) (ExprSet sym)
    } -> AssumptionSet sym v

instance OrdF (W4.SymExpr sym) => Semigroup (AssumptionSet sym v) where
  asm1 <> asm2 = let
    preds = (asmPreds asm1) <> (asmPreds asm2)
    binds = mergeExprSetMap (Proxy @sym) (asmBinds asm1) (asmBinds asm2)
    in AssumptionSet preds binds

instance Show (AssumptionSet sym v) where
  show asms = "Assumptions"

mapExprSet ::
  OrdF (W4.SymExpr sym) =>
  Monad m =>
  sym ->
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  ExprSet sym tp ->
  m (ExprSet sym tp)
mapExprSet _sym f s = SetF.fromList <$> traverse f (SetF.toList s)

mergeExprSetMap ::
  OrdF (W4.SymExpr sym) =>
  Proxy sym ->
  MapF.MapF (W4.SymExpr sym) (ExprSet sym) ->
  MapF.MapF (W4.SymExpr sym) (ExprSet sym) ->
  MapF.MapF (W4.SymExpr sym) (ExprSet sym)
mergeExprSetMap _sym map1 map2 =
  MapF.mergeWithKey
    (\_ eset1 eset2 -> Just (eset1 <> eset2))
    id
    id
    map1
    map2

instance OrdF (W4.SymExpr sym) => PEM.ExprMappable sym (AssumptionSet sym v) where
  mapExpr sym f (AssumptionSet ps bs) = do
    ps' <- mapExprSet sym f ps
    bs' <- forM (MapF.toList bs) $ \(MapF.Pair k v) -> do
      k' <- f k
      v' <- mapExprSet sym f v
      return $ MapF.singleton k' v'
    return $ AssumptionSet ps' (foldr (mergeExprSetMap (Proxy @sym)) MapF.empty bs')

instance Scoped (AssumptionSet sym) where
  unsafeCoerceScope (AssumptionSet a b) = AssumptionSet a b

instance OrdF (W4.SymExpr sym) => Monoid (AssumptionSet sym v) where
  mempty = AssumptionSet mempty MapF.empty

-- | Lift an expression binding environment into an assumption frame
bindingToFrame ::
  forall sym v.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  ExprBindings sym ->
  AssumptionSet sym v
bindingToFrame binds = AssumptionSet { asmPreds = mempty, asmBinds = MapF.map SetF.singleton binds }

exprBinding ::
  forall sym v tp.
  W4.IsSymExprBuilder sym =>
  -- | source expression
  W4.SymExpr sym tp ->
  -- | target expression
  W4.SymExpr sym tp ->
  AssumptionSet sym v
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
  IO (AssumptionSet sym v)
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

-- TODO: this is generally unsafe, since we don't check that the incoming
-- predicate actually respects the variable scope 'v'
frameAssume ::
  forall sym v.
  W4.IsSymExprBuilder sym =>
  W4.Pred sym ->
  AssumptionSet sym v
frameAssume p = AssumptionSet (SetF.singleton p) MapF.empty

getUniqueBinding ::
  forall sym v tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  AssumptionSet sym v ->
  W4.SymExpr sym tp ->
  Maybe (W4.SymExpr sym tp)
getUniqueBinding sym asm e = case MapF.lookup e (asmBinds asm) of
  Just es
    | SetF.size es == 1
    , [e'] <- SetF.toList es -> Just e'
  Just es -> SetF.lookupMin $ SetF.filter (isJust . W4.asConcrete) es
  _ -> case W4.exprType e of
    W4.BaseBoolRepr | isAssumedPred asm e -> Just $ W4.truePred sym
    _ -> Nothing

-- | Compute a predicate that collects the individual assumptions in the frame, including
-- equality on all bindings.
getAssumedPred ::
  forall sym v.
  W4.IsSymExprBuilder sym =>
  sym ->
  AssumptionSet sym v ->
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
  forall sym v.
  W4.IsSymExprBuilder sym =>
  AssumptionSet sym v ->
  W4.Pred sym ->
  Bool
isAssumedPred frame asm = SetF.member asm (asmPreds frame)

-- | Explicitly rebind any known sub-expressions that are in the frame.
rebindWithFrame ::
  forall sym v t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  AssumptionSet sym v ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame sym asm e = do
  cache <- freshVarBindCache
  rebindWithFrame' sym cache asm e

rebindWithFrame' ::
  forall sym v t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  VarBindCache sym ->
  AssumptionSet sym v ->
  W4B.Expr t tp ->
  IO (W4B.Expr t tp)
rebindWithFrame' sym cache asm = rewriteSubExprs' sym cache (getUniqueBinding sym asm)



-- | An empty type represent the kind for a shadow "variable scope" type parameter.
-- This parameter tracks the scope of the bound variables that might appear in the
-- inner What4 expressions anywhere in a datatype.
-- This type variable is introduced when interpreting a 'SimSpec', which existentially
-- quantifies over 'v'.
-- The intended invariant is that each 'SimSpec' contains a distinct (fresh) 'SimBoundVars'
-- which is associated with some scope parameter 'v'.
-- Any type tagged with the same 'v' should only include
-- bound variables from this initial 'SimBoundVars'.
-- When values need to be converted from one scope to another (e.g. when instiantiating
-- their bound variables with 'bindSpec'), we can "unsafely" coerce the scope
-- from one type to another via 'unsafeCoerceScope'.
-- TODO: A safe variant of 'unsafeCoerceScope' could perform a runtime check to
-- ensure that the resulting value is well-scoped.
data VarScope

-- | A 'Scoped' type is parameterized by a phantom 'VarScope' type variable, used
-- to track the scope of its inner bound variables.
class Scoped f where
  -- | Unsafely change the variable scope parameter for an instance of 'f'.
  -- This should be a no-op and only used to make types match up where needed.
  -- It is the responsibility of the user to ensure that this is only applied
  -- in cases where 'f' has been rewritten to only contain bound variables
  -- in the target scope.
  -- TODO: We can check this statically to add a safe variant.
  unsafeCoerceScope :: forall (v :: VarScope) v'. f v -> f v'

-- | A lambda abstraction over 'f', which is parameterized by a variable scope.
-- A 'SimSpec' can be interpreted via 'viewSpec' or modified via 'forSpec'.
-- The 'VarScope' that 'f' is parameterized over is existentially quantified
-- within the 'SimSpec', and is used to track the scope of the
-- bound variables (provided as 'SimVars') within the closure (i.e. retaining
-- the fact that the provided 'SimVars' represent the bound variables appearing
-- in 'f')
data SimSpec sym arch (f :: VarScope -> DK.Type) = forall v.
  SimSpec
    {
      _specScope :: SimScope sym arch v
    , _specBody :: f v
    }

data SimScope sym arch v =
  SimScope
    { scopeBoundVars :: PPa.PatchPair (SimBoundVars sym arch v)
    , scopeAsm :: AssumptionSet sym v
    }

scopeVars :: SimScope sym arch v -> PPa.PatchPair (SimVars sym arch v)
scopeVars scope = TF.fmapF boundVarsAsFree (scopeBoundVars scope)

-- | Create a 'SimSpec' with "fresh" bound variables
freshSimSpec ::
  forall sym arch f m.
  Monad m =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  -- | These must all be fresh variables
  (forall bin tp. PBi.WhichBinaryRepr bin -> MM.ArchReg arch tp -> m (PSR.MacawRegVar sym tp)) ->
  -- | This must be a fresh MemTrace
  (forall bin. PBi.WhichBinaryRepr bin -> m (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))) ->
  -- | Fresh stack base
  (forall bin v. PBi.WhichBinaryRepr bin -> m (StackBase sym arch v)) ->
  -- | Produce the body of the 'SimSpec' given the initial variables
  (forall v. PPa.PatchPair (SimVars sym arch v) -> m (AssumptionSet sym v, (f v))) ->
  m (SimSpec sym arch f)
freshSimSpec mkReg mkMem mkStackBase mkBody = do
  vars <- PPa.forBins' $ \bin -> do
    regs <- MM.mkRegStateM (mkReg bin)
    mem <- mkMem bin
    sb <- mkStackBase bin
    return $ SimBoundVars regs (SimState mem (MM.mapRegsWith (\_ -> PSR.macawVarEntry) regs) sb)
  (asm, body) <- mkBody (TF.fmapF boundVarsAsFree vars)
  return $ SimSpec (SimScope vars asm) body

-- | Project out the bound variables with an arbitrary scope.
-- This is a private function, since as we want to consider the
-- 'SimBoundVars' of the 'SimSpec' to be an implementation detail.
viewSpecVars ::
  SimSpec sym arch f ->
  (forall v. PPa.PatchPair (SimBoundVars sym arch v) -> a) ->
  a
viewSpecVars (SimSpec (SimScope vars _) _) f = f vars

-- | Project out the body with an arbitrary scope.
viewSpecBody ::
  SimSpec sym arch f ->
  (forall v. f v -> a) ->
  a
viewSpecBody (SimSpec _ body) f = f body

-- | Interpret a 'SimSpec' by viewing its initial bound variables as a
-- 'SimVars' pair, and its body, with respect to an arbitrary scope.
-- Note that we
-- avoid exposing 'SimBoundVars' here by only providing 'SimVars'
viewSpec ::
  SimSpec sym arch f ->
  (forall v. SimScope sym arch v -> f v -> a) ->
  a
viewSpec (SimSpec scope body) f = f scope body

-- | Transform a 'SimSpec' by viewing its initial bound variables as a
-- 'SimVars' pair, with respect to an arbitrary scope. Note that we
-- avoid exposing 'SimBoundVars' here by only providing 'SimVars'
forSpec ::
  Applicative m =>
  SimSpec sym arch f ->
  (forall v. SimScope sym arch v -> f v -> m (g v)) ->
  m (SimSpec sym arch g)
forSpec (SimSpec scope body) f = SimSpec <$> pure scope <*> f scope body


-- | Unsafely coerce the body of a spec to have any scope.
-- After this is used, the variables in the resulting 'f' should
-- be rebound to actually be properly scoped to 'v'.
unsafeCoerceSpecBody ::
  Scoped f =>
  SimSpec sym arch f -> f v
unsafeCoerceSpecBody (SimSpec _ body) = unsafeCoerceScope body


unsafeCoerceSpecAsm ::
  Scoped f =>
  SimSpec sym arch f -> AssumptionSet sym v
unsafeCoerceSpecAsm (SimSpec (SimScope _ asm) _) = unsafeCoerceScope asm

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

-- | "Free" bound variables representing the formal variables for some
-- expression-containing value.
-- TODO: Ideally the structure of this could be hidden, since 'SimSpec'
-- should fully abstract its internal representation of the bound variables.
data SimBoundVars sym arch v bin = SimBoundVars
  {
    simBoundVarRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegVar sym)
  , simBoundVarState :: SimState sym arch v bin
  }

-- | A value assignment for the bound variables of a 'SimSpec'. These may
-- contain arbitrary What4 expressions (e.g. the result of symbolic execution).
data SimVars sym arch v bin = SimVars
  {
    simVarState :: SimState sym arch v bin
  }



-- | Project out the initial values for the variables in 'SimBoundVars'.
-- This is roughly analagous to converting a What4 bound variable into an expression.
boundVarsAsFree :: SimBoundVars sym arch v bin -> SimVars sym arch v bin
boundVarsAsFree bv = SimVars (simBoundVarState bv)

mkVarBinds ::
  forall sym arch v v' bin.
  HasCallStack =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  W4.IsExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  SimBoundVars sym arch v bin ->
  MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  StackBase sym arch v' ->
  IO (ExprRewrite sym v v')
mkVarBinds sym simVars mem regs sb = do
  let
    memVar = MT.memState $ simMem $ simBoundVarState simVars
    regVars = simBoundVarRegs simVars
    stackVar = simStackBase $ simBoundVarState simVars
    stackBinds = singleRewrite' (unSE stackVar) (unSE sb)
    
    regBinds = MM.zipWithRegState (\(PSR.MacawRegVar _ vars) val -> PSR.MacawRegVar val vars) regVars regs
  regVarBinds <- fmap PRt.collapse $ PRt.zipWithRegStatesM regVars regs $ \_ (PSR.MacawRegVar _ vars) val -> do
    case PSR.macawRegRepr val of
      CLM.LLVMPointerRepr{} -> do
        CLM.LLVMPointer region off <- return $ PSR.macawRegValue val
        (Ctx.Empty Ctx.:> regVar Ctx.:> offVar) <- return $ vars
        iRegion <- W4.natToInteger sym region
        return $ Const $ singleRewrite' regVar iRegion <> singleRewrite' offVar off
      CT.BoolRepr -> do
        Ctx.Empty Ctx.:> var <- return vars
        return $ Const $ singleRewrite' var (PSR.macawRegValue val)
      CT.StructRepr Ctx.Empty -> return $ Const mempty
      repr -> error ("mkVarBinds: unsupported type " ++ show repr)

  return $ (fromBindings (MT.mkMemoryBinding memVar mem)) <> regVarBinds <> stackBinds

newtype ExprList sym tp = ExprList [W4.SymExpr sym tp]
  deriving (Monoid, Semigroup)

-- | Wrapped expression bindings that convert expressions from one
-- scope to another
data ExprRewrite sym (v :: VarScope) (v' :: VarScope) = 
      ExprRewrite (Maybe (VarBindCache sym)) (MapF.MapF (W4.SymExpr sym) (ExprList sym))
 
instance OrdF (W4.SymExpr sym) => Semigroup (ExprRewrite sym v v') where
  rew1 <> rew2 = case (rew1, rew2) of
    (ExprRewrite _ binds1, ExprRewrite _ binds2) ->
      ExprRewrite Nothing (MapF.mergeWithKey (\_ a1 a2 -> Just (a1 <> a2)) id id binds1 binds2)

instance OrdF (W4.SymExpr sym) => Monoid (ExprRewrite sym v v') where
  mempty = ExprRewrite Nothing MapF.empty

-- UNSAFE: assumes that the incoming expressions adhere to the given scopes
singleRewrite' ::
  W4.SymExpr sym tp ->
  W4.SymExpr sym tp ->
  ExprRewrite sym v v'
singleRewrite' e1 e2 = ExprRewrite Nothing (MapF.singleton e1 (ExprList [e2]))

-- UNSAFE: assumes that the incoming expressions adhere to the given scopes
fromBindings ::
  ExprBindings sym -> ExprRewrite sym v v'
fromBindings binds = ExprRewrite Nothing (TF.fmapF (\e -> ExprList [e]) binds)

lookupExprList ::
  W4.IsSymExprBuilder sym =>
  MapF.MapF (W4.SymExpr sym) (ExprList sym) ->
  W4.SymExpr sym tp ->
  Maybe (W4.SymExpr sym tp)
lookupExprList binds e = case MapF.lookup e binds of
  -- if it's a singleton then just return that
  Just (ExprList [e']) -> Just e'
  -- if there are multiple entries
  -- first try to find any constants and bind to the first one
  Just (ExprList es)
    | Just e' <- find (isJust . W4.asConcrete) es -> Just e'
  -- otherwise just pick the first element
  Just (ExprList (e' : _)) -> Just e'
  _ -> Nothing

asCached ::
  forall sym t solver fs v v'.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  ExprRewrite sym v v' ->
  IO (ExprRewrite sym v v')
asCached rew@(ExprRewrite (Just _) _) = return rew
asCached (ExprRewrite Nothing binds) = ExprRewrite <$> (Just <$> freshVarBindCache) <*> pure binds


-- | An expr tagged with a scoped parameter (representing the fact that the
-- expression is valid under the scope 'v')
data ScopedExpr sym tp (v :: VarScope) =
  ScopedExpr { unSE :: (W4.SymExpr sym tp) }

-- | Perform a scope-modifying rewrite to an 'PEM.ExprMappable'.
-- The rewrite is phrased as a 'ScopedExpr' transformation, which obligates
-- the user to produce an expression that is scoped to 'v2'.
scopedExprMap ::
  Scoped f =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PEM.ExprMappable sym (f v1) =>
  sym ->
  f v1 ->
  (forall tp. ScopedExpr sym tp v1 -> m (ScopedExpr sym tp v2)) ->
  m (f v2)
scopedExprMap sym body f = unsafeCoerceScope <$> PEM.mapExpr sym (\e -> unSE <$> f (ScopedExpr e)) body

-- | Apply an 'ExprRewrite' to a 'ScopedExpr', rebinding its value
-- and changing its scope.
applyExprRewrite ::
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  ExprRewrite sym v v' ->
  ScopedExpr sym tp v ->
  IO (ScopedExpr sym tp v')
applyExprRewrite sym (ExprRewrite mcache binds) (ScopedExpr e) =
  ScopedExpr <$> rewriteSubExprs sym mcache (lookupExprList binds) e

-- | An operation is scope-preserving if it is valid for all builders (i.e. we can't
-- incidentally include bound variables from other scopes)
liftScope2 ::
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall sym'. W4.IsSymExprBuilder sym' => sym' -> W4.SymExpr sym' tp1 -> W4.SymExpr sym' tp2 -> IO (W4.SymExpr sym' tp3)) ->
  ScopedExpr sym tp1 v ->
  ScopedExpr sym tp2 v ->
  IO (ScopedExpr sym tp3 v)
liftScope2 sym f (ScopedExpr e1) (ScopedExpr e2) = ScopedExpr <$> f sym e1 e2


-- | An operation is scope-preserving if it is valid for all builders (i.e. we can't
-- incidentally include bound variables from other scopes)
liftScope0 ::
  forall v sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall sym'. W4.IsSymExprBuilder sym' => sym' -> IO (W4.SymExpr sym' tp)) ->
  IO (ScopedExpr sym tp v)
liftScope0 sym f = ScopedExpr <$> f sym

-- | A concrete value is valid in all scopes
concreteScope ::
  forall v sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.ConcreteVal tp ->
  IO (ScopedExpr sym tp v)
concreteScope sym c = liftScope0 sym (\sym' -> W4.concreteToSym sym' c)

-- | Produce an 'ExprRewrite' that binds the terms in the given 'SimVars'
-- to the bound variables in 'SimScope'.
-- This rewrite is scope-modifying, because we will necessarily rewrite any
-- of the bound variables from the original scope 'v1'.
-- The given 'SimVars' may be arbitrary expressions, but necessarily
-- in the scope 'v2'.
getExprRewrite ::
  forall v1 v2 sym arch s st fs.
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  SimScope sym arch v1 ->
  PPa.PatchPair (SimVars sym arch v2) ->
  IO (ExprRewrite sym v1 v2)
getExprRewrite sym scope vals = do
  let vars = scopeBoundVars scope
  (bindsO, bindsP) <- PPa.forBinsC $ \get -> do
    let st = simVarState $ get vals
    mkVarBinds sym (get vars) (MT.memState $ simMem st) (simRegs st) (simStackBase st)
  asCached $ bindsO <> bindsP

bindSpec ::
  forall sym arch s st fs f v.
  Scoped f =>
  (forall v'. PEM.ExprMappable sym (f v')) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  PPa.PatchPair (SimVars sym arch v) ->
  SimSpec sym arch f ->
  IO (AssumptionSet sym v, f v)
bindSpec sym vals (SimSpec scope@(SimScope _ asm) body) = do
  rew <- getExprRewrite sym scope vals
  body' <- scopedExprMap sym body (applyExprRewrite sym rew)
  asm' <- scopedExprMap sym asm (applyExprRewrite sym rew)
  return $ (asm', body')

------------------------------------
-- ExprMappable instances

-- TODO: in general we should restrict these to be scope-preserving,
-- since allowing arbitrary modifications can violate the scoping
-- assumptions

instance PEM.ExprMappable sym (SimState sym arch v bin) where
  mapExpr sym f (SimState mem regs (ScopedExpr sb)) = SimState
    <$> PEM.mapExpr sym f mem
    <*> MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) regs
    <*> (ScopedExpr <$> f sb)

instance PEM.ExprMappable sym (SimInput sym arch v bin) where
  mapExpr sym f (SimInput st blk absSt) = SimInput
    <$> PEM.mapExpr sym f st
    <*> return blk
    <*> return absSt

instance PEM.ExprMappable sym (SimOutput sym arch v bin) where
  mapExpr sym f (SimOutput out blkend) = SimOutput
    <$> PEM.mapExpr sym f out
    <*> PEM.mapExpr sym f blkend

instance PEM.ExprMappable sym (SimBundle sym arch v) where
  mapExpr sym f (SimBundle in_ out) = SimBundle
    <$> PEM.mapExpr sym f in_
    <*> PEM.mapExpr sym f out
