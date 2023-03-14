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
{-# LANGUAGE OverloadedStrings   #-}
-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.SimState
  ( -- simulator state
    SimState(..)
  , StackBase(..)
  , freshStackBase
  , SimInput(..)
  , SimOutput(..)
  , type VarScope
  , SimScope
  , scopeAsm
  , scopeVars
  , scopeVarsPair
  , Scoped(..)
  , ScopedExpr
  , unSE
  , scopedExprMap
  , scopedLocWither
  , WithScope(..)
  , liftScope0
  , forScopedExpr
  , liftScope2
  , concreteScope
  , SimSpec
  , mkSimSpec
  , freshSimSpec
  , forSpec
  , forSpec2
  , viewSpec
  , viewSpecBody
  , unsafeCoerceSpecBody
  , SimBundle(..)
  , simInMem
  , simInRegs
  , simOutMem
  , simOutRegs
  , simPair
  , simSP
  -- variable binding
  , SimVars(..)
  , bindSpec
  , ScopeCoercion
  , getScopeCoercion
  , applyScopeCoercion
  , bundleOutVars
  , bundleInVars
  ) where

import           GHC.Stack ( HasCallStack )
import qualified Data.Kind as DK
import           Data.Proxy

import qualified Control.Monad.IO.Class as IO
import           Control.Lens ( (^.) )
import           Control.Monad.Trans.Maybe ( MaybeT(..), runMaybeT )
import           Control.Monad.Trans ( lift )

import qualified Prettyprinter as PP

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF
import           Data.Functor.Const

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.AbsDomain.AbsState as MAS
import qualified Data.Macaw.Types as MT

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
import qualified Pate.Panic as P
import qualified Pate.Location as PL
import qualified Pate.Register.Traversal as PRt
import qualified Pate.SimulatorRegisters as PSR
import           What4.ExprHelpers
import           Pate.AssumptionSet
import           Pate.TraceTree

import           Data.Coerce ( coerce ) 

------------------------------------
-- Crucible inputs and outputs


data SimState sym arch (v :: VarScope) (bin :: PBi.WhichBinary) = SimState
  {
    simMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
  , simRegs :: MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
  , simStackBase :: StackBase sym arch v
  -- | The most recent region allocated by malloc. Ideally this should always be
  --   concrete (i.e. have some concrete constraint in the value domain), but
  --   can be symbolic if the number of calls to @malloc()@ cannot be statically determined.
  --   We model a @malloc@ call as simply returning a pointer at offset zero to a fresh
  --   region, and then incrementing this value.
  , simMaxRegion :: ScopedExpr sym v W4.BaseIntegerType
  }

simSP :: MM.RegisterInfo (MM.ArchReg arch) => SimState sym arch v bin ->
  PSR.MacawRegEntry sym (MT.BVType (MM.ArchAddrWidth arch))
simSP st = (simRegs st) ^. (MM.boundValue MM.sp_reg)


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

mkSimSpec :: SimScope sym arch v -> f v -> SimSpec sym arch f
mkSimSpec scope body = SimSpec scope body

data SimScope sym arch v =
  SimScope
    { -- NOTE: explicitly not a 'PatchPair' because the scope always has
      -- variables for both binaries
      scopeBoundVarsO :: SimBoundVars sym arch v PBi.Original
    , scopeBoundVarsP :: SimBoundVars sym arch v PBi.Patched
    , scopeAsm :: AssumptionSet sym
    }

scopeBoundVars :: SimScope sym arch v -> PPa.PatchPair (SimBoundVars sym arch v)
scopeBoundVars scope = PPa.PatchPair (scopeBoundVarsO scope) (scopeBoundVarsP scope)

scopeVars :: SimScope sym arch v -> PPa.PatchPair (SimVars sym arch v)
scopeVars scope = TF.fmapF boundVarsAsFree (scopeBoundVars scope)

-- | A 'SimScope' always has variables defined for both the original and patched binaries,
--   and so we can return a normal tuple of 'SimVars'.
scopeVarsPair :: SimScope sym arch v -> (SimVars sym arch v PBi.Original, SimVars sym arch v PBi.Patched)
scopeVarsPair scope = (boundVarsAsFree $ scopeBoundVarsO scope, boundVarsAsFree $ scopeBoundVarsP scope)

-- | Create a 'SimSpec' with "fresh" bound variables
freshSimSpec ::
  forall sym arch f m.
  PPa.PatchPairM m =>
  HasCallStack =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  -- | These must all be fresh variables
  (forall bin tp. PBi.WhichBinaryRepr bin -> MM.ArchReg arch tp -> m (PSR.MacawRegVar sym tp)) ->
  -- | This must be a fresh MemTrace
  (forall bin. PBi.WhichBinaryRepr bin -> m (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))) ->
  -- | Fresh stack base
  (forall bin v. PBi.WhichBinaryRepr bin -> m (StackBase sym arch v)) ->
  -- | Fresh base region
  (forall bin v. PBi.WhichBinaryRepr bin -> m (ScopedExpr sym v W4.BaseIntegerType)) ->
  -- | Produce the body of the 'SimSpec' given the initial variables
  (forall v. PPa.PatchPair (SimVars sym arch v) -> m (AssumptionSet sym, (f v))) ->
  m (SimSpec sym arch f)
freshSimSpec mkReg mkMem mkStackBase mkMaxregion mkBody = do
  vars <- PPa.forBins $ \bin -> do
    regs <- MM.mkRegStateM (mkReg bin)
    mem <- mkMem bin
    sb <- mkStackBase bin
    mr <- mkMaxregion bin
    return $ SimBoundVars regs (SimState mem (MM.mapRegsWith (\_ -> PSR.macawVarEntry) regs) sb mr)
  (asm, body) <- mkBody (TF.fmapF boundVarsAsFree vars)
  case vars of
    PPa.PatchPair varsO varsP -> return $ SimSpec (SimScope varsO varsP asm) body
    PPa.PatchPairSingle{} -> PPa.throwPairErr

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

forSpec2 ::
  Monad m =>
  SimSpec sym arch f ->
  (forall v. SimScope sym arch v -> f v -> m (g v, h v)) ->
  m (SimSpec sym arch g, SimSpec sym arch h)
forSpec2 (SimSpec scope body) f = do
  (g,h) <- f scope body
  return $ (SimSpec scope g, SimSpec scope h)

-- | Unsafely coerce the body of a spec to have any scope.
-- After this is used, the variables in the resulting 'f' should
-- be rebound to actually be properly scoped to 'v'.
unsafeCoerceSpecBody ::
  Scoped f =>
  SimSpec sym arch f -> f v
unsafeCoerceSpecBody (SimSpec _ body) = unsafeCoerceScope body

-- | The symbolic inputs and outputs of an original vs. patched block slice.
data SimBundle sym arch v = SimBundle
  {
    simIn :: PPa.PatchPair (SimInput sym arch v)
  , simOut :: PPa.PatchPair (SimOutput sym arch v)
  }


instance Scoped (SimBundle sym arch) where
  unsafeCoerceScope bundle = coerce bundle

instance (W4.IsSymExprBuilder sym,  MM.RegisterInfo (MM.ArchReg arch)) => IsTraceNode '(sym,arch) "bundle" where
  type TraceNodeType '(sym,arch) "bundle" = Some (SimBundle sym arch)
  prettyNode () (Some _bundle) = "<TODO: pretty bundle>"
  nodeTags = [("symbolic", \_ _ -> "<TODO: pretty bundle>")]


bundleOutVars :: SimBundle sym arch v -> PPa.PatchPair (SimVars sym arch v)
bundleOutVars bundle = TF.fmapF (SimVars . simOutState) (simOut bundle)

bundleInVars :: SimBundle sym arch v -> PPa.PatchPair (SimVars sym arch v)
bundleInVars bundle = TF.fmapF (SimVars . simInState) (simIn bundle)

simPair :: SimBundle sym arch v -> PB.BlockPair arch
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
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  SimBoundVars sym arch v bin ->
  MT.MemTraceState sym (MM.ArchAddrWidth arch) ->
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  StackBase sym arch v' ->
  ScopedExpr sym v' W4.BaseIntegerType ->
  IO (ExprRewrite sym v v')
mkVarBinds _sym simVars mem regs sb mr = do
  let
    memVar = MT.memState $ simMem $ simBoundVarState simVars
    regVars = simBoundVarRegs simVars
    stackVar = simStackBase $ simBoundVarState simVars
    stackBinds = singleRewrite (unSE $ unSB $ stackVar) (unSE $ unSB $ sb)

    maxRegVar = simMaxRegion $ simBoundVarState simVars
    maxRegBinds = singleRewrite (unSE $ maxRegVar) (unSE $ mr)
    
  regVarBinds <- fmap PRt.collapse $ PRt.zipWithRegStatesM regVars regs $ \_ (PSR.MacawRegVar _ vars) val -> do
    case PSR.macawRegRepr val of
      CLM.LLVMPointerRepr{} -> do
        CLM.LLVMPointer region off <- return $ PSR.macawRegValue val
        (Ctx.Empty Ctx.:> regVar Ctx.:> offVar) <- return $ vars
        let iRegion = W4.natToIntegerPure region
        return $ Const $ singleRewrite regVar iRegion <> singleRewrite offVar off
      CT.BoolRepr -> do
        Ctx.Empty Ctx.:> var <- return vars
        return $ Const $ singleRewrite var (PSR.macawRegValue val)
      CT.StructRepr Ctx.Empty -> return $ Const mempty
      repr -> error ("mkVarBinds: unsupported type " ++ show repr)

  return $ (ExprRewrite (MT.mkMemoryBinding memVar mem)) <> regVarBinds <> stackBinds <> maxRegBinds

-- | Wrapped expression bindings that convert expressions from one
-- scope to another
-- Note that this mapping is not necessarily total and therefore cannot be assumed
-- to completely convert an expression (it must be finalized as a 'ScopeCoercion')
data ExprRewrite sym (v :: VarScope) (v' :: VarScope) = 
      ExprRewrite (ExprBindings sym)
 
instance OrdF (W4.SymExpr sym) => Semigroup (ExprRewrite sym v v') where
  rew1 <> rew2 = case (rew1, rew2) of
    (ExprRewrite binds1, ExprRewrite binds2) ->
      ExprRewrite (MapF.mergeWithKey (\_ -> mergeExprs) id id binds1 binds2)
    where
      mergeExprs :: forall tp. W4.SymExpr sym tp -> W4.SymExpr sym tp -> Maybe (W4.SymExpr sym tp)
      mergeExprs e1 e2 = case testEquality e1 e2 of
        Just _ -> Just e1
        Nothing -> P.panic P.Rewriter "ExprRewrite" ["Unexpected variable clash"]

instance OrdF (W4.SymExpr sym) => Monoid (ExprRewrite sym v v') where
  mempty = ExprRewrite MapF.empty
  
data ScopeCoercion sym v v' =
  ScopeCoercion (VarBindCache sym) (ExprRewrite sym v v')


-- UNSAFE: assumes that the incoming expressions adhere to the given scopes
singleRewrite ::
  W4.SymExpr sym tp ->
  W4.SymExpr sym tp ->
  ExprRewrite sym v v'
singleRewrite e1 e2 = ExprRewrite (MapF.singleton e1 e2)

-- TODO: check that the resulting binding is total
asScopeCoercion ::
  forall sym t solver fs v v'.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  ExprRewrite sym v v' ->
  IO (ScopeCoercion sym v v')
asScopeCoercion rew = ScopeCoercion <$> freshVarBindCache <*> pure rew

-- | An expr tagged with a scoped parameter (representing the fact that the
-- expression is valid under the scope 'v')
data ScopedExpr sym (v :: VarScope) tp =
  ScopedExpr { unSE :: W4.SymExpr sym tp }

instance PEM.ExprMappable sym (ScopedExpr sym v tp) where
  mapExpr _sym f (ScopedExpr e) = ScopedExpr <$> f e

instance W4.IsExpr (W4.SymExpr sym) => PP.Pretty (ScopedExpr sym v tp) where
  pretty (ScopedExpr e) = W4.printSymExpr e

instance W4.IsExpr (W4.SymExpr sym) => Show (ScopedExpr sym v tp) where
  show e = show (PP.pretty e)

instance TestEquality (W4.SymExpr sym) => Eq (ScopedExpr sym v tp) where
  e1 == e2 = case testEquality (unSE e1) (unSE e2) of
    Just _ -> True
    Nothing -> False

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
  (forall tp. ScopedExpr sym v1 tp -> m (ScopedExpr sym v2 tp)) ->
  m (f v2)
scopedExprMap sym body f = unsafeCoerceScope <$> PEM.mapExpr sym (\e -> unSE <$> f (ScopedExpr e)) body

-- | Perform a scope-modifying rewrite to an 'PL.LocationWitherable' (optionally dropping
-- elements instead of updating them).
-- The rewrite is phrased as a 'ScopedExpr' transformation, which obligates
-- the user to produce an expression that is scoped to 'v2'.
scopedLocWither ::
  forall sym arch f m v1 v2.
  Scoped f =>
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  PL.LocationWitherable sym arch (f v1) =>
  sym ->
  f v1 ->
  (forall tp nm k. PL.Location sym arch nm k -> ScopedExpr sym v1 tp -> m (Maybe (ScopedExpr sym v2 tp))) ->
  m (f v2)
scopedLocWither sym body f = do
  fmap unsafeCoerceScope $ PL.witherLocation sym body $ \loc p -> runMaybeT $ do
    ScopedExpr p' <- (MaybeT $ f loc (ScopedExpr p))
    loc' <- PEM.mapExpr sym (\e' -> unSE @sym <$> (MaybeT (f loc (ScopedExpr e')))) loc
    return (PL.getLoc loc', p')

--- FIXME: cludge for scopes missing from inner types
-- | Tag any type with a scope type parameter
newtype WithScope f (v :: VarScope) = WithScope { unWS :: f }

instance Scoped (WithScope f) where
  unsafeCoerceScope (WithScope a) = WithScope a

instance PEM.ExprMappable sym f => PEM.ExprMappable sym (WithScope f v) where
  mapExpr sym f (WithScope a) = WithScope <$> PEM.mapExpr sym f a

instance PL.LocationWitherable sym arch f => PL.LocationWitherable sym arch (WithScope f v) where
  witherLocation sym (WithScope a) f = WithScope <$> PL.witherLocation sym a f


-- | Apply a 'ScopeCoercion' to a 'ScopedExpr', rebinding its value
-- and changing its scope.
applyScopeCoercion ::
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  ScopeCoercion sym v v' ->
  ScopedExpr sym v tp ->
  IO (ScopedExpr sym v' tp)
applyScopeCoercion sym (ScopeCoercion cache (ExprRewrite binds)) (ScopedExpr e) =
  ScopedExpr <$> applyExprBindings' sym cache binds e

-- | An operation is scope-preserving if it is valid for all builders (i.e. we can't
-- incidentally include bound variables from other scopes)
liftScope2 ::
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall sym'. W4.IsSymExprBuilder sym' => sym' -> W4.SymExpr sym' tp1 -> W4.SymExpr sym' tp2 -> IO (W4.SymExpr sym' tp3)) ->
  ScopedExpr sym v tp1 ->
  ScopedExpr sym v tp2 ->
  IO (ScopedExpr sym v tp3)
liftScope2 sym f (ScopedExpr e1) (ScopedExpr e2) = ScopedExpr <$> f sym e1 e2

forScopedExpr ::
  W4.IsSymExprBuilder sym =>
  sym ->
  ScopedExpr sym v tp1 ->
  (forall sym'. W4.IsSymExprBuilder sym' => sym' -> W4.SymExpr sym' tp1 -> IO (W4.SymExpr sym' tp2)) ->
  IO (ScopedExpr sym v tp2)
forScopedExpr sym (ScopedExpr e1) f = ScopedExpr <$> f sym e1

-- | An operation is scope-preserving if it is valid for all builders (i.e. we can't
-- incidentally include bound variables from other scopes)
liftScope0 ::
  forall v sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  (forall sym'. W4.IsSymExprBuilder sym' => sym' -> IO (W4.SymExpr sym' tp)) ->
  IO (ScopedExpr sym v tp)
liftScope0 sym f = ScopedExpr <$> f sym

-- | A concrete value is valid in all scopes
concreteScope ::
  forall v sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.ConcreteVal tp ->
  IO (ScopedExpr sym v tp)
concreteScope sym c = liftScope0 sym (\sym' -> W4.concreteToSym sym' c)

-- | Produce an 'ScopeCoercion' that binds the terms in the given 'SimVars'
-- to the bound variables in 'SimScope'.
-- This rewrite is scope-modifying, because we will necessarily rewrite any
-- of the bound variables from the original scope 'v1'.
-- The given 'SimVars' may be arbitrary expressions, but necessarily
-- in the scope 'v2'.
getScopeCoercion ::
  forall v1 v2 sym arch s st fs.
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  SimScope sym arch v1 ->
  PPa.PatchPair (SimVars sym arch v2) ->
  IO (ScopeCoercion sym v1 v2)
getScopeCoercion sym scope vals = do
  let vars = scopeBoundVars scope
  binds <- PPa.runPatchPairT $ PPa.catBins $ \bin -> do
    st <- simVarState <$> PPa.get bin vals
    vars' <- PPa.get bin vars
    lift $ mkVarBinds sym vars' (MT.memState $ simMem st) (simRegs st) (simStackBase st) (simMaxRegion st)
  asScopeCoercion $ binds

bindSpec ::
  forall sym arch s st fs f v.
  Scoped f =>
  (forall v'. PEM.ExprMappable sym (f v')) =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  sym ~ W4B.ExprBuilder s st fs =>
  sym ->
  PPa.PatchPair (SimVars sym arch v) ->
  SimSpec sym arch f ->
  IO (AssumptionSet sym, f v)
bindSpec sym vals (SimSpec scope@(SimScope _ _ asm) (body :: f v')) = do
  rew <- getScopeCoercion sym scope vals
  body' <- scopedExprMap sym body (applyScopeCoercion sym rew)
  asm' <- unWS <$> scopedExprMap sym (WithScope @_ @v' asm) (applyScopeCoercion sym rew)
  return $ (asm', body')


------------------------------------
-- Stack relative references

{- | = Stack Relative References

== Stack Scope

The equivalence domains are represented as sets of pointers which may diverge
between the two programs. In the case of direct global variable accesses, these
pointers are fully concrete and therefore valid in any scope. In contrast, stack
accesses are always calculated with respect to the stack (or frame) pointer, and
therefore stack pointers necessarily contain the free variable representing the
initial value of the stack register.

Without propagating additional information about this free variable, the
equivalence domain becomes essentially meaningless.

@
void test() {
  // slice 0
  // SP := SP_0
  // domain := {}
  int i = 1;
  int j = 2 OR 3;  // 2 in original function, 3 in patched function
  // SP := SP_0 - 2
  // domain := { SP_0 - 1 }
  // end of slice 0
  f();
  // slice 1
  // SP := SP_1
  // domain := { SP_0 - 1}
  g = i;
  // end of slice 1
}
@

At the return site for @f()@, the connection between the original value of the
stack register (i.e. @SP_0@) and the current value (i.e. @SP_1@) has been
lost. The equivalence domain is meaningless as @SP_0@ is a free variable in this
context. The equivalence check fails and produces a counter-example where the
value of @i@ disagrees between both programs.

== Implementation

The solution requires rewriting the stack pointers in the equivalence domain to
instead be defined with respect to a constant base: the base address of the
function frame. This allows stack accesses to be treated uniformly. At the start
of each function we define the stack pointer to be a free variable: BASE that
is maintained throughout the context of the function.

@
void test() {
  // SP := BASE_0
  // domain := {}
  int i = 1;
  int j = 2 OR 3;
  // SP := BASE_0 - 2
  // domain := { BASE_0 - 1 }
  f();
  // SP := BASE_0 - 2
  // domain := { BASE - 1}
  g = i;
}
@

To support this change, we define the initial stack pointer for a function to be
a distinguished stack base variable (i.e. 'StackBase'), which is treated
specially during function calls.

When verifying @f()@ we rephrase the incoming domain (i.e. @{BASE_0 - 1 }@) by asserting
that the @BASE@ of @f()@ is equal to the value of the stack pointer just after
the function call (e.g. @SP := BASE_0 - 3@ once the return address has been pushed onto the stack).

@
// domain := { BASE_0 - 1 } <- incoming domain
// assume(SP == BASE_0 - 3)
// assume(BASE_1 == SP)
// domain := { BASE_1 + 2 } <- domain rephrased in terms of BASE_1
@


This now becomes the pre-domain when @f()@ is verified.

@
// domain := { BASE_1 + 2 }
void f() {
  int = 1 OR 2;
  return;
}
// domain := { BASE_1 - 1; BASE_1 + 2 }
@

When verifying @test()@ following the call site of @f()@ we can now take this
domain and re-phrase it once again in terms of the stack base of @test()@.

@
// domain := { BASE_1 - 1; BASE_1 + 2 } <- incoming domain (once f() returns)
// assume(SP == BASE_1) --> BASE_1 == BASE_0 - 3
// domain := { BASE_0 - 4; BASE_0 - 1 }
@

Notably this outgoing domain points past the current stack pointer, and therefore
this inequality is unlikely to have any consequence (i.e. this will likely be overwritten
and never accessed).

Given this inequality, we can see that the final assignment to @g@ is equal between
both programs, as the access to the stack variable
@i@ is necessarily equal according to this domain (i.e. @BASE_0 - 0@) .


-}


-- | Points to the base of the stack. In any given context this will always be
-- "free" as the base of the stack is always abstract, but it is rebound to account
-- for changes to the stack pointer when moving between scopes.
newtype StackBase sym arch v =
  StackBase { unSB :: ScopedExpr sym v (W4.BaseBVType (MM.ArchAddrWidth arch)) }

instance PEM.ExprMappable sym (StackBase sym arch v) where
  mapExpr sym f (StackBase e) = StackBase <$> PEM.mapExpr sym f e

instance TestEquality (W4.SymExpr sym) => Eq (StackBase sym arch v) where
  (StackBase a) == (StackBase b) = a == b

freshStackBase ::
  forall sym arch v.
  W4.IsSymExprBuilder sym =>
  MM.MemWidth (MM.ArchAddrWidth arch) =>
  sym ->
  Proxy arch ->
  IO (StackBase sym arch v)
freshStackBase sym _arch = fmap StackBase $ liftScope0 sym $ \sym' ->
    W4.freshConstant sym' (W4.safeSymbol "stack_base") (W4.BaseBVRepr (MM.memWidthNatRepr @(MM.ArchAddrWidth arch)))


------------------------------------
-- ExprMappable instances

-- TODO: in general we should restrict these to be scope-preserving,
-- since allowing arbitrary modifications can violate the scoping
-- assumptions
instance PEM.ExprMappable sym (SimState sym arch v bin) where
  mapExpr sym f (SimState mem regs (StackBase (ScopedExpr sb)) (ScopedExpr mr)) = SimState
    <$> PEM.mapExpr sym f mem
    <*> MM.traverseRegsWith (\_ -> PEM.mapExpr sym f) regs
    <*> ((StackBase . ScopedExpr) <$> f sb)
    <*> (ScopedExpr <$> f mr)

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
