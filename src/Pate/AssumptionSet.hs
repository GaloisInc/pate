{-# LANGUAGE GADTs   #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE LambdaCase   #-}


{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.AssumptionSet (
    AssumptionSet
  , augment
  , weaken
  , fromExprBindings
  , exprBinding
  , bindExprPair
  , natBinding
  , ptrBinding
  , macawRegBinding
  , fromPred
  , toPred
  , toPredList
  , toAtomList
  , apply
  , isAssumedPred
  , mux
  , NamedAsms(..)
  , IsAssumptionSat(..)
  ) where

import           GHC.TypeLits

import           Control.Monad ( forM )
import qualified Control.Monad.IO.Class as IO
import           Data.Proxy
import           Data.Default

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF


import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

import qualified Data.Macaw.Symbolic as MS

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT

import           Data.Parameterized.SetF ( SetF )
import qualified Data.Parameterized.SetF as SetF
import qualified Pate.SimulatorRegisters as PSR
import           Pate.Panic
import qualified Pate.PatchPair as PPa
import qualified What4.ExprHelpers as WEH
import           What4.ExprHelpers ( ExprSet, VarBindCache, ExprBindings, ppExprSet )
import qualified Pate.ExprMappable as PEM
import           Pate.TraceTree
import qualified Pate.Location as PL
import qualified What4.JSON as W4S
import           What4.JSON ( (.=) )

-- | A structured collection of predicates intended to represent an assumption state.
--   Logically it is simply a set of predicates that can be added to the solver's
--   assumption state. It also contains a collection of one-to-many expression
--   rewrite rules (bindings) which represent equality assumptions that can be
--   explicitly applied to simplify What4 terms (see 'apply').
--   When flatting an 'AssumptionSet' into a 'W4.Pred', the binding environment is
--   included (e.g. e -> @{e1, e2} ==> (e == e1) && (e == e2)@).
--   Rewriting terms with the binding environment is therefore strictly optional,
--   as the relevant equality assumptions are always present in the solver state.
--
--   NOTE: Currently there are no assumptions made about the given collection of
--   predicates or bindings. Rewrite loops are implicitly broken arbitrarily
--   when a binding environment is applied, and inconsistent assumptions are only
--   determined when attempting to add them to the solver state.
--   Trivial bindings (i.e. @e --> {e}@) are dropped by most operations, but this
--   not strictly required.
data AssumptionSet sym =
  AssumptionSet
    { asmPreds :: ExprSet sym W4.BaseBoolType
    -- | equivalence on sub-expressions. In the common case where an expression maps
    -- to a single expression (i.e. a singleton 'ExprSet') we can apply the rewrite
    -- inline.
    , asmBinds :: MapF.MapF (W4.SymExpr sym) (ExprSet sym)
    }

-- | Make an AssumptionSet, attempting to collapse it to be concretely False if it
--   has inconsistent predicates or bindings
mkAssumptionSet :: forall sym. W4.IsSymExprBuilder sym => sym -> ExprSet sym W4.BaseBoolType -> MapF.MapF (W4.SymExpr sym) (ExprSet sym) -> AssumptionSet sym
mkAssumptionSet sym ps bs = case SetF.member (W4.falsePred sym) ps of
  True -> AssumptionSet (SetF.singleton (W4.falsePred sym)) MapF.empty
  False ->
    let bad_binds = MapF.filterWithKey (\k v -> case concreteBind k (SetF.toList v) of
          Just False -> True
          _ -> False) bs
    in case MapF.null bad_binds of
      True -> AssumptionSet ps bs
      False -> AssumptionSet (SetF.singleton (W4.falsePred sym)) MapF.empty
  where
    -- Returns Just False if the binding is concretely inconsistent
    concreteBind :: forall tp. W4.SymExpr sym tp -> [W4.SymExpr sym tp] -> Maybe Bool
    concreteBind _e [] = Nothing
    concreteBind e (e':es) = case (W4.asConcrete e, W4.asConcrete e') of
      (Just c1, Just c2) -> case concreteBind e es of
        Just b -> Just (c1 == c2 && b)
        Nothing -> Just (c1 == c2)
      (Just{}, Nothing) -> concreteBind e es
      (Nothing,_) -> Nothing

instance OrdF (W4.SymExpr sym) => Semigroup (AssumptionSet sym) where
  asm1 <> asm2 = let
    preds = (asmPreds asm1) <> (asmPreds asm2)
    binds = mergeExprSetFMap (Proxy @sym) (asmBinds asm1) (asmBinds asm2)
    in AssumptionSet preds binds

instance OrdF (W4.SymExpr sym) => PEM.ExprMappable sym (AssumptionSet sym) where
  mapExpr sym f (AssumptionSet ps bs) | PEM.SymExprMappable aEM <- PEM.symExprMappable sym = do
    ps' <- aEM @W4.BaseBoolType $ PEM.mapExpr sym f ps
    bs' <- forM (MapF.toList bs) $ \(MapF.Pair k (v :: ExprSet sym tp)) -> do
      k' <- f k
      v' <- SetF.filter (\e' -> case testEquality e' k' of Just Refl -> False; Nothing -> True) <$> (aEM @tp $ PEM.mapExpr sym f v)
      if SetF.null v' then
        return $ MapF.empty
      else
        return $ MapF.singleton k' v'
    return $ mkAssumptionSet sym ps' (foldr (mergeExprSetFMap (Proxy @sym)) MapF.empty bs')

instance PEM.ExprFoldable sym (AssumptionSet sym) where
  foldExpr sym f (AssumptionSet ps bs) acc =
    PEM.withSymExprFoldable @W4.BaseBoolType sym $
      PEM.foldExpr sym f ps acc >>= PEM.foldExpr sym f bs

instance forall sym. W4S.SerializableExprs sym => W4S.W4Serializable sym (AssumptionSet sym) where
  w4Serialize (AssumptionSet ps bs) | SetF.null ps, MapF.null bs = W4S.w4Serialize True
  w4Serialize (AssumptionSet ps bs) | [p] <- SetF.toList ps, MapF.null bs = W4S.w4SerializeF p
  w4Serialize (AssumptionSet ps bs) =
    W4S.withSerializable (Proxy @sym) (Proxy @(W4.SymExpr sym)) (Proxy @W4.BaseBoolType) $ do
    W4S.object [ "predicates" .= ps, "bindings" .= bs ]

instance forall sym. W4.IsExpr (W4.SymExpr sym) => PP.Pretty (AssumptionSet sym) where
  pretty asms =
    PP.vsep $
      [ "Predicate Assumptions"
      , PP.indent 4 (ppExprSet (Proxy @sym) (asmPreds asms))
      , "Bindings"
      , PP.indent 4 (ppBinds (Proxy @sym) (asmBinds asms))
      ]

instance W4.IsExpr (W4.SymExpr sym) => Show (AssumptionSet sym) where
  show asms = show (PP.pretty asms)

instance OrdF (W4.SymExpr sym) => Monoid (AssumptionSet sym) where
  mempty = AssumptionSet mempty MapF.empty

data NamedAsms sym (nm :: Symbol) =
  KnownSymbol nm => NamedAsms { namedAsms :: AssumptionSet sym }

instance W4S.SerializableExprs sym => W4S.W4Serializable sym (NamedAsms sym nm) where
  w4Serialize (NamedAsms asm) = W4S.w4Serialize asm

instance PEM.ExprFoldable sym (NamedAsms sym nm) where
  foldExpr sym f (NamedAsms asm) acc = PEM.foldExpr sym f asm acc

instance PEM.ExprFoldableF sym (NamedAsms sym)

instance PEM.ExprMappable sym (NamedAsms sym nm) where
  mapExpr sym f (NamedAsms asm) = NamedAsms <$> PEM.mapExpr sym f asm

instance OrdF (W4.SymExpr sym) => Semigroup (NamedAsms sym nm) where
  (NamedAsms a) <> (NamedAsms b) = NamedAsms (a <> b)

instance (OrdF (W4.SymExpr sym), KnownSymbol nm) => Monoid (NamedAsms sym nm) where
  mempty = NamedAsms mempty

instance forall sym arch nm. (W4.IsSymExprBuilder sym) => PL.LocationWitherable sym arch (NamedAsms sym nm) where
  witherLocation sym (NamedAsms asms) f = do
    p <- toPred sym asms
    f (PL.Named (CT.knownSymbol @nm)) p >>= \case
      Just (_, p') -> return $ (NamedAsms (fromPred p'))
      Nothing -> return $ (NamedAsms mempty)

instance forall sym arch nm. (W4.IsSymExprBuilder sym) => PL.LocationTraversable sym arch (NamedAsms sym nm) where
  traverseLocation sym nasms f = PL.witherLocation sym nasms (\l p -> Just <$> f l p)

mergeExprSetFMap ::
  OrdF (W4.SymExpr sym) =>
  OrdF a =>
  Proxy sym ->
  MapF.MapF (W4.SymExpr sym) (SetF a) ->
  MapF.MapF (W4.SymExpr sym) (SetF a) ->
  MapF.MapF (W4.SymExpr sym) (SetF a)
mergeExprSetFMap _sym map1 map2 =
  MapF.mergeWithKey
    (\_ eset1 eset2 -> Just (eset1 <> eset2))
    id
    id
    map1
    map2


ppBinds ::
  W4.IsExpr (W4.SymExpr sym) =>
  Proxy sym ->
  MapF.MapF (W4.SymExpr sym) (ExprSet sym) ->
  PP.Doc a
ppBinds sym bnds =
  let bs = [ W4.printSymExpr e <+> "-->" <+>  ppExprSet sym es | MapF.Pair e es <- MapF.toList bnds ]
  in PP.sep (zipWith (<+>) ("[" : repeat ",") bs) <+> "]"


-- | Lift an expression binding environment into an assumption set
fromExprBindings ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  ExprBindings sym ->
  AssumptionSet sym
fromExprBindings binds = AssumptionSet { asmPreds = mempty, asmBinds = MapF.map SetF.singleton binds }


fromPred ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  W4.Pred sym ->
  AssumptionSet sym
fromPred p = AssumptionSet (SetF.singleton p) MapF.empty

toPredList ::
  forall m sym.
  W4.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  AssumptionSet sym ->
  m [W4.Pred sym]
toPredList sym asms = do
  bindPreds <- concat <$> mapM assumeBinds (MapF.toList (asmBinds asms))
  return $ bindPreds ++ (SetF.toList (asmPreds asms))
  where
    assumeBinds :: MapF.Pair (W4.SymExpr sym) (ExprSet sym) -> m [W4.Pred sym]
    assumeBinds (MapF.Pair eSrc eTgts) = forM (SetF.toList eTgts) $ \eTgt ->
      IO.liftIO $ W4.isEq sym eSrc eTgt

-- | Decompose an 'AssumptionSet' into "atomic" assumptions (i.e. each
--   containing a single bind or predicate)
toAtomList ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  AssumptionSet sym ->
  [AssumptionSet sym]
toAtomList asms = bindingAtoms <> predAtoms
  where
    predAtoms :: [AssumptionSet sym]
    predAtoms = do
      p <- SetF.toList (asmPreds asms)
      return $ fromPred p      

    bindingAtoms :: [AssumptionSet sym]
    bindingAtoms = do
      bindPair <- MapF.toList (asmBinds asms)
      MapF.Pair src tgt <- assumeBind bindPair
      return $ exprBinding src tgt

    assumeBind :: MapF.Pair (W4.SymExpr sym) (ExprSet sym) -> [MapF.Pair (W4.SymExpr sym) (W4.SymExpr sym)]
    assumeBind (MapF.Pair eSrc eTgts) = do
      eTgt <- SetF.toList eTgts
      return $ MapF.Pair eSrc eTgt

exprBinding ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  -- | source expression
  W4.SymExpr sym tp ->
  -- | target expression
  W4.SymExpr sym tp ->
  AssumptionSet sym
exprBinding eSrc eTgt = case testEquality eSrc eTgt of
  Just Refl -> mempty
  _ -> (mempty :: AssumptionSet sym) { asmBinds = (MapF.singleton eSrc (SetF.singleton eTgt)) }

-- | Equates an original and patched assumption (binds the original to the patched)
--   Has no effect for singleton 'PatchPair' values
bindExprPair ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  PPa.PatchPairC (W4.SymExpr sym tp) ->
  AssumptionSet sym
bindExprPair (PPa.PatchPairC src tgt) = exprBinding src tgt
bindExprPair _ = mempty

natBinding ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  -- | source expression
  W4.SymNat sym ->
  -- | target expression
  W4.SymNat sym ->
  AssumptionSet sym
natBinding n1 n2 = exprBinding (W4.natToIntegerPure n1) (W4.natToIntegerPure n2)

-- | Bind the first argument to the second in the resulting
--   'AssumptionSet' by binding the component expressions of the given pointer.
--   e.g.
--   @ptrBinding ptr(reg1,off1) ptr(reg2,off2) == [ reg1 --> {reg2}, off1 --> {off2} ]@
ptrBinding ::
  W4.IsSymExprBuilder sym =>
  CLM.LLVMPtr sym w ->
  CLM.LLVMPtr sym w ->
  AssumptionSet sym
ptrBinding (CLM.LLVMPointer reg1 off1) (CLM.LLVMPointer reg2 off2) =
  let
    regBind = natBinding reg1 reg2
    offBind = exprBinding off1 off2
  in (regBind <> offBind)


-- | Bind the first argument to the second in the resulting
--   'AssumptionSet' by binding the component expressions of the given value.
--   e.g.
--   @
--   macawRegBinding ptr(reg1,off1) ptr(reg2,off2) == [ reg1 --> {reg2}, off1 --> {off2} ]
--   macawRegBinding bool1 bool2 == [ bool1 --> {bool2} ]
--   @
--   Only supports pointers, booleans and empty structs.
macawRegBinding ::
  W4.IsSymExprBuilder sym =>
  MS.ToCrucibleType tp ~ MS.ToCrucibleType tp' =>
  sym ->
  -- | value to rebind
  PSR.MacawRegEntry sym tp ->
  -- | new value
  PSR.MacawRegEntry sym tp' ->
  AssumptionSet sym
macawRegBinding _sym var val = do
  case PSR.macawRegRepr var of
    CLM.LLVMPointerRepr _ -> ptrBinding (PSR.macawRegValue var) (PSR.macawRegValue val)
    CT.BoolRepr -> exprBinding (PSR.macawRegValue var) (PSR.macawRegValue val)
    CT.StructRepr Ctx.Empty -> mempty
    _ -> panic Rewriter "macawRegBinding" ["Unexpected macaw types"
                                          , show (PSR.macawRegRepr var)
                                          , show (PSR.macawRegRepr val)
                                          ]



-- | Rewrite the given 'f' with any bindings in the given 'AssumptionSet'.
--   Bindings are applied repeatedly to each component expression until a fixpoint
--   is reached or a loop is detected.
apply ::
  forall sym f m t solver fs.
  PEM.ExprMappable sym f =>
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  AssumptionSet sym ->
  f ->
  m f
apply sym asm f = do
  cache <- IO.liftIO WEH.freshVarBindCache
  applyWithCache sym cache asm f

-- | Rewrite the given 'f' with any bindings in the given 'AssumptionSet'.
--   Bindings are applied repeatedly to each component expression until a fixpoint
--   is reached or a loop is detected.
applyWithCache ::
  forall sym f m t solver fs.
  PEM.ExprMappable sym f =>
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  VarBindCache sym ->
  AssumptionSet sym ->
  f ->
  m f
applyWithCache sym cache asm f = do
  let
    -- FIXME: This hangs in some cases. Maybe some rewrite loop
    -- causes some monotonic increase in expression size rather than a loop?
    _doRebind :: forall tp. ExprSet sym tp -> W4.SymExpr sym tp -> m (W4.SymExpr sym tp)
    _doRebind ancestors e = do
      e' <- rebindWithFrame' sym cache asm e
      case SetF.member e' ancestors of
        True -> return e'
        False -> doRebind (SetF.insert e' ancestors) e'
    doRebind :: forall tp. ExprSet sym tp -> W4.SymExpr sym tp -> m (W4.SymExpr sym tp)
    doRebind _ancestors e = rebindWithFrame' sym cache asm e
  PEM.mapExpr sym (doRebind mempty) f

-- | Augment an assumption set by first rewriting its entries with the given
--   assumptions before adding them to the set.
--   i.e. given `a + b -> {c,d}` and adding `a -> b; c -> d` the result
--   will be `b + b -> {d}; a -> b; c -> d`
augment ::
  sym ~ (W4B.ExprBuilder t solver fs) =>
  IO.MonadIO m =>
  sym ->
  AssumptionSet sym {- ^ original asm set -}  ->
  AssumptionSet sym {- ^ additional assumptions -} ->
  m (AssumptionSet sym)
augment sym origAsm newAsm = do
  cache <- IO.liftIO WEH.freshVarBindCache
  origAsm' <- PEM.mapExpr sym (applyWithCache sym cache newAsm) origAsm
  return $ newAsm <> origAsm'

weaken ::
  IO.MonadIO m =>
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  AssumptionSet sym ->
  m (AssumptionSet sym)
weaken sym p asms = do
  asms_pred <- toPred sym asms
  p' <- IO.liftIO $ W4.impliesPred sym p asms_pred
  return $ fromPred p'

-- | Retrieve a value that the given expression is bound to in
--   the given 'AssumptionSet'.
--   In the case of multiple results, constant values are preferred,
--   otherwise the least element of all possible symbolic bindings is returned.
--   This is a heuristic used in 'apply' for usefully applying a binding
--   environment to a term when multiple possible bindings are found.
--   e.g. given @asm = [ x --> {y, 3} ]@ then @getSomeBinding asm x == 3@, therefore
--   @apply (x + z) == (3 + z)@
getSomeBinding ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  OrdF (W4.SymExpr sym) =>
  sym ->
  AssumptionSet sym ->
  W4.SymExpr sym tp ->
  Maybe (W4.SymExpr sym tp)
getSomeBinding sym asm e =
  let allBinds = getAllBindings sym SetF.empty asm e
  in case SetF.lookupMin (SetF.filter (\e' -> isJust (W4.asConcrete e')) allBinds) of
    Just e' -> Just e'
    Nothing -> SetF.lookupMin allBinds

-- | Retrieve all possible bindings (transitively) for a given expression.
getAllBindings ::
  forall sym tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SetF (W4.SymExpr sym) tp ->
  AssumptionSet sym ->
  W4.SymExpr sym tp ->
  SetF (W4.SymExpr sym) tp
getAllBindings sym ancestors asm e = case SetF.member e ancestors of
  True -> SetF.empty
  False -> case MapF.lookup e (asmBinds asm) of
    Just es ->
      let ancestors' = SetF.insert e ancestors
      in SetF.unions (map (\e' -> SetF.insert e' (getAllBindings sym ancestors' asm e')) (SetF.toList es))
    Nothing -> case W4.exprType e of
      W4.BaseBoolRepr | isAssumedPred asm e -> SetF.singleton (W4.truePred sym)
      _ -> SetF.empty

-- | Compute a predicate that forms a conjunction from the individual predicates
--   and bindings in the given 'AssumptionSet'. The resulting predicate is therefore true iff
--   all of the given predicates are true and all of the equalities represented from the
--   binding environment are true.
-- e.g.
-- @
-- let asm = (fromPred (x > 0) <> exprBinding (y, x) <> exprBinding (y, z))
-- asm ==> [ x > 0; y --> {x, z} ]
-- toPred asm ==> x > 0 && y == x && y == z
-- @
toPred ::
  forall sym m.
  W4.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  AssumptionSet sym ->
  m (W4.Pred sym)
toPred sym asm = do
  bindsAsm <- fmap concat $ mapM assumeBinds (MapF.toList (asmBinds asm))
  let predList = SetF.toList $ (asmPreds asm) <> (SetF.fromList bindsAsm)
  IO.liftIO $ WEH.allPreds sym predList
  where
    assumeBinds :: MapF.Pair (W4.SymExpr sym) (ExprSet sym) -> m [W4.Pred sym]
    assumeBinds (MapF.Pair eSrc eTgts) = forM (SetF.toList eTgts) $ \eTgt ->
      IO.liftIO $ W4.isEq sym eSrc eTgt

mux ::
  W4.IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  W4.Pred sym ->
  AssumptionSet sym ->
  AssumptionSet sym ->
  m (AssumptionSet sym)  
mux sym p asmT asmF = do
  asmT_pred <- toPred sym asmT
  asmF_pred <- toPred sym asmF
  ite <- IO.liftIO $ W4.baseTypeIte sym p asmT_pred asmF_pred
  return $ fromPred ite

isAssumedPred ::
  forall sym.
  W4.IsSymExprBuilder sym =>
  AssumptionSet sym ->
  W4.Pred sym ->
  Bool
isAssumedPred _ asm | Just b <- W4.asConstantPred asm = b
isAssumedPred frame asm = SetF.member asm (asmPreds frame)

-- | Explicitly rebind any known sub-expressions that are in the frame.
_rebindWithFrame ::
  forall sym m t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  IO.MonadIO m =>
  sym ->
  AssumptionSet sym ->
  W4B.Expr t tp ->
  m (W4B.Expr t tp)
_rebindWithFrame sym asm e = do
  cache <- IO.liftIO $ WEH.freshVarBindCache
  rebindWithFrame' sym cache asm e

rebindWithFrame' ::
  forall sym m t solver fs tp.
  sym ~ (W4B.ExprBuilder t solver fs) =>
  IO.MonadIO m =>
  sym ->
  VarBindCache sym ->
  AssumptionSet sym ->
  W4B.Expr t tp ->
  m (W4B.Expr t tp)
rebindWithFrame' sym cache asm = WEH.rewriteSubExprs' sym cache (getSomeBinding sym asm)

data IsAssumptionSat = UnknownSatAssumption | IsSatAssumption
  deriving (Eq, Ord, Show)

instance Default IsAssumptionSat where
  def = UnknownSatAssumption

instance W4.IsExpr (W4.SymExpr sym) => IsTraceNode '(sym,arch) "assumption" where
  type TraceNodeType '(sym,arch) "assumption" = AssumptionSet sym
  type TraceNodeLabel "assumption" = IsAssumptionSat
  prettyNode _ asm = PP.pretty asm
  nodeTags = [(Summary, \_ _ -> "assumptions")]
