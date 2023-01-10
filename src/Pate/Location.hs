{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Location (
    Location(..)
  , getLoc
  , showLoc
  , LocationWitherable(..)
  , LocationTraversable(..)
  , IsLocation(..)
  , SomeLocation(..)
  , LocationK
  , AsK
  , LocPrf(..)
  , asProof
  , pattern Register
  , pattern Cell
  , pattern Expr
  , pattern Unit
  , pattern Named
  , withUnitEq
  , NamedPred(..)
  , namedPred
  , knownNamedPred
  , namedPredLoc
  , concreteSymbol
  ) where

import           GHC.TypeLits
--import           Prelude.Singletons
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.Trans.Except ( throwE, runExceptT )
import           Control.Monad.Trans.State ( StateT, get, put, execStateT )
import           Control.Monad.Trans ( lift )
import qualified Data.Kind as DK

import qualified Prettyprinter as PP

import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Classes
import           Data.Parameterized.HasRepr ( typeRepr )
import           Data.Parameterized.SymbolRepr ( knownSymbol, symbolRepr, SymbolRepr )

import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFG as MM


import qualified Pate.PatchPair as PPa
import qualified Pate.MemCell as PMC
import qualified Pate.ExprMappable as PEM
import qualified What4.Interface as W4
import qualified What4.PredMap as WPM

import           Pate.TraceTree
import qualified Data.Parameterized.TraversableF as TF
import Data.Functor.Const
import Unsafe.Coerce (unsafeCoerce)

-- | Generalized, extensible location-based traversals

type family LocationK (nm :: Symbol) :: k
type family AsK (nm :: Symbol) (tp :: k) :: LocationK nm

--type family FromLocK (nm :: Symbol) (tp :: LocationK nm) :: k

class (KnownSymbol nm)  => IsLocation (sym :: DK.Type) (arch :: DK.Type) (nm :: Symbol) where
  type LocationType sym arch nm :: (LocationK nm) -> DK.Type
  type Valid sym arch nm :: DK.Constraint
  

  showLoc_ :: f nm -> String
  showLoc_ _ = show $ symbolRepr $ knownSymbol @nm

  mapLocExpr :: W4.IsSymExprBuilder sym =>
    IO.MonadIO m =>
    sym ->
    (forall tp. W4.SymExpr sym tp -> m (W4.SymExpr sym tp)) ->
    (LocationType sym arch nm (x :: (LocationK nm))) ->
    m (LocationType sym arch nm (x :: (LocationK nm)))
  
  prettyLoc :: Valid sym arch nm => LocationType sym arch nm x -> PP.Doc a
  ordFLoc :: Valid sym arch nm => LocationType sym arch nm x1 -> LocationType sym arch nm x2 -> OrderingF x1 x2

showLoc :: forall nm k sym arch. Location sym arch nm k -> String
showLoc (Location{}) = showLoc_ @sym @arch (knownSymbol @nm)

data LocPrf sym arch nm1 nm2 (tp1 :: k1) where
  LocPrf :: forall nm sym arch tp1. (Valid sym arch nm) => 
    LocationType sym arch nm (AsK nm tp1) -> LocPrf sym arch nm nm tp1
  NoLocPrf :: LocPrf sym arch nm1 nm2 tp2

asSymbol :: forall nm_concrete sym arch nm k. (KnownSymbol nm_concrete) => Location sym arch nm k -> Maybe (nm :~: nm_concrete)
asSymbol (Location{}) = testEquality (knownSymbol @nm) (knownSymbol @nm_concrete)

asProof :: forall nm_concrete sym arch nm tp. KnownSymbol nm_concrete => Location sym arch nm tp -> LocPrf sym arch nm nm_concrete tp
asProof l@(Location r) = case asSymbol @nm_concrete l of
  Just Refl -> LocPrf r
  Nothing -> NoLocPrf 


type instance LocationK "register" = MT.Type
type instance AsK "register" tp1 = tp1

instance IsLocation sym arch "register" where
  type LocationType sym arch "register" = MM.ArchReg arch
  type Valid sym arch "register" = MM.RegisterInfo (MM.ArchReg arch)
  mapLocExpr _ _ r = return r
  prettyLoc r = PP.pretty (showF r)
  ordFLoc v1 v2 = compareF v1 v2

pattern Register :: forall sym arch nm (k :: LocationK nm). () => (Valid sym arch nm, nm ~ "register") => MM.ArchReg arch (AsK "register" k) -> Location sym arch nm k
pattern Register r <- ((\l -> asProof @"register" l) -> LocPrf r)
  where
    Register r = Location @"register" r

type instance LocationK "cell" = Nat
type instance AsK "cell" tp1 = tp1

instance IsLocation sym arch "cell" where
  type LocationType sym arch "cell" = PMC.MemCell sym arch
  type Valid sym arch "cell" = (OrdF (W4.SymExpr sym), W4.IsExprBuilder sym)
  mapLocExpr sym f cell = PEM.mapExpr sym f cell
  prettyLoc c = PMC.ppCell c
  ordFLoc v1 v2 = compareF v1 v2

pattern Cell :: forall sym arch nm k. () => (Valid sym arch nm, nm ~ "cell") => PMC.MemCell sym arch (AsK "cell" k) -> Location sym arch nm (k :: (LocationK nm))
pattern Cell r <- ((\l -> asProof @"cell" l) -> LocPrf r)
  where
    Cell r = Location @"cell" r

type instance LocationK "expr" = W4.BaseType
type instance AsK "expr" tp1 = tp1

instance IsLocation sym arch "expr" where
  type LocationType sym arch "expr" = W4.SymExpr sym
  type Valid sym arch "expr" = W4.IsSymExprBuilder sym

  mapLocExpr _sym f expr = f expr
  prettyLoc expr = W4.printSymExpr expr
  ordFLoc v1 v2 = compareF v1 v2

pattern Expr :: forall sym arch nm k. () => (Valid sym arch nm, nm ~ "expr") => W4.SymExpr sym (AsK "expr" k) -> Location sym arch nm (k :: (LocationK nm))
pattern Expr r <- ((\l -> asProof @"expr" l) -> LocPrf r)
  where
    Expr r = Location @"expr" r

-- FIXME: I'm assuming we can get this from the Sing module somehow.
unitSing :: forall (k1 :: ()) (k2 :: ()). k1 :~: k2
unitSing = unsafeCoerce Refl

withUnitEq :: forall k1 k2 f g a. f (k1 :: ()) -> g (k2 :: ()) -> (k1 ~ k2 => a) -> a
withUnitEq _f _g a | Refl <- unitSing @k1 @k2 = a


-- | A "named" location is used for values which don't have an obvious
--   means to index them. Usually this is used for meta-state for the machine
--   (e.g. the nonce used by the malloc stub used to track pointer region allocations).
type instance LocationK "named" = Symbol
type instance AsK "named" tp1 = tp1

instance IsLocation sym arch "named" where
  type LocationType sym arch "named" = SymbolRepr
  type Valid sym arch "named" = ()
  mapLocExpr _ _ s = return s
  prettyLoc s = PP.pretty (symbolRepr s)
  ordFLoc = compareF


pattern Named :: 
  forall sym arch nm (k :: (LocationK nm)). () => (Valid sym arch nm, nm ~ "named") =>
  SymbolRepr (AsK "named" k) ->
  Location sym arch nm k
pattern Named r <- ((\l -> (asProof @"named" l) ) -> (LocPrf r))
  where
    Named s = Location @"named" s

concreteSymbol :: forall nm_concrete nm. KnownSymbol nm_concrete => SymbolRepr nm -> Maybe (nm :~: nm_concrete)
concreteSymbol s = testEquality s (knownSymbol @nm_concrete)

-- FIXME: Should this be deprecated in favor of only using named locations?
type instance LocationK "unit" = ()
type instance AsK "unit" tp1 = tp1
instance IsLocation sym arch "unit" where
  type LocationType sym arch "unit" = Const ()
  type Valid sym arch "unit" = ()

  mapLocExpr _sym _f x = return x
  prettyLoc _ = "()"
  ordFLoc a b = withUnitEq a b $ EQF

pattern Unit :: forall sym arch nm k. () => nm ~ "unit" => Location sym arch nm (k :: (LocationK nm))
pattern Unit <- ((\l -> asProof @"unit" l) -> LocPrf (Const ()))
  where
    Unit = Location @"unit" (Const ())

_pat_test_raw :: forall sym arch nm k. Location sym arch nm k -> LocationType sym arch nm k
_pat_test_raw l@(Location v) = if
  | Just Refl <- asSymbol @"register" l, (r :: MM.ArchReg arch tp) <- v ->  r
  | Just Refl <- asSymbol @"cell" l, (c :: PMC.MemCell sym arch w) <- v -> c
  | Just Refl <- asSymbol @"expr" l, (e :: W4.SymExpr sym tp) <- v -> e
  | Just Refl <- asSymbol @"named" l, (s :: SymbolRepr w) <- v -> s
  | Just Refl <- asSymbol @"unit" l, (Const ()) <- v -> Const ()
  | otherwise -> error "unsupported"



_pat_test :: forall sym arch nm k. Location sym arch nm k -> LocationType sym arch nm k
_pat_test l = case l of
  Register (r :: MM.ArchReg arch tp) -> r
  Cell (c :: PMC.MemCell sym arch w) -> c
  Expr (e :: W4.SymExpr sym tp) -> e
  Named (concreteSymbol @"foo" -> Just Refl) -> knownSymbol @"foo"
  Named (s :: SymbolRepr s) -> s
  Unit -> Const ()
  _ -> error "unsupported"

-- | Container for any type with a corresponding 'IsLocation' instance.
--   The type can be determined by examining the 'nm' parameter.

data Location (sym :: DK.Type) (arch :: DK.Type) (nm :: Symbol) (tp :: LocationK nm) where
  Location :: forall nm k sym arch. (AsK nm k ~ k, IsLocation sym arch nm, Valid sym arch nm) => 
    LocationType sym arch nm k -> Location sym arch nm k



instance forall sym arch nm k. PEM.ExprMappable sym (Location sym arch nm k) where
  mapExpr sym f (Location l) = Location <$> mapLocExpr  @sym @arch @nm sym f l

instance forall sym arch nm k. PP.Pretty (Location sym arch nm k) where
  pretty (Location l) = prettyLoc @sym @arch @nm l

-- We need a wrapper to define TestEquality and OrdF in order to relax
-- the constraint on the type parameter
data Location_ (sym :: DK.Type) (arch :: DK.Type) (nm :: Symbol) (tp :: k) where
  Location_ :: Location sym arch nm tp -> Location_ sym arch nm tp

instance TestEquality (Location_ sym arch nm) where
  testEquality l1 l2 = case compareF l1 l2 of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF (Location_ sym arch nm) where
  compareF (Location_ ((Location l1) :: Location sym arch nm k1)) 
           (Location_ ((Location l2) :: Location sym arch nm k2)) = ordFLoc @sym @arch @nm l1 l2

data SomeLocation sym arch = forall nm k. SomeLocation (Location sym arch nm k)

instance Eq (SomeLocation sym arch) where
  l1 == l2 = case compare l1 l2 of
    EQ -> True
    _ -> False

instance Ord (SomeLocation sym arch) where
  compare (SomeLocation ((Location l1) :: Location sym arch nm1 k1)) 
          (SomeLocation ((Location l2) :: Location sym arch nm2 k2)) = case compareF (knownSymbol @nm1) (knownSymbol @nm2) of
            EQF -> toOrdering $ (ordFLoc @sym @arch @nm1 l1 l2)
            LTF -> LT
            GTF -> GT

instance (W4.IsSymExprBuilder sym, MM.RegisterInfo (MM.ArchReg arch)) => IsTraceNode '(sym :: DK.Type,arch :: DK.Type) "loc" where
  type TraceNodeType '(sym,arch) "loc" = SomeLocation sym arch
  prettyNode () (SomeLocation l) = PP.pretty (showLoc l) PP.<> ":" PP.<+> PP.pretty l

data NamedPred sym (k :: WPM.PredOpK) (nm :: Symbol) where
  NamedPred :: (KnownSymbol nm) => { namedPredMap :: WPM.PredMap sym () k } -> NamedPred sym k nm

namedPred :: IO.MonadIO m => W4.IsExprBuilder sym => sym -> NamedPred sym k nm -> m (W4.Pred sym)
namedPred sym (NamedPred pm) = snd <$> WPM.collapse sym (\_ -> return) () pm

namedPredLoc :: forall nm sym arch k. NamedPred sym k nm -> Location sym arch "named" nm
namedPredLoc (NamedPred _) = Named knownRepr

knownNamedPred :: forall nm k sym. (KnownRepr WPM.PredOpRepr k, KnownSymbol nm) => W4.Pred sym -> NamedPred sym k nm
knownNamedPred p = NamedPred (WPM.singleton knownRepr () p)

instance PEM.ExprMappable sym (NamedPred sym k nm) where
  mapExpr _sym f (NamedPred p) = NamedPred <$> WPM.traverse p (\() -> f)

instance forall sym arch nm k. (W4.IsSymExprBuilder sym) => LocationWitherable sym arch (NamedPred sym k nm) where
  witherLocation sym np@(NamedPred pm) f = do
    let repr = WPM.predOpRepr pm
    p <- namedPred sym np
    (f (Named (knownSymbol @nm)) p) >>= \case
      Just (_, p') -> return $ NamedPred $ WPM.singleton repr () p'
      Nothing -> return $ NamedPred $ WPM.empty repr

instance forall sym arch nm k. (W4.IsSymExprBuilder sym) => LocationTraversable sym arch (NamedPred sym k nm) where
  traverseLocation sym nasms f = witherLocation sym nasms (\l p -> Just <$> f l p)

getLoc :: Location sym arch nm k -> LocationType sym arch nm k
getLoc (Location l) = l

-- TODO: this can be abstracted over 'W4.Pred'

-- | Defines 'f' to be viewed as a witherable (traversable but
-- optionally dropping elements instead of updating them) collection of
-- 'Location' elements paired with 'W4.Pred' elements.
class LocationWitherable sym arch f where
  -- | Traverse 'f' and map each element pair, optionally dropping
  -- it by returning 'Nothing'
  witherLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall nm (k :: LocationK nm). Location sym arch nm k -> W4.Pred sym -> m (Maybe (LocationType sym arch nm k, W4.Pred sym))) ->
    m f

-- | Defines 'f' to be viewed as a traversable collection of
-- 'Location' elements paired with 'W4.Pred' elements.
class LocationTraversable sym arch f where
  traverseLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall nm (k :: LocationK nm). Location sym arch nm k -> W4.Pred sym -> m (LocationType sym arch nm k, W4.Pred sym)) ->
    m f

  -- | Return the first location (according to the traversal order
  -- defined by 'traverseLocation') where the given function returns
  -- a 'Just' result
  firstLocation ::
    IO.MonadIO m =>
    sym ->
    f ->
    (forall nm (k :: LocationK nm). Location sym arch nm k -> W4.Pred sym -> m (Maybe a)) ->
    m (Maybe a)
  firstLocation sym body f = do
    r <- runExceptT $ do
      _ <- traverseLocation sym body $ \loc v' -> do
        lift (f loc v') >>= \case
          Just a -> throwE a
          Nothing -> return $ (getLoc loc, v')
      return ()
    case r of
      Left a -> return $ Just a
      Right () -> return Nothing

  -- | Fold over 'f' (according to its traversal order
  -- defined by 'traverseLocation')
  foldLocation ::
    forall m a.
    IO.MonadIO m =>
    sym ->
    f ->
    a ->
    (forall nm (k :: LocationK nm). a -> Location sym arch nm k -> W4.Pred sym -> m a) ->
    m a
  foldLocation sym body init_ f = execStateT g init_
    where
      g :: StateT a m ()
      g = do
        _ <- traverseLocation @sym @arch sym body $ \loc v' -> do
          a <- get
          a' <- lift (f a loc v')
          put a'
          return $ (getLoc loc, v')
        return ()


instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) =>
  LocationWitherable sym arch (PMC.MemCellPred sym arch k) where
  witherLocation sym mp f = fmap WPM.dropUnit $ WPM.alter sym mp $ \(Some c) p -> PMC.viewCell c $
    f (Cell c) p >>= \case
      Just (c', p') -> return $ (Some c', p')
      Nothing -> return $ (Some c, WPM.predOpUnit sym (typeRepr mp))


instance (W4.IsExprBuilder sym, OrdF (W4.SymExpr sym)) =>
  LocationTraversable sym arch (PMC.MemCellPred sym arch k) where
  traverseLocation sym mp f = witherLocation sym mp (\l p -> Just <$> f l p)


instance (LocationTraversable sym arch a, LocationTraversable sym arch b) =>
  LocationTraversable sym arch (a, b) where
  traverseLocation sym (a, b) f = (,) <$> traverseLocation sym a f <*> traverseLocation sym b f

instance (forall bin. (LocationWitherable sym arch (f bin))) =>
  LocationWitherable sym arch (PPa.PatchPair f) where
  witherLocation sym pp f = TF.traverseF (\x -> witherLocation sym x f) pp


