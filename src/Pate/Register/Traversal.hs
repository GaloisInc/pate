{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}

module Pate.Register.Traversal (
    zipWithRegStatesPar
  , zipWithRegStatesM
  , assocs
  , collapse
  ) where

import           Control.Lens ( (^.) )
import           Data.Functor.Const ( Const(..) )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some

import qualified Data.Macaw.CFG as MM

import qualified Pate.Parallel as PP

assocs :: MM.RegState r (Const v) -> [(Some r, v)]
assocs regs = map (\(MapF.Pair r (Const v)) -> (Some r, v)) $ MapF.toList (MM.regStateMap regs)

collapse ::
  Monoid v =>
  MM.RegState r (Const v) ->
  v
collapse regs = mconcat $ map snd $ assocs regs

newtype FutureF future f tp where
  FutureF :: future (f tp) -> FutureF future f tp

zipWithRegStatesPar :: PP.IsFuture m future
                => MM.RegisterInfo r
                => MM.RegState r f
                -> MM.RegState r g
                -> (forall u. r u -> f u -> g u -> m (future (h u)))
                -> m (future (MM.RegState r h))
zipWithRegStatesPar regs1 regs2 f = do
  regs' <- MM.traverseRegsWith (\r v1 -> FutureF <$> f r v1 (regs2 ^. MM.boundValue r)) regs1
  PP.promise $ MM.traverseRegsWith (\_ (FutureF v) -> PP.joinFuture v) regs'

zipWithRegStatesM :: Monad m
                  => MM.RegisterInfo r
                  => MM.RegState r f
                  -> MM.RegState r g
                  -> (forall u. r u -> f u -> g u -> m (h u))
                  -> m (MM.RegState r h)
zipWithRegStatesM regs1 regs2 f = MM.mkRegStateM (\r -> f r (regs1 ^. MM.boundValue r) (regs2 ^. MM.boundValue r))

