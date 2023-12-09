{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}

-- | An 'Ctx.Assignment' with distinct elements, providing a reverse map
--   from elements to indexes
module Data.Parameterized.SetCtx 
  ( SetCtx,
    toAssignment,
    empty,
    lookup,
    adjust,
    member,
    lastIndex,
    size,
    fromList,
    insertMaybe
  ) 
  where

import           Prelude hiding (lookup)
import           Data.Parameterized.Classes ( OrdF )
import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Kind (Type)
import GHC.TypeLits

#ifdef UNSAFE_OPS 
import Unsafe.Coerce (unsafeCoerce)
#endif

data SetCtx (f :: k -> Type) (ctx :: Ctx.Ctx k) =
  -- the map is maintained as a bijection, so we can recover an 'Ctx.Assignment'
  -- by sorting the elements based on the index
  SetCtx { size :: Ctx.Size ctx, _map :: (MapF f (Ctx.Index ctx)) }

asnFromMap :: forall ctx f. Ctx.Size ctx -> MapF (Ctx.Index ctx) f -> Maybe (Ctx.Assignment f ctx)
#ifdef UNSAFE_OPS
-- if we sort the contents by their index, the result should be a list of elements in
-- order according to 'ctx'
asnFromMap sz m 
  | MapF.size m == Ctx.sizeInt sz
  , es <- MapF.toAscList m
  , Some (ls :: Ctx.Assignment f ctx') <- Ctx.fromList $ (map (\(MapF.Pair _ a) -> Some a) es)
  = Just (unsafeCoerce ls)
asnFromMap _ _ = Nothing
#else
asnFromMap sz m =
  Ctx.generateM sz $ \idx -> 
    case MapF.lookup idx m of
      Just a -> return a
      Nothing -> fail "asnFromCompleteMap: incomplete indexes"
#endif

toAssignment :: SetCtx f ctx -> Ctx.Assignment f ctx
toAssignment (SetCtx sz m) = 
    let elems = MapF.fromList $ map (\(MapF.Pair e idx) -> (MapF.Pair idx e)) (MapF.toList m)
    in case asnFromMap sz elems of
        Just asn -> asn
        Nothing -> error "toAssignment: unexpected incomplete indexes"

empty :: SetCtx f Ctx.EmptyCtx
empty = SetCtx Ctx.zeroSize MapF.empty 

coerceMap :: forall f ctx tp. MapF f (Ctx.Index ctx) -> MapF f (Ctx.Index (ctx Ctx.::> tp))
coerceMap m =
#ifdef UNSAFE_OPS 
  unsafeCoerce m
#else
  MapF.map Ctx.skipIndex m
#endif

member :: OrdF f => f tp -> SetCtx f ctx -> Bool
member e (SetCtx _ m) = MapF.member e m

lookup :: OrdF f => f tp -> SetCtx f ctx -> Maybe (Ctx.Index ctx tp)
lookup e (SetCtx _ m) = MapF.lookup e m

-- | NB: This is unsafe to export because there is no guarantee that the provided element
--   isn't already in the underlying assignment
append :: OrdF f => f tp -> SetCtx f ctx -> SetCtx f (ctx Ctx.::> tp)
append e (SetCtx sz m) = 
  let idx = Ctx.nextIndex sz
  in (SetCtx (Ctx.incSize sz) (MapF.insert e idx (coerceMap m)))

insertMaybe ::
  OrdF f => 
  f tp ->
  SetCtx f ctx ->
  Either (Ctx.Index ctx tp) (SetCtx f (ctx Ctx.::> tp))
insertMaybe e idx_asn = case lookup e idx_asn of
  Just idx -> Left idx
  Nothing -> Right (append e idx_asn)


adjust ::
  forall f tp ctx a.
  OrdF f => 
  f tp ->
  SetCtx f ctx ->
  (forall ctx'. (Ctx.KnownContext ctx', Ctx.CtxSize ctx' <= 1) => 
    Ctx.Index (ctx Ctx.<+> ctx') tp -> SetCtx f (ctx Ctx.<+> ctx') -> a) ->
  a
adjust e idx_asn f = case insertMaybe e idx_asn of
  Left idx -> f @Ctx.EmptyCtx idx idx_asn
  Right idx_asn' -> f @(Ctx.SingleCtx tp) (lastIndex idx_asn') idx_asn'

fromList :: forall f. OrdF f => [Some f] -> Some (SetCtx f)
fromList es_outer = go es_outer empty
    where
        go :: forall ctx. [Some f] -> SetCtx f ctx -> Some (SetCtx f)
        go (Some e: es) idxasn = case insertMaybe e idxasn of
            Left{} -> Some idxasn
            Right idxasn' -> go es idxasn'
        go [] idxasn = Some idxasn

lastIndex :: SetCtx f (ctx Ctx.::> tp) -> Ctx.Index (ctx Ctx.::> tp) tp
lastIndex (SetCtx sz _) = Ctx.lastIndex sz