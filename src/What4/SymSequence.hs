
{-|
Module           : What4.SymSequence
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Additional operations on Lang.Crucible.Simulator.SymSequence

-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes #-}

module What4.SymSequence
( takeMatchingPrefix
, takeMatchingPrefix2
, reverseSeq
, collapsePartialSeq
, compareSymSeq
, concatSymSequence
, feasiblePaths
, mapConcatSeq
, muxTreeToSeq
, module Lang.Crucible.Simulator.SymSequence
) where

import           Control.Monad (forM)
import qualified Control.Monad.IO.Class as IO

import qualified Prettyprinter as PP

import           What4.Interface as W4
import           What4.Partial
import           Lang.Crucible.Simulator.SymSequence

import qualified Pate.ExprMappable as PEM
import qualified What4.JSON as W4S
import           What4.JSON ( (.=) ) 
import qualified Data.Aeson as JSON
import Lang.Crucible.Utils.MuxTree
import qualified Data.IORef as IO
import qualified Data.Map as Map
import Data.Parameterized.Nonce
import Data.Functor.Const
import Data.Maybe (catMaybes)

instance PEM.ExprMappable sym a => PEM.ExprMappable sym (SymSequence sym a) where
  mapExpr sym f = evalWithFreshCache $ \rec -> \case
    SymSequenceNil -> IO.liftIO $ nilSymSequence sym
    SymSequenceCons _ x xs ->
      do x'  <- PEM.mapExpr sym f x
         xs' <- rec xs
         IO.liftIO $ consSymSequence sym x' xs'
    SymSequenceAppend _ xs ys ->
     do xs' <- rec xs
        ys' <- rec ys
        IO.liftIO $ appendSymSequence sym xs' ys'
    SymSequenceMerge _ p xs ys ->
     do p' <- f p
        case asConstantPred p' of
          Just True -> rec xs
          Just False -> rec ys
          Nothing -> do
            xs' <- rec xs
            ys' <- rec ys
            IO.liftIO $ muxSymSequence sym p' xs' ys'


singleSeq ::
  forall sym a.
  IsExprBuilder sym =>
  sym ->
  a ->
  IO (SymSequence sym a)
singleSeq sym a = do
  n <- nilSymSequence sym
  consSymSequence sym a n

-- | Convert a 'MuxTree' into a sequence with length at most 1, collapsing all 'Nothing' results
--   from the given function into an empty sequence.
muxTreeToSeq ::
  forall sym a b.
  IsExprBuilder sym =>
  sym ->
  (a -> IO (Maybe b)) ->
  MuxTree sym a ->
  IO (SymSequence sym b)
muxTreeToSeq sym f mt = do
  es <- fmap catMaybes $ forM (viewMuxTree mt) $ \(x, p) -> f x >>= \case
    Just y -> return $ Just (p, y)
    Nothing -> return Nothing
  collect es
  where
    collect :: [(Pred sym, b)] -> IO (SymSequence sym b)
    collect [] = nilSymSequence sym
    collect ((p,y):ys) = do
      y_seq <- singleSeq sym y
      ys_seq <- collect ys
      muxSymSequence sym p y_seq ys_seq

-- | Smarter mux that checks for predicate concreteness
muxSymSequence' ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  SymSequence sym a ->
  SymSequence sym a ->
  m (SymSequence sym a)
muxSymSequence' sym p sT sF = case asConstantPred p of
  Just True -> return sT
  Just False -> return sF
  Nothing -> IO.liftIO $ muxSymSequence sym p sT sF


appendSingle ::
  IO.MonadIO m =>
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  a ->
  m (SymSequence sym a)
appendSingle sym s a = IO.liftIO $ do
  a_seq <- consSymSequence sym a =<< nilSymSequence sym
  appendSymSequence sym s a_seq

muxSeqM ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a) ->
  m (SymSequence sym a) ->
  m (SymSequence sym a)
muxSeqM sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    aT <- f_s1
    aF <- f_s2
    muxSymSequence' sym p aT aF

muxSeqM2 ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a, SymSequence sym b) ->
  m (SymSequence sym a, SymSequence sym b) ->
  m (SymSequence sym a, SymSequence sym b)
muxSeqM2 sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    (a1,b1) <- f_s1
    (a2,b2) <- f_s2
    a <- muxSymSequence' sym p a1 a2
    b <- muxSymSequence' sym p b1 b2
    return $ (a,b)

-- | Apply a partial function to a sequence, returning the longest
--   prefix of nonempty results.
--   For example, given any predicate 'p' and 'f a :=  if p a then Just a else Nothing'
--   Then we expect the following to hold:
--     let (result, as_suffix) = takeMatchingPrefix f as
--     in   result ++ as_suffix == as
--       && all r result
--       && not (p (head as_suffix))
--   Notably this is semantic equality since 'p' is a symbolic predicate
--   TODO: caching?
--   TODO: if 'a' and 'b' are the same type there are a few optimizations
--     that could be made to avoid re-creating sub-sequences
takeMatchingPrefix ::
  forall sym m a b.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> m (PartExpr (Pred sym) b)) ->
  SymSequence sym a ->
  m (SymSequence sym b, SymSequence sym a)
takeMatchingPrefix sym f s_a_outer = go SymSequenceNil s_a_outer
  where
    go :: SymSequence sym b -> SymSequence sym a -> m (SymSequence sym b, SymSequence sym a)
    go acc s_a = case s_a of
      SymSequenceNil -> return $ (acc, s_a)
      (SymSequenceCons _ a s_a') -> do
        f a >>= \case
          Unassigned -> return $ (acc, s_a)
          PE p v -> muxSeqM2 sym p
            -- for a 'Just' result we add it to the accumulated prefix and continue
            ((IO.liftIO $ appendSingle sym acc v) >>= \acc' -> go acc' s_a')
            -- otherwise we return the current accumulated prefix and stop
            (return (acc, s_a))
      (SymSequenceAppend _ a1 a2) -> do
        (acc', a1_suf) <- go acc a1
        p <- IO.liftIO $ isNilSymSequence sym a1_suf
        muxSeqM2 sym p
          (go acc' a2) $ do
            a2_suf <- if a1 == a1_suf then return s_a
              else IO.liftIO $ appendSymSequence sym a1_suf a2
            return (acc', a2_suf)
      (SymSequenceMerge _ p a_T a_F) -> muxSeqM2 sym p (go acc a_T) (go acc a_F)

muxSeqM3 ::
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  Pred sym ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c) ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c) ->
  m (SymSequence sym a, SymSequence sym b, SymSequence sym c)
muxSeqM3 sym p f_s1 f_s2 = case asConstantPred p of
  Just True -> f_s1
  Just False -> f_s2
  Nothing -> do
    (a1,b1,c1) <- f_s1
    (a2,b2,c2) <- f_s2
    a <- muxSymSequence' sym p a1 a2
    b <- muxSymSequence' sym p b1 b2
    c <- muxSymSequence' sym p c1 c2
    return $ (a,b,c)


-- TODO: This is a duplicate of Pate.Verification.StrongestPosts.SeqPairCache
-- Replacing 'equivalentSequences' in that module with 'compareSymSeq' will also
-- let us remove the duplicates there
data SeqPairCache a b c = SeqPairCache (IO.IORef (Map.Map (Maybe (Nonce GlobalNonceGenerator a), Maybe (Nonce GlobalNonceGenerator b)) c))

newSeqPairCache :: IO (SeqPairCache a b c)
newSeqPairCache = SeqPairCache <$> IO.newIORef Map.empty

-- TODO: clagged from SymSequence module, should probably be exported, either
-- directly or with some abstraction for the nonces
symSequenceNonce :: SymSequence sym a -> Maybe (Nonce GlobalNonceGenerator a)
symSequenceNonce SymSequenceNil = Nothing
symSequenceNonce (SymSequenceCons n _ _ ) = Just n
symSequenceNonce (SymSequenceAppend n _ _) = Just n
symSequenceNonce (SymSequenceMerge n _ _ _) = Just n

-- TODO: duplicated in Pate.Verification.StrongestPosts, see above
evalWithPairCache :: IO.MonadIO m =>
  SeqPairCache a b c ->
  SymSequence sym a ->
  SymSequence sym b ->
  m c ->
  m c
evalWithPairCache (SeqPairCache ref) seq1 seq2 f = do
  m <- IO.liftIO (IO.readIORef ref)
  let k = (symSequenceNonce seq1, symSequenceNonce seq2)
  case Map.lookup k m of
    Just v -> return v
    Nothing -> do
      v <- f
      IO.liftIO (IO.modifyIORef ref (Map.insert k v))
      return v

zipSeq' ::
  forall sym a b.
  IsSymExprBuilder sym =>
  sym ->
  SeqPairCache a b (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b) ->
  SymSequence sym a ->
  SymSequence sym b ->
  IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
zipSeq' sym cache as_outer bs_outer = go as_outer bs_outer
  where
    handle_append :: forall x y.
      (SymSequence sym x -> SymSequence sym y -> IO (SymSequence sym (a,b), SymSequence sym x, SymSequence sym y)) ->
      SymSequence sym x ->
      SymSequence sym y ->
      Maybe (IO (SymSequence sym (a,b), SymSequence sym x, SymSequence sym y))
    handle_append rec xs@(SymSequenceAppend _ xs_1 xs_2) ys = Just $ do
      (acc, xs_suf', ys_suf) <- rec xs_1 ys
      p <- isNilSymSequence sym xs_suf'
      (acc', xs_fin, ys_fin) <- muxSeqM3 sym p
        -- if xs_suf' is nil then it means we consumed all of the first
        -- and thus we can continue zipping elements
        (do
          (acc', xs_fin, ys_fin) <- rec xs_2 ys_suf
          return (acc', xs_fin, ys_fin)
          ) $ do
          -- otherwise, we append the tail to the found suffix and return
          -- as a small optimization, if the suffix is the same as the input
          -- then we don't need to create a new sequence for appended suffix
        xs_suf'' <- if xs_suf' == xs_1 then return xs
          else appendSymSequence sym xs_suf' xs_2
        return $ (SymSequenceNil, xs_suf'', ys_suf)
      acc'' <- appendSymSequence sym acc acc'
      return (acc'', xs_fin, ys_fin)

    handle_append _ _ _ = Nothing
    go' :: SymSequence sym b -> SymSequence sym a -> IO (SymSequence sym (a,b), SymSequence sym b, SymSequence sym a)
    go' s_b s_a = go s_a s_b >>= \(acc, s_a', s_b') -> return (acc, s_b', s_a')

    go :: SymSequence sym a -> SymSequence sym b -> IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
    go s_a s_b = evalWithPairCache cache s_a s_b $ case (s_a, s_b) of
      -- if either sequence is nil that we can't extend the matching prefix any more
      -- and so we return
      (_, SymSequenceNil) -> return $ (SymSequenceNil, s_a, s_b)
      (SymSequenceNil, _) -> return $ (SymSequenceNil, s_a, s_b)
      (SymSequenceCons _ a s_a', SymSequenceCons _ b s_b') -> do

        (acc, suf_a, suf_b) <- go s_a' s_b'
        acc' <- IO.liftIO $ appendSingle sym acc (a,b)
        return (acc', suf_a, suf_b)
      _ | Just g <- handle_append go s_a s_b -> g
      _ | Just g <- handle_append go' s_b s_a -> g >>= \(acc', s_b', s_a') -> return (acc', s_a', s_b')
      (SymSequenceMerge _ p_a a_T a_F, SymSequenceMerge _ p_b b_T b_F)
        | Just Refl <- testEquality p_a p_b -> muxSeqM3 sym p_a (go a_T b_T)  (go a_F b_F)
      (SymSequenceMerge _ p_a a_T a_F, SymSequenceMerge _ p_b b_T b_F) -> do
        p_a_p_b <- andPred sym p_a p_b
        not_p_a <- notPred sym p_a
        not_p_b <- notPred sym p_b
        not_p_a_not_p_b <- andPred sym not_p_a not_p_b

        muxSeqM3 sym p_a_p_b (go a_T b_T) $
          muxSeqM3 sym not_p_a_not_p_b (go a_F b_F) $
            muxSeqM3 sym p_a (go a_T b_F) (go a_F b_T)

      (SymSequenceMerge _ p a_T a_F, _) -> muxSeqM3 sym p (go a_T s_b) (go a_F s_b)
      (_, SymSequenceMerge _ p b_T b_F) -> muxSeqM3 sym p (go s_a b_T) (go s_a b_F)
      (SymSequenceAppend{}, _) -> error "zipSeq: handle_append unexpectedly failed"
      (_, SymSequenceAppend{}) -> error "zipSeq: handle_append unexpectedly failed"


-- | Zip two sequences pointwise. If one is longer than the other, return
--   the suffix of elements.
--   Notably this is not an 'Either' result (i.e. returning only the suffix of the longer sequence),
--   as both suffixes may be nontrivial and symbolic.
zipSeq ::
  forall sym a b.
  IsSymExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  SymSequence sym b ->
  IO (SymSequence sym (a,b), SymSequence sym a, SymSequence sym b)
zipSeq sym as bs = newSeqPairCache >>= \cache -> zipSeq' sym cache as bs

unzipSeq ::
  forall sym a b.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym (a,b) ->
  IO (SymSequence sym a, SymSequence sym b)
unzipSeq sym s = do
  s_a <- traverseSymSequence sym (\(a, _) -> return a) s
  s_b <- traverseSymSequence sym (\(_, b) -> return b) s
  return (s_a, s_b)

-- | Same as 'evalWithFreshCache' but without the result type depending on 'a'
evalWithFreshCache' ::
  forall sym m a b.
  IO.MonadIO m =>
  ((SymSequence sym a -> m b) -> SymSequence sym a -> m b) ->
  (SymSequence sym a -> m b)
evalWithFreshCache' f s_outer = getConst <$> evalWithFreshCache (\rec s -> Const <$> f (do_wrap rec) s) s_outer
  where
    do_wrap :: (SymSequence sym a -> m (Const b a)) -> (SymSequence sym a -> m b)
    do_wrap g = \s -> getConst <$> g s

mapConcatSeq ::
  forall sym m a b.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> m (SymSequence sym b)) ->
  SymSequence sym a ->
  m (SymSequence sym b)
mapConcatSeq sym f s_a_outer = evalWithFreshCache' go s_a_outer
  where
    go :: (SymSequence sym a -> m (SymSequence sym b)) -> SymSequence sym a -> m (SymSequence sym b)
    go _ SymSequenceNil = IO.liftIO $ nilSymSequence sym
    go rec (SymSequenceCons _ a as) = do
      bs <- f a
      bs' <- rec as
      IO.liftIO $ appendSymSequence sym bs bs'
    go rec (SymSequenceAppend _ as1 as2) = do
      bs1 <- rec as1
      bs2 <- rec as2
      IO.liftIO $ appendSymSequence sym bs1 bs2
    go rec (SymSequenceMerge _ p asT asF) =
      muxSeqM sym p (rec asT) (rec asF)

partToSeq ::
  forall sym c.
  IsExprBuilder sym =>
  sym ->
  PartExpr (Pred sym) c ->
  IO (SymSequence sym c)
partToSeq sym = \case
  Unassigned -> nilSymSequence sym
  PE p c -> muxSeqM sym p (singleSeq sym c) (nilSymSequence sym)

-- | Collapses partial elements into empty sub-sequences
collapsePartialSeq ::
  forall sym c.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym (PartExpr (Pred sym) c) ->
  IO (SymSequence sym c)
collapsePartialSeq sym s_outer = mapConcatSeq sym (partToSeq sym) s_outer

-- | Apply a partial function pairwise to two sequences, returning the longest
--   prefix of nonempty results.
--   For example, given any relation 'r' and 'f a b :=  if r (a, b) then Just (a, b) else Nothing'
--   Then we expect the following to hold:
--     let (result, as_suffix, bs_suffix) = takeMatchingPrefix2 f as bs
--     in   (map fst result) ++ as_suffix == as
--       && (map snd result) ++ bs_suffix == bs
--       && all r result
--       && not (r (head as_suffix, head bs_suffix))
--   Notably this is semantic equality since 'r' is a symbolic relation
--   TODO: caching?
takeMatchingPrefix2 ::
  forall sym m a b c.
  IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (a -> b -> m (PartExpr (Pred sym) c)) ->
  SymSequence sym a ->
  SymSequence sym b ->
  m (SymSequence sym c, SymSequence sym a, SymSequence sym b)
takeMatchingPrefix2 sym f s_a_outer s_b_outer = do
  (zipped, as_suffix, bs_suffix) <- IO.liftIO $ zipSeq sym s_a_outer s_b_outer
  (matching_prefix, as_bs_suffix) <- takeMatchingPrefix sym (\(a,b) -> f a b) zipped
  (as_suffix', bs_suffix') <- IO.liftIO $ unzipSeq sym as_bs_suffix
  as_suffix'' <- IO.liftIO $ appendSymSequence sym as_suffix' as_suffix
  bs_suffix'' <- IO.liftIO $ appendSymSequence sym bs_suffix' bs_suffix
  return (matching_prefix, as_suffix'', bs_suffix'')

-- | Reverse the order of elements in a sequence
reverseSeq ::
  forall sym a.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  IO (SymSequence sym a)
reverseSeq sym s_outer = evalWithFreshCache go s_outer
  where
    go :: (SymSequence sym a -> IO (SymSequence sym a)) -> SymSequence sym a -> IO (SymSequence sym a)
    go _ SymSequenceNil = nilSymSequence sym
    go rec (SymSequenceCons _ a as) = rec as >>= \as_rev -> appendSingle sym as_rev a
    go rec (SymSequenceAppend _ as bs) = do
      as_rev <- rec as
      bs_rev <- rec bs
      appendSymSequence sym bs_rev as_rev
    go rec (SymSequenceMerge _ p sT sF) = do
      sT_rev <- rec sT
      sF_rev <- rec sF
      muxSymSequence sym p sT_rev sF_rev

-- | Concatenate the elements of a 'SymSequence' together
--   using the provided combine and mux operations and
--   empty value.
concatSymSequence ::
  forall sym m c.
  IsExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (Pred sym -> c -> c -> m c) {-^ mux for 'c' -} ->
  (c -> c -> m c) {-^ combining 'c' values -} ->
  c {-^ empty c -} ->
  SymSequence sym c ->
  m c
concatSymSequence _sym f g c_init s_outer = getConst <$> evalWithFreshCache go s_outer
  where
    go :: (SymSequence sym c -> m ((Const c) c)) -> SymSequence sym c -> m ((Const c) c)
    go rec s = fmap Const $ case s of
      SymSequenceNil -> return $ c_init
      SymSequenceCons _ c1 sa -> do
        Const c2 <- rec sa
        g c1 c2
      SymSequenceAppend _ sa1 sa2 -> do
        Const c1 <- rec sa1
        Const c2 <- rec sa2
        g c1 c2
      SymSequenceMerge _ p' saT saF -> do
        Const cT <- rec saT
        Const cF <- rec saF
        f p' cT cF

-- | Pointwise comparison of two sequences. When they are (semantically) not
--   the same length, the resulting predicate is False. Otherwise it is
--   the result of 'f' on each pair of values.
--   TODO: Pate.Verification.StrongestPosts.equivalentSequences should be
--   replaced with this. They are semantically equivalent, however
--   'zipSeq' creates more concise terms in cases where the predicates
--   for sequence merges aren't exactly equivalent between the two sequences.

compareSymSeq ::
  forall sym a b m.
  IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  SymSequence sym a ->
  SymSequence sym b ->
  (a -> b -> m (Pred sym)) ->
  m (Pred sym)
compareSymSeq sym sa sb f = do
  (matching_pfx, suf_a, suf_b) <- IO.liftIO $ zipSeq sym sa sb
  f_seq <- traverseSymSequence sym (\(a,b) -> f a b) matching_pfx
  nil_a <- IO.liftIO $ isNilSymSequence sym suf_a
  nil_b <- IO.liftIO $ isNilSymSequence sym suf_b

  matching_head <- concatSymSequence sym
    (\p a b -> IO.liftIO $ baseTypeIte sym p a b)
    (\a b -> IO.liftIO $ andPred sym a b)
    (truePred sym)
    f_seq
  IO.liftIO $ andPred sym matching_head nil_a >>= andPred sym nil_b

-- | Simplify a SymSequence by considering path satisfiability
--   according to the given functions.
feasiblePaths ::
  forall m sym a.
  IsSymExprBuilder sym =>
  IO.MonadIO m =>
  sym ->
  (forall b. Pred sym -> m b -> m b) {-^ perform any operation under a given assumption -} ->
  (Pred sym -> m (Maybe Bool)) {-^ decide predicate cases: necessarily true, necessarily false, or neither -} ->
  SymSequence sym a ->
  m (SymSequence sym a)
feasiblePaths sym with_asm dec_pred = go
  where
    -- NOTE: We explicitly *don't* want to use caching because we're relying on context in the monad
    go :: SymSequence sym a -> m (SymSequence sym a)
    go s = case s of
      SymSequenceNil -> return $ SymSequenceNil
      SymSequenceCons _ a as -> do
        as' <- go as
        if as == as' 
          then return s 
          else IO.liftIO $ consSymSequence sym a as'
      SymSequenceAppend _ as1 as2 -> do
        as1' <- go as1
        as2' <- go as2
        if as1' == as1 && as2' == as2
          then return s
          else IO.liftIO $ appendSymSequence sym as1' as2'
      SymSequenceMerge _ p asT asF -> do
        dec_pred p >>= \case
          Just True -> return asT
          Just False -> return asF
          Nothing -> do
            asT' <- with_asm p $ go asT
            not_p <- IO.liftIO $ W4.notPred sym p
            asF' <- with_asm not_p $ go asF
            if asT == asT' && asF == asF' then
              return s
            else IO.liftIO $ muxSymSequence sym p asT asF