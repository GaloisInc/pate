{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module What4.Simplify.Bitvector (
    memReadPrettySimplify
  , memWritePrettySimplify
  , bvPrettySimplify
  , collapseBVOps
  , asSimpleSum
) where

import           GHC.TypeNats
import           Control.Lens ( (.~), (&), (^.) )

import           Control.Monad
import           Control.Applicative
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.Trans

import           Data.List ( permutations )

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Vector as V

import           What4.Simplify
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import qualified What4.Expr.BoolMap as BM
import Data.List.NonEmpty
import qualified What4.Concrete as W4C
import qualified Data.BitVector.Sized as BVS
import qualified What4.SemiRing as SR
import qualified What4.Expr.WeightedSum as WSum


-- ======================================
-- Detecting memory-like array accesses and wrapping them in defined
-- functions. Specifically we look for a concatenation of bitvectors
-- from an array where the indexes (addresses) are sequential.
-- i.e. concat (select arr 0) (select arr 1) --> readLE2 0

data BVConcatResult sym w_outer w_inner where
  BVConcatResult :: forall n sym w_inner. (1 <= n, 1 <= w_inner) => 
    W4.NatRepr n -> W4.NatRepr w_inner -> V.Vector n (W4.SymBV sym w_inner) -> BVConcatResult sym (n * w_inner) w_inner

bvConcatResultWidth :: BVConcatResult sym w_outer w_inner -> W4.NatRepr w_inner
bvConcatResultWidth = \case
 BVConcatResult _ w _ -> w

combineBVConcatResults ::
  BVConcatResult sym w_outer1 w_inner ->
  BVConcatResult sym w_outer2 w_inner ->
  BVConcatResult sym (w_outer1 + w_outer2) w_inner
combineBVConcatResults (BVConcatResult lhs_n_inner lhs_w_inner lhs_bvs) (BVConcatResult rhs_n_inner _ rhs_bvs) 
  | Refl <- W4.addMulDistribRight lhs_n_inner rhs_n_inner lhs_w_inner
    , W4.LeqProof <- W4.leqAddPos  lhs_n_inner rhs_n_inner
    = BVConcatResult (W4.addNat lhs_n_inner rhs_n_inner) lhs_w_inner (V.append lhs_bvs rhs_bvs)


-- Could be implemented as a pure/total function, since
-- there is always a base case of no concatenations
getBVConcats ::
  Monad m =>
  W4.SymBV sym w ->
  SimpT sym m (Some (BVConcatResult sym w))
getBVConcats e = withSym $ \_ -> do
  W4B.BVConcat _ lhs rhs <- asApp e
  getBVConcatsApp lhs rhs
  <|> do
    W4.BaseBVRepr w <- return $ W4.exprType e
    return $ Some $ BVConcatResult (W4.knownNat @1) w (V.singleton e)

getBVConcatsApp ::
  Monad m =>
  W4.SymBV sym w1 ->
  W4.SymBV sym w2 ->
  SimpT sym m (Some (BVConcatResult sym (w1 + w2)))
getBVConcatsApp lhs rhs = do
  Some lhs_result <- getBVConcats lhs
  Some rhs_result <- getBVConcats rhs
  lhs_inner_w <- return $ bvConcatResultWidth lhs_result
  rhs_inner_w <- return $ bvConcatResultWidth rhs_result
  Refl <- simpMaybe $ testEquality lhs_inner_w rhs_inner_w
  return $ Some $ combineBVConcatResults lhs_result rhs_result

asSequential ::
  forall m sym w n.
  IO.MonadIO m =>
  Bool ->
  W4.BoundVar sym (W4.BaseBVType w) ->
  V.Vector n (W4.SymBV sym w) -> 
  SimpT sym m (V.Vector n (W4.SymBV sym w))
asSequential be var v_outer = go 0 v_outer
  where
    go :: forall n_. Integer -> V.Vector n_ (W4.SymBV sym w) -> SimpT sym m (V.Vector n_ (W4.SymBV sym w))
    go offset v = withSym $ \sym -> do

      let (x1, rest) = next_bv v
      W4.BaseBVRepr w <- return $ W4.exprType x1
      offset_bv <- IO.liftIO $ W4.bvLit sym w (BVS.mkBV w offset)
      var_as_offset <- IO.liftIO $ W4.bvAdd sym (W4.varExpr sym var) offset_bv
      x1_as_offset <- IO.liftIO $ W4.bvAdd sym first_bv offset_bv
      check <- IO.liftIO $ W4.isEq sym x1_as_offset x1
      case W4.asConstantPred check of
        Just True -> case rest of
          Left Refl -> return $ V.singleton var_as_offset
          Right v' -> do
            v_result <- go (offset + 1) v'
            W4.LeqProof <- return $ V.nonEmpty v
            Refl <- return $ W4.minusPlusCancel (V.length v) (W4.knownNat @1)
            return $ mk_v var_as_offset v_result
        _ -> fail $ "not sequential:" ++ show x1 ++ "vs. " ++ show x1_as_offset

    mk_v :: tp -> V.Vector n_ tp -> V.Vector (n_+1) tp
    mk_v x v_ = case be of
      True -> V.cons x v_
      False -> V.snoc v_ x

    next_bv :: forall n_ tp. V.Vector n_ tp -> (tp, Either (n_ :~: 1) (V.Vector (n_-1) tp))
    next_bv v_ = case be of
      True -> V.uncons v_
      False -> V.unsnoc v_

    first_bv = fst (next_bv v_outer)

concatBVs ::
  W4.IsExprBuilder sym =>
  sym -> 
  V.Vector n (W4.SymBV sym w) -> 
  IO (W4.SymBV sym (n*w))
concatBVs sym v = do
  let (x1, rest) = V.uncons v
  W4.BaseBVRepr w <- return $ W4.exprType x1
  case rest of
    Left Refl -> return x1
    Right v' -> do
      W4.LeqProof <- return $ V.nonEmpty v
      W4.LeqProof <- return $ V.nonEmpty v'
      bv' <- concatBVs sym v'
      W4.LeqProof <- return $ W4.leqMulPos (V.length v') w
      Refl <- return $ W4.lemmaMul w (V.length v)
      W4.bvConcat sym x1 bv'

memReadPrettySimplifyApp ::
  forall sym m tp.
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  W4B.App (W4.SymExpr sym) tp -> 
  SimpT sym m (W4.SymExpr sym tp)
memReadPrettySimplifyApp rec app = withSym $ \sym -> do
  W4B.BVConcat _ lhs rhs <- return app
  Some (BVConcatResult _ _ inner_bvs) <- getBVConcatsApp lhs rhs
  let (fst_bv, _) = V.uncons inner_bvs
  W4B.SelectArray _ arr (Ctx.Empty Ctx.:> fst_addr) <- asApp fst_bv
  W4.BaseBVRepr (addr_w :: W4.NatRepr addr_w) <- return $ W4.exprType fst_addr
  (addrs :: V.Vector n (W4.SymBV sym addr_w)) <- forM inner_bvs $ \inner_bv -> do
    W4B.SelectArray _ arr' (Ctx.Empty Ctx.:> inner_addr) <- asApp inner_bv
    Refl <- simpMaybe $ testEquality arr arr'
    return inner_addr
  tryAll [True,False] $ \b -> do
    addr_var <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.BaseBVRepr addr_w)
    addrs_seq <- asSequential b addr_var addrs
    let index_addr = if b then fst (V.uncons addrs) else fst (V.unsnoc addrs)
    arr_var <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.exprType arr)
    vals <- IO.liftIO $ mapM (\addr_ -> W4.arrayLookup sym (W4.varExpr sym arr_var) (Ctx.empty Ctx.:> addr_)) addrs_seq
    new_val <- IO.liftIO $ concatBVs sym vals
    let nm = (if b then "readBE" else "readLE") ++ show (W4.natValue (V.length addrs))
    fn <- IO.liftIO $ W4.definedFn sym (W4.safeSymbol nm) (Ctx.Empty Ctx.:> arr_var Ctx.:> addr_var) new_val W4.NeverUnfold
    arr' <- lift $ rec arr
    index_addr' <- lift $ rec index_addr
    IO.liftIO $ W4.applySymFn sym fn (Ctx.empty Ctx.:> arr' Ctx.:> index_addr') 

memReadPrettySimplify ::
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) => 
  SimpStrategy sym m
memReadPrettySimplify = liftSimpTStrategy memReadPrettySimplifyApp



asByteUpdateSequence ::
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  V.Vector n (W4.SymExpr sym (W4.BaseBVType addr_w)) ->
  W4.SymExpr sym (W4.BaseBVType w) ->
  
  W4.SymExpr sym (W4.BaseArrayType (Ctx.EmptyCtx Ctx.::> W4.BaseBVType addr_w) (W4.BaseBVType 8)) ->
  
  W4.SymExpr sym (W4.BaseBVType 8) ->
  SimpT sym m (W4.SymExpr sym (W4.BaseArrayType (Ctx.EmptyCtx Ctx.::> W4.BaseBVType addr_w) (W4.BaseBVType 8)))
asByteUpdateSequence rec acc prev_byte_base arr byte = withSym $ \sym -> do
  W4.BaseBVRepr w <- return $ W4.exprType prev_byte_base
  W4B.BVSelect fstBit nBits byte_base <- asApp byte
  Refl <- simpMaybe $ testEquality byte_base prev_byte_base

  Refl <- simpMaybe $ testEquality nBits (W4.knownNat @8)
  case W4.isZeroOrGT1 fstBit of
    Left Refl -> 
      tryAll [True,False] $ \b -> do
        let addr = fst (V.uncons acc)
        addr_var <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.exprType addr)
        addr_vars <- asSequential b addr_var acc
        val_var <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.exprType byte_base)
        arr_var <- IO.liftIO $ W4.freshBoundVar sym W4.emptySymbol (W4.exprType arr)
        W4.LeqProof <- return $ V.nonEmpty acc
        Refl <- return $ W4.minusPlusCancel (V.length acc) (W4.knownNat @1)
        val_vars <- V.generateM (W4.decNat (V.length acc)) (\n -> do
            -- TODO: should be provable
            let k = W4.natMultiply n (W4.knownNat @8)
            W4.LeqProof <- simpMaybe $ W4.testLeq (W4.addNat k (W4.knownNat @8)) w
            IO.liftIO $ W4.bvSelect sym k (W4.knownNat @8) (W4.varExpr sym val_var))
        let
          acts = V.zipWith (\addr_ val_ -> (\arr_ -> W4.arrayUpdate sym arr_ (Ctx.empty Ctx.:> addr_) val_ )) addr_vars val_vars
        body <- IO.liftIO $ foldM (\arr_ act_ -> act_ arr_) (W4.varExpr sym arr_var) acts

        let nm = (if b then "writeBE" else "writeLE") ++ show (W4.natValue (V.length addr_vars))

        fn <- IO.liftIO $ 
          W4.definedFn sym (W4.safeSymbol nm) (Ctx.empty Ctx.:> arr_var Ctx.:> addr_var Ctx.:> val_var) body W4.NeverUnfold
        
        byte_base' <- lift $ rec byte_base
        arr' <- lift $ rec arr
        addr' <- lift $ rec addr

        IO.liftIO $ W4.applySymFn sym fn (Ctx.empty Ctx.:> arr' Ctx.:> addr' Ctx.:> byte_base')
    Right W4.LeqProof -> do
      W4B.UpdateArray _ _ arr_prev (Ctx.Empty Ctx.:> addr_prev) val_prev <- asApp arr
      W4B.BVSelect fstBit' _ _ <- asApp val_prev
      -- check that we're actually grabbing the next byte
      Refl <- simpMaybe $ testEquality (W4.addNat fstBit' (W4.knownNat @8)) fstBit

      asByteUpdateSequence rec (V.cons addr_prev acc) byte_base arr_prev val_prev


memWritePrettySimplifyApp ::
  forall sym m tp.
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  W4B.App (W4.SymExpr sym) tp -> 
  SimpT sym m (W4.SymExpr sym tp)
memWritePrettySimplifyApp rec app = withSym $ \_ -> do
  W4B.UpdateArray _ _ arr_prev (Ctx.Empty Ctx.:> addr_prev) byte_prev <- return app
  W4.BaseBVRepr{} <- return $ W4.exprType addr_prev
  W4B.BVSelect _ nBits byte_base <- asApp byte_prev
  Refl <- simpMaybe $ testEquality nBits (W4.knownNat @8)
  asByteUpdateSequence rec (V.singleton addr_prev) byte_base arr_prev byte_prev

memWritePrettySimplify ::
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) => 
  SimpStrategy sym m
memWritePrettySimplify = liftSimpTStrategy memWritePrettySimplifyApp



-- ======================================
-- Bitvector simplification strategies

-- | Simplification rules that are for display purposes only,
--   as they can make terms more difficult for the solver to handle.
--   TODO: if we add implicit function unfolding to all solver calls then
--   we can safely apply these unconditionally
--   TODO: these were lifted directly from term forms that appear in the ARM semantics when comparing values,
--   but can likely be generalized.
bvPrettySimplifyApp ::
  forall sym m tp.
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  W4B.App (W4.SymExpr sym) tp -> 
  SimpT sym m (W4.SymExpr sym tp)
bvPrettySimplifyApp rec app = withSym $ \sym -> tryAll (appAlts @sym app) $ \app' -> do
  W4B.BaseEq _ (isUInt @sym 0 -> True) (W4B.asApp -> Just (W4B.BVSelect idx n bv_)) <- return app'
  W4.BaseBVRepr bv_w <- return $ W4.exprType bv_
  Refl <- simpMaybe $ testEquality (W4.knownNat @1) n
  let bv_dec = W4.decNat bv_w
  Refl <- simpMaybe $ testEquality bv_dec idx
  let bv_min_i = BVS.asSigned bv_w $ BVS.minSigned bv_w
  bv_min_sym <- IO.liftIO $ W4.intLit sym bv_min_i
  bv <- lift $ rec bv_
  ss@[_,_] <- asSimpleSumM bv
  tryAll (permutations ss) $ \ss' -> do
    [bv_base, (W4.asConcrete -> Just (W4C.ConcreteBV _ bv_c))] <- return ss'
    let bv_c_i = BVS.asSigned bv_w bv_c
    guard $ bv_c_i < 0
    let le = GE True (CompatibleBVToInt2 bv_w)
    bv_c_i_sym <- IO.liftIO $ W4.intLit sym (-bv_c_i)
    bounded <- IO.liftIO $ mvBVOpFn sym le bv_base bv_c_i_sym
    let sub = BVSub True (CompatibleBVToInt2 bv_w)
    new_sum <- IO.liftIO $ mvBVOpFn sym sub bv_base bv_c_i_sym
    let lt = COrd LT True CompatibleInts
    overflowed <- IO.liftIO $ mvBVOpFn sym lt new_sum bv_min_sym
    IO.liftIO $ W4.orPred sym bounded overflowed
  <|> do
  simpLog $ "check app: " ++ show app'
  W4B.BaseEq _ bv_sum1_ (W4B.asApp -> Just (W4B.BVSext sext_w bv_sum2)) <- return app'

  simpLog $ "as_eq: " ++ show bv_sum1_ ++ " AND " ++ show bv_sum2
  W4.BaseBVRepr bv_sum2_w <- return $ W4.exprType bv_sum2
  Refl <- simpMaybe $ testEquality (W4.knownNat @65) sext_w

  bv_sum2_sext <- transformSum bv_sum2 sext_w (\bv_ -> IO.liftIO $ W4.bvSext sym sext_w bv_)
  sums_eq <- IO.liftIO $ W4.isEq sym bv_sum1_ bv_sum2_sext
  simpLog $ "sums_eq: " ++ show sums_eq
  Just True <- return $ W4.asConstantPred sums_eq
  bv_sum1 <- lift $ rec bv_sum1_

  let bv_min_i = BVS.asSigned bv_sum2_w $ BVS.minSigned bv_sum2_w
  let bv_max_i = BVS.asSigned bv_sum2_w $ BVS.maxSigned bv_sum2_w

  ss@[_,_] <- asSimpleSumM bv_sum1
  simpLog $ "simple sum:" ++ show ss
  tryAll (permutations ss) $ \ss' -> do
    [(W4B.asApp -> Just (W4B.BVSext _ bv_s1)), (W4.asConcrete -> Just (W4C.ConcreteBV _ bv_c))] <- return ss'
    let bv_c_i = BVS.asSigned sext_w bv_c
    
    bv_min_sym <- IO.liftIO $ W4.intLit sym bv_min_i
    bv_max_sym <- IO.liftIO $ W4.intLit sym bv_max_i
    e <- case bv_c_i < 0 of
      True -> do
        let sub = BVSub True (CompatibleBVToInt2 (W4.bvWidth bv_s1))
        bv_c_i_sym <- IO.liftIO $ W4.intLit sym (-bv_c_i)
        IO.liftIO $ mvBVOpFn sym sub bv_s1 bv_c_i_sym
      False -> do
        let add = BVAdd True (CompatibleBVToInt2 (W4.bvWidth bv_s1))
        bv_c_i_sym <- IO.liftIO $ W4.intLit sym bv_c_i
        IO.liftIO $ mvBVOpFn sym add bv_s1 bv_c_i_sym
    
    let le = LE True CompatibleInts
    let ge = GE True CompatibleInts
    upper_bound <- IO.liftIO $ mvBVOpFn sym le e bv_max_sym
    lower_bound <- IO.liftIO $ mvBVOpFn sym ge e bv_min_sym
    p <- IO.liftIO $ W4.andPred sym upper_bound lower_bound
    return p

bvPrettySimplify ::
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) => 
  SimpStrategy sym m
bvPrettySimplify = liftSimpTStrategy bvPrettySimplifyApp

isUInt :: W4.IsExpr (W4.SymExpr sym) => Integer -> W4.SymExpr sym tp -> Bool
isUInt i e = case W4.asConcrete e of
  Just (W4C.ConcreteBV _w bv_c) | BVS.asUnsigned bv_c == i -> True 
  Just (W4C.ConcreteInteger int_c) | int_c == i -> True 
  _ -> False

transformSum :: IO.MonadIO m =>
  1 <= w' =>
  (W4.SymBV sym w) ->
  W4.NatRepr w' ->
  (W4.SymBV sym w -> SimpT sym m (W4.SymBV sym w')) ->
  SimpT sym m (W4.SymBV sym w')
transformSum bv w' f = withSym $ \sym -> do
  W4B.SemiRingSum s <- asApp bv
  SR.SemiRingBVRepr baserepr w <- return $ WSum.sumRepr s
  let repr = SR.SemiRingBVRepr baserepr w'
  let f_lit c = do
        c' <- IO.liftIO $ W4.bvLit sym w c
        Just (W4C.ConcreteBV _ c'') <- W4.asConcrete <$> f c'
        return c''
  s' <- WSum.transformSum repr f_lit f s
  IO.liftIO $ WSum.evalM (W4.bvAdd sym) (\c x -> W4.bvMul sym x =<< W4.bvLit sym w' c) (W4.bvLit sym w') s'

asSimpleSum :: 
  forall sym sr w.
  sym ->
  W4.NatRepr w ->
  WSum.WeightedSum (W4.SymExpr sym) (SR.SemiRingBV sr w) -> 
  Maybe ([W4.SymBV sym w], BVS.BV w)
asSimpleSum _ _ ws = do
  terms <- WSum.evalM 
    (\x y -> return $ x ++ y)
    (\c e -> case c == one of {True -> return [e]; False -> fail ""})
    (\c -> case c == zero of { True -> return []; False -> fail ""})
    (ws & WSum.sumOffset .~ zero)
  return $ (terms, ws ^. WSum.sumOffset )
  where
    one :: BVS.BV w
    one = SR.one (WSum.sumRepr ws)

    zero :: BVS.BV w
    zero = SR.zero (WSum.sumRepr ws)

asSimpleSumM :: IO.MonadIO m => W4.SymBV sym w -> SimpT sym m [W4.SymBV sym w]
asSimpleSumM bv = withSym $ \sym -> do
  W4B.SemiRingSum s <- asApp bv
  W4.BaseBVRepr w <- return $ W4.exprType bv
  SR.SemiRingBVRepr SR.BVArithRepr _ <- return $ WSum.sumRepr s
  (bvs, c) <- simpMaybe $ asSimpleSum sym w s
  const_expr <- IO.liftIO $ W4.bvLit sym w c
  return $ const_expr:bvs


-- ======================================
-- Wrappers around bitvector operations to help with pretty-printing.
-- Specifically they hide type conversions and add explicit representations
-- for comparisons/operations that are otherwise simplified into a normal
-- form by the What4 expression builder.
-- ======================================

data CompatibleTypes tp1 tp2 tp3 where
  CompatibleInts :: CompatibleTypes W4.BaseIntegerType W4.BaseIntegerType W4.BaseIntegerType
  CompatibleBVs :: 1 <= w => W4.NatRepr w -> CompatibleTypes (W4.BaseBVType w) (W4.BaseBVType w) (W4.BaseBVType w)
  CompatibleBVsExt1 :: (1 <= w1, w1+1 <= w2, 1 <= w2) => W4.NatRepr w1 -> W4.NatRepr w2 -> CompatibleTypes (W4.BaseBVType w1) (W4.BaseBVType w2) (W4.BaseBVType w2)
  CompatibleBVsExt2 :: (1 <= w2, w2+1 <= w1, 1 <= w1) => W4.NatRepr w1 -> W4.NatRepr w2 -> CompatibleTypes (W4.BaseBVType w1) (W4.BaseBVType w2) (W4.BaseBVType w1)
  CompatibleBVToInt1 :: 1 <= w => W4.NatRepr w -> CompatibleTypes W4.BaseIntegerType (W4.BaseBVType w) W4.BaseIntegerType
  CompatibleBVToInt2 :: 1 <= w => W4.NatRepr w -> CompatibleTypes (W4.BaseBVType w) W4.BaseIntegerType W4.BaseIntegerType

compatibleTypeRepr :: CompatibleTypes tp1 tp2 tp3 -> W4.BaseTypeRepr tp3
compatibleTypeRepr = \case
  CompatibleInts -> W4.BaseIntegerRepr
  CompatibleBVs w -> W4.BaseBVRepr w
  CompatibleBVsExt1 _ w2 -> W4.BaseBVRepr w2
  CompatibleBVsExt2 w1 _ -> W4.BaseBVRepr w1
  CompatibleBVToInt1{} -> W4.BaseIntegerRepr
  CompatibleBVToInt2{} -> W4.BaseIntegerRepr

instance Show (CompatibleTypes tp1 tp2 tp3) where
  show ct = case ct of
    CompatibleInts -> go showInt showInt
    CompatibleBVs w -> go (showBV w) (showBV w)
    CompatibleBVsExt1 w1 w2 -> go (showBV w1) (showBV w2)
    CompatibleBVsExt2 w1 w2 -> go (showBV w1) (showBV w2)
    CompatibleBVToInt1 w -> go showInt (showBV w)
    CompatibleBVToInt2 w -> go (showBV w) showInt
    where
      showInt = showTp W4.BaseIntegerRepr
      showBV w = showTp (W4.BaseBVRepr w)

      showTp :: forall tp'. W4.BaseTypeRepr tp' -> String
      showTp = \case
        W4.BaseIntegerRepr -> "int"
        W4.BaseBVRepr w -> "bv" ++ show (W4.natValue w)
        tp -> show tp
      
      parens :: String -> String -> String
      parens s1 s2 = "(" ++ s1 ++ "," ++ s2 ++ ")"

      go :: String -> String -> String
      go s1 s2 = parens s1 s2 ++ "→" ++ showTp (compatibleTypeRepr ct)

compatibleTypes ::
  W4.BaseTypeRepr t1 ->
  W4.BaseTypeRepr t2 ->
  Maybe (Some (CompatibleTypes t1 t2))
compatibleTypes t1 t2 = case (t1, t2) of
  (W4.BaseIntegerRepr, W4.BaseIntegerRepr) -> Just $ Some CompatibleInts
  (W4.BaseBVRepr w1, W4.BaseBVRepr w2) -> Just $ case W4.testNatCases w1 w2 of
    W4.NatCaseLT W4.LeqProof ->  Some $ CompatibleBVsExt1 w1 w2
    W4.NatCaseGT W4.LeqProof -> Some $ CompatibleBVsExt2 w1 w2
    W4.NatCaseEQ -> Some $ CompatibleBVs w1
  (W4.BaseIntegerRepr, W4.BaseBVRepr w) -> Just $ Some $ CompatibleBVToInt1 w
  (W4.BaseBVRepr w, W4.BaseIntegerRepr) -> Just $ Some $ CompatibleBVToInt2 w
  _ -> Nothing

-- Turn two incompatible operands into the same type using
-- conversion operations
mkOperands ::
  forall sym tp1 tp2 tp3.
  W4.IsExprBuilder sym =>
  sym ->
  Bool {- signed comparison -} ->
  CompatibleTypes tp1 tp2 tp3  {- proof that the types are compatible for comparison -} ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  IO (W4.SymExpr sym tp3, W4.SymExpr sym tp3)
mkOperands sym b ct e1 e2  = case ct of
  CompatibleBVsExt1 _ w2 | b -> do
    e1' <- W4.bvSext sym w2 e1
    return $ (e1', e2)
  CompatibleBVsExt1 _ w2 | False <- b -> do
    e1' <- W4.bvZext sym w2 e1
    return $ (e1', e2)
  CompatibleBVsExt2 w1 _ | b -> do
    e2' <- W4.bvSext sym w1 e2
    return $ (e1, e2')
  CompatibleBVsExt2 w1 _ | False <- b -> do
    e2' <- W4.bvZext sym w1 e2
    return $ (e1, e2')
  CompatibleBVToInt1{} -> case b of
    True -> do
      e2' <- W4.sbvToInteger sym e2
      return $ (e1, e2')
    False -> do
      e2' <- W4.bvToInteger sym e2
      return $ (e1, e2')
  CompatibleBVToInt2{} -> case b of
    True -> do
      e1' <- W4.sbvToInteger sym e1
      return $ (e1', e2)
    False -> do
      e1' <- W4.bvToInteger sym e1
      return $ (e1', e2)
  CompatibleInts -> return (e1,e2)
  CompatibleBVs{} -> return (e1,e2)

data BVOp tp1 tp2 tp3 where
  COrd :: forall tp1 tp2 tp3. Ordering -> Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 W4.BaseBoolType
  NEQ :: Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 W4.BaseBoolType
  LE :: Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 W4.BaseBoolType
  GE :: Bool -> CompatibleTypes tp1 tp2 tp3 ->  BVOp tp1 tp2 W4.BaseBoolType
  BVAdd :: Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 tp3
  BVSub :: Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 tp3
  BVMul :: Bool -> CompatibleTypes tp1 tp2 tp3 -> BVOp tp1 tp2 tp3


instance Show (BVOp tp1 tp2 tp3) where
  show bvop | Some ct <- getCompatibleTypes bvop = simpleShowBVOp bvop ++ show ct

parseBVOp ::
  String -> 
  W4.BaseTypeRepr tp1 -> 
  W4.BaseTypeRepr tp2 -> 
  W4.BaseTypeRepr tp3 ->
  Maybe (BVOp tp1 tp2 tp3)
parseBVOp nm tp1 tp2 tp3 = case compatibleTypes tp1 tp2 of
  Just (Some ct) ->
    case tp3 of
      W4.BaseBoolRepr -> case nm of
        "LTs" -> Just $ COrd LT True ct
        "GTs" -> Just $ COrd GT True ct
        "EQs" -> Just $ COrd EQ True ct
        "LTu" -> Just $ COrd LT False ct
        "GTu" -> Just $ COrd GT False ct
        "EQu" -> Just $ COrd EQ False ct
        "LEs" -> Just $ LE True ct
        "GEs" -> Just $ GE True ct
        "LEu" -> Just $ LE False ct
        "GEu" -> Just $ GE False ct
        "NEQu" -> Just $ NEQ False ct
        "NEQs" -> Just $ NEQ True ct
        _ -> Nothing
      W4.BaseBVRepr{} | Just Refl <- testEquality (compatibleTypeRepr ct) tp3 -> case nm of
        "ADDs" -> Just $ BVAdd True ct
        "ADDu" -> Just $ BVAdd False ct
        "MULs" -> Just $ BVMul True ct
        "MULu" -> Just $ BVMul False ct
        "SUBs" -> Just $ BVSub True ct
        "SUBu" -> Just $ BVSub False ct
        _ -> Nothing
      _ -> Nothing
  _ -> Nothing

isSignedOp :: BVOp tp1 tp2 tp3 -> Bool
isSignedOp = \case
  COrd LT b _ -> b
  COrd GT b _ -> b
  COrd EQ b _ -> b
  NEQ b _ -> b
  LE b _ -> b
  GE b _ -> b
  BVAdd b _ -> b
  BVSub b _ -> b
  BVMul b _ -> b

simpleShowBVOp :: BVOp tp1 tp2 tp3 -> String
simpleShowBVOp bvop = case bvop of
  COrd LT _ _ -> "LT" ++ suf
  COrd EQ _ _ -> "EQ" ++ suf
  COrd GT _ _ -> "GT" ++ suf
  NEQ _ _ -> "NEQ" ++ suf
  LE _ _ -> "LE" ++ suf
  GE _ _ -> "GE" ++ suf
  BVAdd _ _ -> "ADD" ++ suf
  BVSub _ _ -> "SUB" ++ suf
  BVMul _ _ -> "MUL" ++ suf
  where
    suf :: String
    suf = case (isSignedOp bvop) of
      True -> "s"
      False -> "u"

getCompatibleTypes :: BVOp tp1 tp2 tp3 -> Some (CompatibleTypes tp1 tp2)
getCompatibleTypes = \case
  COrd _ _ ct -> Some ct
  NEQ _ ct -> Some ct
  LE _ ct -> Some ct
  GE _ ct -> Some ct
  BVAdd _ ct -> Some ct
  BVSub _ ct -> Some ct
  BVMul _ ct -> Some ct

notBVOp :: BVOp tp1 tp2 W4.BaseBoolType -> BVOp tp1 tp2 W4.BaseBoolType
notBVOp = \case
  COrd LT b ct -> GE b ct
  COrd GT b ct -> LE b ct
  COrd EQ b ct -> NEQ b ct
  NEQ b ct -> COrd EQ b ct
  LE b ct -> COrd GT b ct
  GE b ct -> COrd LT b ct
  -- arithmetic ops can't occur with bool result type
  BVAdd _ ct -> case ct of
  BVSub _ ct -> case ct of
  BVMul _ ct -> case ct of

appBVOp ::
  W4.IsExprBuilder sym =>
  sym ->
  BVOp tp1 tp2 tp3 ->
  CompatibleTypes tp1 tp2 tpOp ->
  (sym -> W4.SymExpr sym tpOp -> W4.SymExpr sym tpOp -> IO (W4.SymExpr sym tp3)) ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  IO (W4.SymExpr sym tp3)
appBVOp sym bvop ct f e1 e2 = do
  (e1', e2') <- mkOperands sym (isSignedOp bvop) ct e1 e2
  f sym e1' e2'

mkBVOp ::
  forall sym tp1 tp2 tp3.
  W4.IsExprBuilder sym =>
  sym ->
  BVOp tp1 tp2 tp3 ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  IO (W4.SymExpr sym tp3)
mkBVOp sym bvop e1 e2  = do
  case bvop of
    COrd EQ _ ct -> appBVOp sym bvop ct W4.isEq e1 e2
    NEQ _ ct -> appBVOp sym bvop ct (\sym' e1' e2' -> W4.isEq sym' e1' e2' >>= W4.notPred sym') e1 e2
    BVAdd _ ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} -> appBVOp sym bvop ct W4.bvAdd e1 e2
      W4.BaseIntegerRepr{} -> appBVOp sym bvop ct W4.intAdd e1 e2
      _ -> case ct of

    BVSub _ ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} -> appBVOp sym bvop ct W4.bvSub e1 e2
      W4.BaseIntegerRepr{} -> appBVOp sym bvop ct W4.intSub e1 e2
      _ -> case ct of

    BVMul _ ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} -> appBVOp sym bvop ct W4.bvMul e1 e2
      W4.BaseIntegerRepr{} -> appBVOp sym bvop ct W4.intMul e1 e2
      _ -> case ct of
    
    COrd ord s ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} -> case (ord, s) of
        (LT, True) -> appBVOp sym bvop ct W4.bvSlt e1 e2
        (LT, False) -> appBVOp sym bvop ct W4.bvUlt e1 e2
        (GT, True) -> appBVOp sym bvop ct W4.bvSgt e1 e2
        (GT, False) -> appBVOp sym bvop ct W4.bvUgt e1 e2
      W4.BaseIntegerRepr{} -> case ord of
        LT -> appBVOp sym bvop ct W4.intLt e1 e2
        GT -> appBVOp sym bvop ct (\sym' e1' e2' -> W4.intLt sym' e2' e1') e1 e2
      _ -> case ct of

    GE s ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} | s -> appBVOp sym bvop ct W4.bvSge e1 e2
      W4.BaseBVRepr{} | False <- s -> appBVOp sym bvop ct W4.bvUge e1 e2
      W4.BaseIntegerRepr{} -> appBVOp sym bvop ct (\sym' e1' e2' -> W4.intLe sym' e2' e1') e1 e2
      _ -> case ct of

    LE s ct -> case compatibleTypeRepr ct of
      W4.BaseBVRepr{} | s -> appBVOp sym bvop ct W4.bvSle e1 e2
      W4.BaseBVRepr{} | False <- s -> appBVOp sym bvop ct W4.bvUle e1 e2
      W4.BaseIntegerRepr{} -> appBVOp sym bvop ct W4.intLe e1 e2
      _ -> case ct of

-- | Wrap an operation in an applied defined function.
wrapFn ::
  forall sym args tp.
  W4.IsSymExprBuilder sym =>
  Ctx.CurryAssignmentClass args =>
  sym -> 
  String ->
  Ctx.Assignment (W4.SymExpr sym) args ->
  (Ctx.CurryAssignment args (W4.SymExpr sym) (IO (W4.SymExpr sym tp))) ->
  IO (W4.SymExpr sym tp)
wrapFn sym nm args f = do
  let tps = TFC.fmapFC W4.exprType args
  fn <- W4.inlineDefineFun sym (W4.safeSymbol nm) tps W4.NeverUnfold f
  W4.applySymFn sym fn args

mvBVOpFn :: 
  forall sym tp1 tp2 tp3.
  W4.IsSymExprBuilder sym =>
  sym ->
  BVOp tp1 tp2 tp3 ->
  W4.SymExpr sym tp1 ->
  W4.SymExpr sym tp2 ->
  IO (W4.SymExpr sym tp3)
mvBVOpFn sym bvop e1 e2 = do
  wrapFn sym (simpleShowBVOp bvop) (Ctx.empty Ctx.:> e1 Ctx.:> e2) (mkBVOp sym bvop)

data SomeAppBVOp sym tp where
  SomeAppBVOp :: forall sym tp1 tp2 tp3. BVOp tp1 tp2 tp3 -> W4.SymExpr sym tp1 -> W4.SymExpr sym tp2 -> SomeAppBVOp sym tp3

asSomeAppBVOp ::
  Monad m =>
  W4.SymExpr sym tp -> 
  SimpT sym m (SomeAppBVOp sym tp)
asSomeAppBVOp e = withSym $ \_ -> do
  W4B.FnApp fn (Ctx.Empty Ctx.:> arg1 Ctx.:> arg2) <- simpMaybe $ W4B.asNonceApp e
  nm <- return $ show (W4B.symFnName fn)
  case parseBVOp nm (W4.exprType arg1) (W4.exprType arg2) (W4.exprType e) of
    Just bvop -> return $ (SomeAppBVOp bvop arg1 arg2)
    Nothing -> fail $ "Failed to parse " ++ show nm ++ ": " ++ show e 

toSimpleConj ::
  forall sym m t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->  
  BM.BoolMap (W4B.Expr t) ->
  m [W4.Pred sym]
toSimpleConj sym bm = case BM.viewBoolMap bm of
   BM.BoolMapTerms (t1:|ts) -> mapM go (t1:ts)
   BM.BoolMapUnit -> return [W4.truePred sym]
   BM.BoolMapDualUnit -> return [W4.falsePred sym]
  where
    go :: (W4.Pred sym, BM.Polarity) -> m (W4.Pred sym)
    go (p, BM.Positive) = return p
    go (p, BM.Negative) = IO.liftIO $ W4.notPred sym p

collapseAppBVOps ::
  forall sym m tp.
  IO.MonadIO m =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  W4B.App (W4.SymExpr sym) tp -> 
  SimpT sym m (W4.SymExpr sym tp)
collapseAppBVOps rec app = case app of
  W4B.NotPred e -> go e
  W4B.ConjPred bm -> withSym $ \sym -> do
    ps <- toSimpleConj sym bm
    (p:ps') <- lift $ mapM rec ps 
    IO.liftIO $ foldM (W4.andPred sym) p ps'
  _ -> withSym $ \_ -> fail $ "not negated predicate" ++ show app
  where
    go :: W4.Pred sym -> SimpT sym m (W4.Pred sym)
    go e = withSym $ \sym -> do
      e' <- lift $ rec e
      SomeAppBVOp bvop e1 e2 <- asSomeAppBVOp e'
      let bvop' = notBVOp bvop
      IO.liftIO $ mvBVOpFn sym bvop' e1 e2

collapseBVOps ::
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) => 
  SimpStrategy sym m
collapseBVOps = liftSimpTStrategy collapseAppBVOps



