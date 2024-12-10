{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module QuantTest 
  ( testSingle
  , testAll
  , testMap
  , testOrdering
  , testConversions ) where

import qualified Test.Tasty.HUnit as TTH

import           Data.Parameterized.Classes
import           Data.Parameterized.WithRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( MapF )

import qualified Data.Parameterized.TotalMapF as TMF
import qualified Data.Quant as Qu
import           Data.Quant ( Quant, QuantK, AllK, ExistsK, OneK )

data ColorK = RedK | BlueK

data ColorRepr (tp :: ColorK) where
  RedRepr :: ColorRepr RedK
  BlueRepr :: ColorRepr BlueK

instance KnownRepr ColorRepr RedK where
  knownRepr = RedRepr

instance KnownRepr ColorRepr BlueK where
  knownRepr = BlueRepr

instance Show (ColorRepr tp) where
  show c = case c of
    RedRepr -> "red"
    BlueRepr -> "blue"

instance ShowF ColorRepr

instance IsRepr ColorRepr

instance TestEquality ColorRepr where
  testEquality r1 r2 = case (r1, r2) of
    (RedRepr, RedRepr) -> Just Refl
    (BlueRepr, BlueRepr) -> Just Refl
    _ -> Nothing

instance Eq (ColorRepr tp) where
  _ == _ = True

instance Ord (ColorRepr tp) where
  compare _ _ = EQ

instance OrdF ColorRepr where
  compareF r1 r2 = case (r1, r2) of
    (RedRepr, RedRepr) -> EQF
    (BlueRepr, BlueRepr) -> EQF
    (RedRepr, BlueRepr) -> LTF
    (BlueRepr, RedRepr) -> GTF



instance TMF.HasTotalMapF ColorRepr where
  allValues = [Some RedRepr, Some BlueRepr]

instance Qu.HasReprK ColorK where
  type ReprOf = ColorRepr

data Bucket (tp :: ColorK) = Bucket { bucketSize :: Int }
  deriving (Eq, Ord, Show)

instance ShowF Bucket

instance Show (Qu.Quant Bucket tp) where
  show qb = case qb of
    Qu.Single c (Bucket sz) -> show c ++ " bucket: " ++ show sz
    Qu.All f -> 
      let
        Bucket redsz = f RedRepr
        Bucket bluesz = f BlueRepr
      in "red: " ++ show redsz ++ " and blue: " ++ show bluesz

instance ShowF (Qu.Quant Bucket)

data BucketContainer (tp :: QuantK ColorK) = BucketContainer { buckets :: [Quant Bucket tp]}
  deriving (Show, Eq)

instance ShowF BucketContainer

instance Qu.QuantCoercible BucketContainer where
  coerceQuant (BucketContainer bs) = BucketContainer (map Qu.coerceQuant bs)

instance Qu.QuantConvertible BucketContainer where
  convertQuant (BucketContainer bs) = BucketContainer <$> mapM Qu.convertQuant bs

assertEq:: (Show f, Eq f) => f -> f -> IO ()
assertEq f1 f2 = case f1 == f2 of
  True -> return ()
  False -> TTH.assertFailure $ "assertEq failure: " ++ show f1 ++ " vs. " ++ show f2

assertInEq:: (Show f, Eq f) => f -> f -> IO ()
assertInEq f1 f2 = case f1 == f2 of
  True -> TTH.assertFailure $ "assertInEq failure: " ++ show f1 ++ " vs. " ++ show f2 
  False -> return ()


assertEquality' :: (ShowF f, TestEquality f) => f tp1 -> f tp2 -> IO (tp1 :~: tp2)
assertEquality' f1 f2 = case testEquality f1 f2 of
  Just Refl -> return Refl
  Nothing -> TTH.assertFailure $ "assertEquality failure: " ++ showF f1 ++ " vs. " ++ showF f2

assertEquality :: (ShowF f, TestEquality f) => f tp1 -> f tp2 -> IO ()
assertEquality f1 f2 = assertEquality' f1 f2 >> return ()

qRed0 :: Qu.Quant Bucket (OneK RedK)
qRed0 = Qu.QuantOne RedRepr (Bucket 0) 

qAll0 :: Qu.Quant Bucket AllK
qAll0 = Qu.QuantAll (TMF.mapWithKey (\c _ -> case c of RedRepr -> Bucket 0; BlueRepr -> Bucket 1) TMF.totalMapRepr)

testSingle :: IO ()
testSingle = do
  let (q2 :: Qu.Quant Bucket (OneK RedK)) = Qu.Single RedRepr (Bucket 0)
  assertEq qRed0 q2
  assertEquality qRed0 q2


testAll :: IO ()
testAll = do
  let (q2 :: Qu.Quant Bucket AllK) = Qu.All (\c -> case c of RedRepr -> Bucket 0; BlueRepr -> Bucket 1) 
  assertEq qAll0 q2
  assertEquality qAll0 q2

testMap :: IO ()
testMap = do
  assertEq (Qu.map (\(Bucket sz) -> Bucket (sz + 1)) qRed0) (Qu.QuantOne RedRepr (Bucket 1))
  assertInEq (Qu.map (\(Bucket sz) -> Bucket (sz + 1)) qRed0) (Qu.map (\(Bucket sz) -> Bucket (sz + 2)) qRed0)

  assertEq (Qu.map (\(Bucket sz) -> Bucket (sz + 1)) qAll0) (Qu.All (\c -> case c of RedRepr -> Bucket 1; BlueRepr -> Bucket 2))
  assertInEq (Qu.map (\(Bucket sz) -> Bucket (sz + 1)) qAll0) (Qu.map (\(Bucket sz) -> Bucket (sz + 2)) qAll0)


testOrdering :: IO ()
testOrdering = do
  let (bucketRed :: BucketContainer (OneK RedK)) = BucketContainer [qRed0]
  let (bucketAll :: BucketContainer AllK) = BucketContainer [qAll0]

  let (m :: MapF (Qu.Quant Bucket) BucketContainer) = MapF.fromList [MapF.Pair qRed0 bucketRed, MapF.Pair qAll0 bucketAll]
  assertEq (MapF.lookup qRed0 m) (Just bucketRed)
  assertEq (MapF.lookup qAll0 m) (Just bucketAll)

  return ()


testConversions :: IO ()
testConversions = do
  let (bucketRed :: BucketContainer (OneK RedK)) = BucketContainer [qRed0]
  let (bucketRedEx :: BucketContainer ExistsK) = Qu.coerceQuant bucketRed

  () <- case bucketRedEx of
    BucketContainer [] -> TTH.assertFailure "bucketRedEx: unexpected empty BucketContainer"
    BucketContainer (Qu.All _:_) -> TTH.assertFailure $ "bucketRedEx: Qu.All unexpected match"
    BucketContainer (Qu.Single repr x:_) -> do
      Refl <- assertEquality' repr RedRepr
      assertEq (Bucket 0) x
  
  let (mbucketRed :: Maybe (BucketContainer (OneK RedK))) = Qu.convertQuant bucketRedEx
  assertEq (Just bucketRed) mbucketRed

  let (mbucketBlue :: Maybe (BucketContainer (OneK BlueK))) = Qu.convertQuant bucketRedEx
  -- known invalid conversion
  assertEq Nothing mbucketBlue
  
  let (bucketAll :: BucketContainer AllK) = BucketContainer [qAll0]
  let (bucketAllEx :: BucketContainer ExistsK) = Qu.coerceQuant bucketAll

  case bucketAllEx of
    BucketContainer [] -> TTH.assertFailure "bucketAllEx: unexpected empty BucketContainer"
    BucketContainer (Qu.Single{}:_) -> TTH.assertFailure $ "bucketOneEx: Qu.Single unexpected match"
    BucketContainer (Qu.All f:_) -> assertEq qAll0 (Qu.All f)
  
  let bucketRedFromAll :: BucketContainer (OneK RedK) = Qu.coerceQuant bucketAll
  assertEq bucketRed bucketRedFromAll

  let (mbucketAll :: Maybe (BucketContainer AllK)) = Qu.convertQuant bucketAllEx
  assertEq (Just bucketAll) mbucketAll

  let (mbucketRedFromExistsAll :: Maybe (BucketContainer (OneK RedK))) = Qu.convertQuant bucketRedEx
  assertEq (Just bucketRed) mbucketRedFromExistsAll

  let (bucketMixed :: BucketContainer ExistsK) = BucketContainer [Qu.Single BlueRepr (Bucket 1), Qu.Single RedRepr (Bucket 0)]
  let (mixedToAll :: Maybe (BucketContainer AllK)) = Qu.convertQuant bucketMixed
  assertEq Nothing mixedToAll

  let (mixedToRed :: Maybe (BucketContainer (OneK RedK))) = Qu.convertQuant bucketMixed
  assertEq Nothing mixedToRed

  let (mixedToBlue :: Maybe (BucketContainer (OneK BlueK))) = Qu.convertQuant bucketMixed
  assertEq Nothing mixedToBlue

  let (bucketMixedRed :: BucketContainer ExistsK) = BucketContainer [Qu.QuantAny qAll0, Qu.QuantExists qRed0]

  let (mixedRedToRed :: Maybe (BucketContainer (OneK RedK))) = Qu.convertQuant bucketMixedRed
  assertEq (Just (BucketContainer [qRed0, qRed0])) mixedRedToRed

  let (mixedRedToBlue :: Maybe (BucketContainer (OneK BlueK))) = Qu.convertQuant bucketMixed
  assertEq Nothing mixedRedToBlue

  return ()

  
