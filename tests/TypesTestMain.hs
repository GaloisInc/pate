{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

module Main ( main ) where


import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH

import qualified QuantTest as QT

main :: IO ()
main = do
  let tests = TT.testGroup "TypesTests" $ [
          TT.testGroup "Data.Quant" $ 
            [ TTH.testCase "testAll" $ QT.testAll 
            , TTH.testCase "testSingle" $ QT.testSingle
            , TTH.testCase "testMap" $ QT.testMap
            , TTH.testCase "testOrdering" $ QT.testOrdering
            , TTH.testCase "testConversions" $ QT.testOrdering
            ]
        ]
  TT.defaultMain tests