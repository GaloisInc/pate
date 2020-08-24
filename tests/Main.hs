{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main ( main ) where

import           System.FilePath
import           System.FilePath.Glob (namesMatching)

import           Control.Monad.Except
import           Data.Word ( Word64 )
import           Data.Proxy
import           Data.Maybe
import qualified Data.Map as Map
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
--import qualified Test.Tasty.Options as T
--import qualified Test.Tasty.Runners as T
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import qualified Data.Macaw.Memory as MM

import qualified Pate.Binary as PB
import qualified Pate.Verification as V
import qualified Pate.PPC as PPC


main :: IO ()
main = do
  ppcTestFiles <- mapMaybe (stripExtension "info") <$> namesMatching "tests/ppc/*.info"
  T.defaultMain $ T.testGroup "Equivalence Tests" [ ppcTests ppcTestFiles ]

data ValidArchProxy arch where
  ValidArchProxy :: (V.ValidArch arch, PB.ArchConstraints arch) => ValidArchProxy arch

ppcTests :: [FilePath] -> T.TestTree
ppcTests files = T.testGroup "PPC" $ map (mkTest proxy) files
  where
    proxy = ValidArchProxy @PPC.PPC64

mkTest :: ValidArchProxy arch -> FilePath -> T.TestTree
mkTest proxy fp = T.testCase fp $ doTest proxy fp


doTest :: forall arch. ValidArchProxy arch -> FilePath -> IO ()
doTest proxy@ValidArchProxy fp = do
  rawPatchData <- readFile $ fp <.> "info"
  r <- case readMaybe rawPatchData of
    Nothing -> error $ "Bad patch info file"
    Just r -> return r
  original <- PB.loadELF @arch Proxy $ fp <.> "original" <.> "exe"
  patched <- PB.loadELF @arch Proxy $ fp <.> "patched" <.> "exe"
  testEquivVerification proxy r original patched

  

newtype Hex a = Hex a
  deriving (Eq, Ord, Num, PrintfArg)

instance (Num a, Show a, PrintfArg a) => Show (Hex a) where
  show (Hex a) = printf "0x%x" a

instance (Read a) => Read (Hex a) where
  readsPrec i s = [ (Hex a, s') | (a, s') <- readsPrec i s ]

type BlockData = (Hex Word64, Word64)

data PatchData =
  PatchData { patchPairs :: [(BlockData, BlockData)]
            , blockMapping :: [(Hex Word64, Hex Word64)]
            }
  deriving (Read, Show, Eq)

hexToAddr :: ValidArchProxy arch -> Hex Word64 -> V.ConcreteAddress arch
hexToAddr ValidArchProxy (Hex w) = V.ConcreteAddress $ MM.absoluteAddr $ MM.memWord w

unpackBlockData :: ValidArchProxy arch -> BlockData -> V.ConcreteBlock arch
unpackBlockData proxy (start, size) =
  V.ConcreteBlock
    { V.concreteBlockAddress = (hexToAddr proxy start)
    , V.concreteBlockSize = fromIntegral $ size
    }


unpackPatchData :: ValidArchProxy arch -> PatchData -> (V.BlockMapping arch, [V.PatchPair arch])
unpackPatchData proxy (PatchData pairs bmap) =
  let
    bmap' = V.BlockMapping $ 
      Map.fromList $ map (\(addr, addr') -> (hexToAddr proxy addr, hexToAddr proxy addr')) bmap
    ppairs = map (\(bd, bd') -> V.PatchPair (unpackBlockData proxy bd) (unpackBlockData proxy bd')) pairs
  in (bmap', ppairs)

testEquivVerification ::
  ValidArchProxy arch ->
  PatchData ->
  PB.LoadedELF arch ->
  PB.LoadedELF arch ->
  IO ()
testEquivVerification proxy@ValidArchProxy pd original patched = do
  let (bmap, ppairs) = unpackPatchData proxy pd
  v <- runExceptT (V.verifyPairs original patched bmap ppairs)
  case v of
    Left err -> T.assertFailure (show err)
    Right b -> T.assertBool "Verification did not succeed" b
