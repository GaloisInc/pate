{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Block (
  -- * Block data
    BlockEntryKind(..)
  , ConcreteBlock(..)
  , FunCallKind(..)
  , BlockTarget(..)
  , BlockPair
  , FunPair
  , equivBlocks
  , blockMemAddr
  , mkConcreteBlock
  , mkConcreteBlock'
  , asFunctionEntry

  -- * Function entry data
  , FunctionEntry(..)
  , functionAddress
  , functionEntryToConcreteBlock

  -- * Pretty Printers
  , ppBlockEntry
  , ppBlock
  , ppFunctionEntry
  , matchEquatedAddress
  , AbsStateOverride
  , MkInitialAbsState(..)
  , defaultMkInitialAbsState
  ) where

import qualified Data.ByteString.Char8 as BSC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Macaw.AbsDomain.AbsState as DMAA

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.Address as PA
import qualified Pate.PatchPair as PPa
import qualified Pate.Binary as PB
import           Pate.TraceTree

-- | The way this block is entered dictates the initial equivalence relation we can assume
data BlockEntryKind arch =
    BlockEntryInitFunction
    -- ^ block starts a new function
  | BlockEntryPostFunction
    -- ^ block is an intermediate point in a function, after a function call
  | BlockEntryPostArch
    -- ^ block is an intermediate point in a function, after an arch function call
  | BlockEntryPreArch
    -- ^ block is an intermediate point in a function, about to make an arch function call
  | BlockEntryJump
    -- ^ block was entered by an arbitrary jump
    -- problems
  deriving (Eq, Ord, Show)

ppBlockEntry :: BlockEntryKind arch -> String
ppBlockEntry be = case be of
  BlockEntryInitFunction -> "function entry point"
  BlockEntryPostFunction -> "intermediate function point"
  BlockEntryPreArch -> "intermediate function point (before syscall)"
  BlockEntryPostArch -> "intermediate function point (after syscall)"
  BlockEntryJump -> "unknown program point"

data ConcreteBlock arch (bin :: PB.WhichBinary) =
  ConcreteBlock { concreteAddress :: PA.ConcreteAddress arch
                , concreteBlockEntry :: BlockEntryKind arch
                , blockBinRepr :: PB.WhichBinaryRepr bin
                , blockFunctionEntry :: FunctionEntry arch bin
                }

equivBlocks :: ConcreteBlock arch PB.Original -> ConcreteBlock arch PB.Patched -> Bool
equivBlocks blkO blkP =
  concreteAddress blkO == concreteAddress blkP &&
  concreteBlockEntry blkO == concreteBlockEntry blkP &&
  equivFuns (blockFunctionEntry blkO) (blockFunctionEntry blkP)

blockMemAddr :: ConcreteBlock arch bin -> MM.MemAddr (MM.ArchAddrWidth arch)
blockMemAddr b = PA.addrToMemAddr (concreteAddress b)

asFunctionEntry :: ConcreteBlock arch bin -> Maybe (FunctionEntry arch bin)
asFunctionEntry blk
  | concreteAddress blk == (functionAddress (blockFunctionEntry blk))
  = Just (blockFunctionEntry blk)

  | otherwise = Nothing

mkConcreteBlock ::
  ConcreteBlock arch bin ->
  BlockEntryKind arch ->
  MM.ArchSegmentOff arch ->
  ConcreteBlock arch bin
mkConcreteBlock from k a =
  ConcreteBlock
  { concreteAddress = PA.segOffToAddr a
  , concreteBlockEntry = k
  , blockBinRepr = blockBinRepr from
  , blockFunctionEntry = blockFunctionEntry from
  }

mkConcreteBlock' ::
  ConcreteBlock arch bin ->
  BlockEntryKind arch ->
  PA.ConcreteAddress arch ->
  ConcreteBlock arch bin
mkConcreteBlock' from k a =
  ConcreteBlock
  { concreteAddress = a
  , concreteBlockEntry = k
  , blockBinRepr = blockBinRepr from
  , blockFunctionEntry = blockFunctionEntry from
  }


instance PC.TestEquality (ConcreteBlock arch) where
  testEquality (ConcreteBlock addr1 entry1 binrepr1 fe1) (ConcreteBlock addr2 entry2 binrepr2 fe2) =
    case PC.testEquality binrepr1 binrepr2 of
      Just PC.Refl | addr1 == addr2 && entry1 == entry2 && fe1 == fe2 -> Just PC.Refl
      _ -> Nothing

instance Eq (ConcreteBlock arch bin) where
  blk1 == blk2 | Just PC.Refl <- PC.testEquality blk1 blk2 = True
  _ == _ = False

instance PC.OrdF (ConcreteBlock arch) where
  compareF (ConcreteBlock addr1 entry1 binrepr1 fe1) (ConcreteBlock addr2 entry2 binrepr2 fe2) =
    PC.lexCompareF binrepr1 binrepr2 $ PC.fromOrdering $
      compare addr1 addr2 <>
      compare entry1 entry2 <>
      compare fe1 fe2

instance Ord (ConcreteBlock arch bin) where
  compare blk1 blk2 = PC.toOrdering $ PC.compareF blk1 blk2

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (ConcreteBlock arch bin) where
  show blk = ppBlock blk

instance MM.MemWidth (MM.ArchAddrWidth arch) => PC.ShowF (ConcreteBlock arch) where
  showF blk = show blk

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> String
ppBlock b = show (concreteAddress b)

instance (MM.MemWidth (MM.ArchAddrWidth arch)) => PP.Pretty (ConcreteBlock arch bin) where
  pretty cb = case functionSymbol (blockFunctionEntry cb) of
    Just s -> PP.viaShow s <+> "(" <> PP.viaShow (concreteAddress cb) <> ")"
    Nothing -> PP.viaShow (concreteAddress cb)

data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    -- | The expected block exit case when this target is taken
    , targetEndCase :: MCS.MacawBlockEndCase
    } deriving (Eq, Ord)


instance PC.TestEquality (BlockTarget arch) where
  testEquality e1 e2 = PC.orderingF_refl (PC.compareF e1 e2)

instance PC.OrdF (BlockTarget arch) where
  compareF e1 e2 = case PC.compareF (blockBinRepr $ targetCall e1) (blockBinRepr $ targetCall e2) of
    PC.EQF -> PC.fromOrdering (compare e1 e2)
    x -> x

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b _) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

instance MM.MemWidth (MM.ArchAddrWidth arch) => PP.Pretty (BlockTarget arch bin) where
  pretty blkt = PP.pretty (show blkt)


instance MM.MemWidth (MM.ArchAddrWidth arch) => IsTraceNode '(sym,arch) "blocktarget" where
  type TraceNodeType '(sym,arch) "blocktarget" = PPa.PatchPair (BlockTarget arch)
  prettyNode () blkts = PP.pretty blkts

data FunctionEntry arch (bin :: PB.WhichBinary) =
  FunctionEntry { functionSegAddr :: MM.ArchSegmentOff arch
                , functionSymbol  :: Maybe BSC.ByteString
                , functionBinRepr :: PB.WhichBinaryRepr bin
                , functionIgnored :: Bool
                -- ^ does our toplevel configuration tell us to ignore this function?
                }

data FunCallKind = NormalFunCall | TailFunCall
  deriving (Eq, Ord, Show)

instance MM.MemWidth (MM.ArchAddrWidth arch) => IsTraceNode '(sym,arch) "funcall" where
  type TraceNodeType '(sym,arch) "funcall" = PPa.PatchPair (FunctionEntry arch)
  type TraceNodeLabel "funcall" = FunCallKind
  prettyNode k funs = case k of
    NormalFunCall -> PP.pretty funs
    TailFunCall -> "Tail Call:" PP.<+> PP.pretty funs

equivFuns :: FunctionEntry arch PB.Original -> FunctionEntry arch PB.Patched -> Bool
equivFuns fn1 fn2 =
  functionSegAddr fn1 == functionSegAddr fn2


functionAddress :: FunctionEntry arch bin -> PA.ConcreteAddress arch
functionAddress fe = PA.segOffToAddr (functionSegAddr fe)

ppFunctionEntry :: MM.MemWidth (MM.ArchAddrWidth arch) => FunctionEntry arch bin -> String
ppFunctionEntry fe = show (functionAddress fe)

instance (MM.MemWidth (MM.ArchAddrWidth arch)) => PP.Pretty (FunctionEntry arch bin) where
  pretty fe = case functionSymbol fe of
    Just s -> PP.viaShow s <+> "(" <> PP.viaShow (functionAddress fe) <> ")"
    Nothing -> PP.viaShow (functionAddress fe)

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (FunctionEntry arch bin) where
  show fe = ppFunctionEntry fe

instance MM.MemWidth (MM.ArchAddrWidth arch) => PC.ShowF (FunctionEntry arch) where
  showF fe = show fe

instance PC.TestEquality (FunctionEntry arch) where
  testEquality (FunctionEntry segAddr1 _s1 binrepr1 _ign1) (FunctionEntry segAddr2 _s2 binrepr2 _ign2) =
    case PC.testEquality binrepr1 binrepr2 of
      Just PC.Refl | segAddr1 == segAddr2 -> Just PC.Refl
      _ -> Nothing

instance Eq (FunctionEntry arch bin) where
  fe1 == fe2 = PC.isJust $ PC.testEquality fe1 fe2

instance PC.OrdF (FunctionEntry arch) where
  compareF (FunctionEntry segAddr1 _s1 binrepr1 _ign1) (FunctionEntry segAddr2 _s2 binrepr2 _ign2) =
    PC.lexCompareF binrepr1 binrepr2 $ PC.fromOrdering $
      compare segAddr1 segAddr2


instance Ord (FunctionEntry arch bin) where
  compare fe1 fe2 = PC.toOrdering $ PC.compareF fe1 fe2

functionEntryToConcreteBlock :: FunctionEntry arch bin -> ConcreteBlock arch bin
functionEntryToConcreteBlock fe@(FunctionEntry segAddr _s binRepr _ign) =
  ConcreteBlock
  { concreteAddress    = PA.segOffToAddr segAddr
  , concreteBlockEntry = BlockEntryInitFunction
  , blockBinRepr       = binRepr
  , blockFunctionEntry = fe
  }

type BlockPair arch = PPa.PatchPair (ConcreteBlock arch)

type FunPair arch = PPa.PatchPair (FunctionEntry arch)

-- | Returns 'True' if the equated function pair (specified by address) matches
-- the current call target
matchEquatedAddress
  :: BlockPair arch
  -- ^ Addresses of the call targets in the original and patched binaries (in
  -- the 'proveLocalPostcondition' loop)
  -> (PA.ConcreteAddress arch, PA.ConcreteAddress arch)
  -- ^ Equated function pair
  -> Bool
matchEquatedAddress pPair (origAddr, patchedAddr) =
  and [ origAddr == concreteAddress (PPa.pOriginal pPair)
      , patchedAddr == concreteAddress (PPa.pPatched pPair)
      ]


-- FIXME: put this somewhere more sensible

type AbsStateOverride arch =  MapF.MapF (MM.ArchReg arch) (DMAA.AbsValue (MM.ArchAddrWidth arch))

-- Defining overrides for initial abstract values for blocks
-- FIXME: also concrete?
data MkInitialAbsState arch =
  MkInitialAbsState { mkInitAbs :: MM.Memory (MM.RegAddrWidth (MM.ArchReg arch)) -> MM.ArchSegmentOff arch -> AbsStateOverride arch }

defaultMkInitialAbsState :: MkInitialAbsState arch
defaultMkInitialAbsState = MkInitialAbsState (\_ _ -> MapF.empty)
