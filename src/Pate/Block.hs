{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
module Pate.Block (
    BlockEntryKind(..)
  , ConcreteBlock(..)
  , BlockTarget(..)
  , concreteEntryPoint
  , equivBlocks
  , blockMemAddr
  -- * Pretty Printers
  , ppBlockEntry
  , ppBlock
  ) where

import qualified Data.Macaw.CFG as MM
import qualified Data.Parameterized.Classes as PC
import qualified Prettyprinter as PP

import qualified Pate.Address as PA
import qualified Pate.Binary as PB

-- | The way this block is entered dictates the initial equivalence relation we can assume
data BlockEntryKind arch =
    BlockEntryInitFunction
    -- ^ block starts a new function
  | BlockEntryPostFunction
    -- ^ block is an intermediate point in a function, after a function call
  | BlockEntryPostArch
    -- ^ block is an intermediate point in a function, after an arch function call
  | BlockEntryJump
    -- ^ block was entered by an arbitrary jump
    -- problems
  deriving (Eq, Ord, Show)

ppBlockEntry :: BlockEntryKind arch -> String
ppBlockEntry be = case be of
  BlockEntryInitFunction -> "function entry point"
  BlockEntryPostFunction -> "intermediate function point"
  BlockEntryPostArch -> "intermediate function point (after syscall)"
  BlockEntryJump -> "unknown program point"

data ConcreteBlock arch (bin :: PB.WhichBinary) =
  ConcreteBlock { concreteAddress :: PA.ConcreteAddress arch
                , concreteBlockEntry :: BlockEntryKind arch
                , blockBinRepr :: PB.WhichBinaryRepr bin
                }

concreteEntryPoint ::
  MM.ArchSegmentOff arch ->
  PB.WhichBinaryRepr bin ->
  ConcreteBlock arch bin
concreteEntryPoint off repr =
  ConcreteBlock
  { concreteAddress    = PA.addressFromMemAddr (MM.segoffAddr off)
  , concreteBlockEntry = BlockEntryInitFunction
  , blockBinRepr       = repr
  }

equivBlocks :: ConcreteBlock arch PB.Original -> ConcreteBlock arch PB.Patched -> Bool
equivBlocks blkO blkP =
  concreteAddress blkO == concreteAddress blkP &&
  concreteBlockEntry blkO == concreteBlockEntry blkP

blockMemAddr :: ConcreteBlock arch bin -> MM.MemAddr (MM.ArchAddrWidth arch)
blockMemAddr (ConcreteBlock (PA.ConcreteAddress addr) _ _) = addr

instance PC.TestEquality (ConcreteBlock arch) where
  testEquality (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    case PC.testEquality binrepr1 binrepr2 of
      Just PC.Refl | addr1 == addr2 && entry1 == entry2 -> Just PC.Refl
      _ -> Nothing

instance Eq (ConcreteBlock arch bin) where
  blk1 == blk2 | Just PC.Refl <- PC.testEquality blk1 blk2 = True
  _ == _ = False

instance PC.OrdF (ConcreteBlock arch) where
  compareF (ConcreteBlock addr1 entry1 binrepr1) (ConcreteBlock addr2 entry2 binrepr2) =
    PC.lexCompareF binrepr1 binrepr2 $ PC.fromOrdering $
      compare addr1 addr2 <>
      compare entry1 entry2

instance Ord (ConcreteBlock arch bin) where
  compare blk1 blk2 = PC.toOrdering $ PC.compareF blk1 blk2

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (ConcreteBlock arch bin) where
  show blk = ppBlock blk

instance MM.MemWidth (MM.ArchAddrWidth arch) => PC.ShowF (ConcreteBlock arch) where
  showF blk = show blk

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> String
ppBlock b = show (concreteAddress b)

instance (MM.MemWidth (MM.ArchAddrWidth arch)) => PP.Pretty (ConcreteBlock arch bin) where
  pretty = PP.viaShow . concreteAddress


data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , targetReturn :: Maybe (ConcreteBlock arch bin)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

