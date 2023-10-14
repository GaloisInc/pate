{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Block (
  -- * Block data
    BlockEntryKind(..)
  , ConcreteBlock(..)
  , FunCallKind(..)
  , BlockTarget(..)
  , targetBinRepr
  , targetEndCase
  , targetReturn
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
  , ppBlockAddr
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
import           Data.Parameterized.Some
import qualified Data.Macaw.AbsDomain.AbsState as DMAA

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Pate.Address as PA
import qualified Pate.PatchPair as PPa
import qualified Pate.Binary as PB
import           Pate.TraceTree
import qualified Data.Aeson as JSON

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
  deriving (Eq, Ord, Show, Enum, Bounded)

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

instance JSON.ToJSON (ConcreteBlock arch bin) where
  toJSON cb = JSON.object [
      "address" JSON..= concreteAddress cb
    , "function" JSON..= blockFunctionEntry cb
    ]


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
  testEquality (ConcreteBlock addr1 _entry1 binrepr1 fe1) (ConcreteBlock addr2 _entry2 binrepr2 fe2) =
    case PC.testEquality binrepr1 binrepr2 of
      Just PC.Refl | addr1 == addr2 && fe1 == fe2 -> Just PC.Refl
      _ -> Nothing

instance Eq (ConcreteBlock arch bin) where
  blk1 == blk2 | Just PC.Refl <- PC.testEquality blk1 blk2 = True
  _ == _ = False

instance PC.OrdF (ConcreteBlock arch) where
  compareF (ConcreteBlock addr1 _entry1 binrepr1 fe1) (ConcreteBlock addr2 _entry2 binrepr2 fe2) =
    PC.lexCompareF binrepr1 binrepr2 $ PC.fromOrdering $
      compare addr1 addr2 <>
      compare fe1 fe2

instance Ord (ConcreteBlock arch bin) where
  compare blk1 blk2 = PC.toOrdering $ PC.compareF blk1 blk2

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (ConcreteBlock arch bin) where
  show blk = ppBlock blk

instance MM.MemWidth (MM.ArchAddrWidth arch) => PC.ShowF (ConcreteBlock arch) where
  showF blk = show blk

ppBlock :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> String
ppBlock b = show (concreteAddress b)

ppBlockAddr :: MM.MemWidth (MM.ArchAddrWidth arch) => ConcreteBlock arch bin -> PP.Doc a
ppBlockAddr b = PP.viaShow (concreteAddress b)

instance (MM.MemWidth (MM.ArchAddrWidth arch)) => PP.Pretty (ConcreteBlock arch bin) where
  pretty cb =
    PP.hsep $ [      
      case functionSymbol (blockFunctionEntry cb) of
        Just s -> PP.viaShow s <+> "(" <> PP.viaShow (concreteAddress cb) <> ")"
        Nothing -> PP.viaShow (concreteAddress cb)
      ]

data BlockTarget arch bin =
  BlockTarget
    { targetCall :: ConcreteBlock arch bin
    , _targetReturn :: Maybe (ConcreteBlock arch bin)
    -- | The expected block exit case when this target is taken
    , _targetEndCase :: MCS.MacawBlockEndCase
    , targetRawPC :: PA.ConcreteAddress arch
    -- ^ raw PC value used for matching block exits
    }
  | BlockTargetReturn { _targetBinRepr :: PB.WhichBinaryRepr bin }
   deriving (Eq, Ord)

instance JSON.ToJSON (BlockTarget arch bin) where
  toJSON bt@BlockTarget{} = JSON.object
    [ "target" JSON..= targetCall bt
    , "return" JSON..= targetReturn bt
    , "endcase" JSON..= targetEndCase bt
    , "pc" JSON..= targetRawPC bt
    ]
  toJSON BlockTargetReturn{} = JSON.String "return_target"

targetReturn :: BlockTarget arch bin -> Maybe (ConcreteBlock arch bin)
targetReturn BlockTargetReturn{} = Nothing
targetReturn tgt@BlockTarget{} = _targetReturn tgt

targetBinRepr :: BlockTarget arch bin -> PB.WhichBinaryRepr bin
targetBinRepr tgt@BlockTargetReturn{} = _targetBinRepr tgt
targetBinRepr tgt@BlockTarget{} = blockBinRepr $ targetCall tgt

targetEndCase :: BlockTarget arch bin -> MCS.MacawBlockEndCase
targetEndCase tgt@BlockTarget{} = _targetEndCase tgt
targetEndCase BlockTargetReturn{} = MCS.MacawBlockEndReturn

instance PC.TestEquality (BlockTarget arch) where
  testEquality e1 e2 = PC.orderingF_refl (PC.compareF e1 e2)

instance PC.OrdF (BlockTarget arch) where
  compareF e1 e2 = case PC.compareF (targetBinRepr e1) (targetBinRepr e2) of
    PC.EQF -> PC.fromOrdering (compare e1 e2)
    x -> x

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch bin) where
  show (BlockTarget a b _ _) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"
  show (BlockTargetReturn{}) = "BlockTargetReturn"

instance MM.MemWidth (MM.ArchAddrWidth arch) => PP.Pretty (BlockTarget arch bin) where
  pretty blkt = PP.pretty (show blkt)

ppBlockTarget ::
  MM.MemWidth (MM.ArchAddrWidth arch) =>
  BlockTarget arch bin ->
  PP.Doc a
ppBlockTarget (BlockTargetReturn{}) = "Return"
ppBlockTarget (BlockTarget tgt ret c _) = case c of
  MCS.MacawBlockEndJump -> "Jump to:" <+> PP.pretty tgt
  MCS.MacawBlockEndBranch -> "Branch to:" <+> PP.pretty tgt
  MCS.MacawBlockEndCall -> case ret of
    Just r -> "Call to:" <+> PP.pretty tgt <+> "Returns to:" <+> PP.pretty r
    Nothing -> "Tail call to " <+> PP.pretty tgt
  MCS.MacawBlockEndReturn -> "Return"
  MCS.MacawBlockEndFail -> "Analysis Failure"
  MCS.MacawBlockEndArch -> case ret of
    Just r -> "Arch-specific exit to:" <+> PP.pretty tgt <+> PP.pretty r
    Nothing ->  "Arch-specific exit to:" <+> PP.pretty tgt <+> "without return"

instance forall sym arch. MM.MemWidth (MM.ArchAddrWidth arch) => IsTraceNode '(sym,arch) "blocktarget" where
  type TraceNodeType '(sym,arch) "blocktarget" = PPa.PatchPair (BlockTarget arch)
  prettyNode () blkts = PPa.ppPatchPair' ppBlockTarget blkts
  nodeTags = mkTags @'(sym,arch) @"blocktarget" [Simplified,Summary, JSONTrace]
  jsonNode = nodeToJSON @'(sym,arch) @"blocktarget"

instance forall sym arch. MM.MemWidth (MM.ArchAddrWidth arch) => IsTraceNode '(sym,arch) "blocktarget1" where
  type TraceNodeType '(sym,arch) "blocktarget1" = Some (BlockTarget arch)
  prettyNode () (Some blkt) = ppBlockTarget blkt
  nodeTags = mkTags @'(sym,arch) @"blocktarget1" [Simplified,Summary, JSONTrace]


data FunctionEntry arch (bin :: PB.WhichBinary) =
  FunctionEntry { functionSegAddr :: MM.ArchSegmentOff arch
                , functionSymbol  :: Maybe BSC.ByteString
                , functionBinRepr :: PB.WhichBinaryRepr bin
                , functionIgnored :: Bool
                -- ^ does our toplevel configuration tell us to ignore this function?
                , functionEnd :: Maybe (MM.ArchSegmentOff arch)
                -- ^ we might know the bounds of this function
                }

instance forall arch bin. JSON.ToJSON (FunctionEntry arch bin) where
  toJSON cb = JSON.object 
    [ "address" JSON..= functionSegAddr cb
    , "symbol" JSON..= functionSymbol cb
    ]

data FunCallKind = NormalFunCall | TailFunCall
  deriving (Eq, Ord, Show)

instance forall sym arch. MM.MemWidth (MM.ArchAddrWidth arch) => IsTraceNode '(sym,arch) "funcall" where
  type TraceNodeType '(sym,arch) "funcall" = PPa.PatchPair (FunctionEntry arch)
  type TraceNodeLabel "funcall" = FunCallKind
  prettyNode k funs = case k of
    NormalFunCall -> PP.pretty funs
    TailFunCall -> "Tail Call:" PP.<+> PP.pretty funs
  nodeTags = mkTags @'(sym,arch) @"funcall" [Summary, Simplified]

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
  testEquality (FunctionEntry segAddr1 _s1 binrepr1 _ign1 segEnd1) (FunctionEntry segAddr2 _s2 binrepr2 _ign2 segEnd2) =
    case PC.testEquality binrepr1 binrepr2 of
      Just PC.Refl | segAddr1 == segAddr2, segEnd1 == segEnd2 -> Just PC.Refl
      _ -> Nothing

instance Eq (FunctionEntry arch bin) where
  fe1 == fe2 = PC.isJust $ PC.testEquality fe1 fe2

instance PC.OrdF (FunctionEntry arch) where
  compareF (FunctionEntry segAddr1 _s1 binrepr1 _ign1 segEnd1) (FunctionEntry segAddr2 _s2 binrepr2 _ign2 segEnd2) =
    PC.lexCompareF binrepr1 binrepr2 $ PC.fromOrdering $
      (compare segAddr1 segAddr2 <> compare segEnd1 segEnd2)


instance Ord (FunctionEntry arch bin) where
  compare fe1 fe2 = PC.toOrdering $ PC.compareF fe1 fe2

functionEntryToConcreteBlock :: FunctionEntry arch bin -> ConcreteBlock arch bin
functionEntryToConcreteBlock fe@(FunctionEntry segAddr _s binRepr _ign _segEnd) =
  ConcreteBlock
  { concreteAddress    = PA.segOffToAddr segAddr
  , concreteBlockEntry = BlockEntryInitFunction
  , blockBinRepr       = binRepr
  , blockFunctionEntry = fe
  }

type BlockPair arch = PPa.PatchPair (ConcreteBlock arch)

type FunPair arch = PPa.PatchPair (FunctionEntry arch)

-- | Returns 'True' if the equated function pair (specified by address) matches
-- the current call target.
--   For singleton 'BlockPair' values this always returns false, since there
--   it cannot match an equated function pair.
matchEquatedAddress
  :: BlockPair arch
  -- ^ Addresses of the call targets in the original and patched binaries (in
  -- the 'proveLocalPostcondition' loop)
  -> (PA.ConcreteAddress arch, PA.ConcreteAddress arch)
  -- ^ Equated function pair
  -> Bool
matchEquatedAddress (PPa.PatchPair blkO blkP) (origAddr, patchedAddr) =
  and [ origAddr == concreteAddress blkO
      , patchedAddr == concreteAddress blkP
      ]
matchEquatedAddress _ _ = False

-- FIXME: put this somewhere more sensible

type AbsStateOverride arch =  MapF.MapF (MM.ArchReg arch) (DMAA.AbsValue (MM.ArchAddrWidth arch))

-- Defining overrides for initial abstract values for blocks
-- FIXME: also concrete?
data MkInitialAbsState arch =
  MkInitialAbsState { mkInitAbs :: MM.Memory (MM.RegAddrWidth (MM.ArchReg arch)) -> MM.ArchSegmentOff arch -> AbsStateOverride arch }

defaultMkInitialAbsState :: MkInitialAbsState arch
defaultMkInitialAbsState = MkInitialAbsState (\_ _ -> MapF.empty)
