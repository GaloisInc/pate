{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Functions for cutting out sub-graphs from macaw CFGs

module Data.Macaw.CFGSlice
  ( -- * Classifying the original block exit in a sliced CFG
    HasArchEndCase
  , HasArchTermEndCase(..)
  , MacawBlockEndCase(..)
  , MacawBlockEndType
  , MacawBlockEnd(..)
  , blockEndCaseEq
  , isBlockEndCase
  , blockEndCase
  , blockEndReturn
  , initBlockEnd
  , termStmtToBlockEnd
  , blockEndSliceFns
  ) where

import           Control.Monad

import           Data.Proxy
import qualified Data.BitVector.Sized as BV
import qualified Data.Kind as Kind

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map ( Pair(..) )

import           What4.Interface
import           What4.Partial

import           Lang.Crucible.Backend
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR

import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.LLVM.MemModel as MM

import qualified Lang.Crucible.Utils.MuxTree as C
import qualified Data.Macaw.Symbolic as MS

import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.Symbolic.Backend as MSB

-- * Retaining original macaw block endings when slicing CFG

-- | An enum corresponding to the kind of terminal statement that originally
-- appeared at the end of a block.
data MacawBlockEndCase =
    MacawBlockEndJump
  | MacawBlockEndCall
  | MacawBlockEndReturn
  | MacawBlockEndBranch
  | MacawBlockEndFail
  -- | An otherwise-unclassified arch exit. Some arch exits may end up being classified
  -- as either calls or returns, according to 'archTermCase'
  | MacawBlockEndArch
  deriving (Eq, Enum, Bounded, Ord)


class HasArchTermEndCase (f :: (M.Type -> Kind.Type) -> Kind.Type) where
  archTermCase :: f v -> MacawBlockEndCase

type HasArchEndCase arch = HasArchTermEndCase (M.ArchTermStmt arch)

-- | A summary of a 'M.ParsedTermStmt', representing how the block ended and
-- potentally the address to return to in the case of a function call.
data MacawBlockEnd arch = MacawBlockEnd MacawBlockEndCase !(Maybe (M.ArchSegmentOff arch))

-- | A crucible encoding of 'MacawBlockEnd', where the 'MacawBlockEndCase' as an 8-bit bitvector
-- and the return address is a 'MM.LLVMPointerType'.
type MacawBlockEndType arch = C.StructType (Ctx.EmptyCtx Ctx.::> C.BVType 8 Ctx.::> C.MaybeType (MM.LLVMPointerType (M.ArchAddrWidth arch)))

-- | Construct a crucible expression that is equivalent to a 'MacawBlockEnd'
-- TODO: it probably makes sense to instead define this as an intrinsic, rather
-- than relying on encoding/decoding
blockEndAtom :: forall arch ids s
              . MS.MacawSymbolicArchFunctions arch
             -> MacawBlockEnd arch
             -> MSB.CrucGen arch ids s (CR.Atom s (MacawBlockEndType arch))
blockEndAtom archFns (MacawBlockEnd blendK mret) = MSB.crucGenArchConstraints archFns $ do
    blendK' <- MSB.bvLit knownNat (toInteger $ fromEnum blendK)
    let
      memWidthNatRepr = M.memWidthNatRepr @(M.ArchAddrWidth arch)
      ptrRepr = MM.LLVMPointerRepr memWidthNatRepr
    mret' <- case mret of
      Just addr -> do
        ptr <- MSB.valueToCrucible $ M.RelocatableValue (M.addrWidthRepr (Proxy @(M.ArchAddrWidth arch))) (M.segoffAddr addr)
        MSB.appAtom $ C.JustValue ptrRepr ptr
      Nothing -> do
        MSB.appAtom $ C.NothingValue ptrRepr
    let repr = Ctx.empty Ctx.:> C.BVRepr knownNat Ctx.:> C.MaybeRepr ptrRepr
    MSB.appAtom $ C.MkStruct repr (Ctx.empty Ctx.:> blendK' Ctx.:> mret')

-- | Classify the given 'M.ParsedTermStmt' as a 'MacawBlockEnd' according
-- to 'termStmtToBlockEnd' and write it out to the given global variable.
-- After symbolic execution, this global then represents how the block
-- orignally "exited" before the CFG slicing.
assignBlockEnd :: HasArchEndCase arch =>
                  MSB.MacawSymbolicArchFunctions arch
               -> CR.GlobalVar (MacawBlockEndType arch)
               -> M.ParsedTermStmt arch ids
               -> MSB.CrucGen arch ids s ()
assignBlockEnd archFns blendVar stmt = MSB.crucGenArchConstraints archFns $ do
  let blend = termStmtToBlockEnd stmt
  blend' <- blockEndAtom archFns blend
  MSB.addStmt $ CR.WriteGlobal blendVar blend'

-- | Return a pair of expressions '(e, c)' where the 'e' represents
--   the symbolic backing for the given 'MacawBlockEndType' and 'c'
--   is the given concrete 'MacawBlockEndCase' injected into a symbolic value.
--   (i.e. the predicate 'e == c' is true iff the first argument matches the
--   given concrete exit case).
blockEndCaseEq :: forall sym arch proxy
                . IsSymInterface sym
               => proxy arch
               -> sym
               -> C.RegValue sym (MacawBlockEndType arch)
               -> MacawBlockEndCase
               -> IO (Pair (SymExpr sym) (SymExpr sym))
blockEndCaseEq _ sym (_ Ctx.:> C.RV blendC' Ctx.:> _) blendC = do
  blendC'' <- bvLit sym knownNat (BV.mkBV knownNat (toInteger $ fromEnum blendC))
  return $ Pair blendC' blendC''

isBlockEndCase :: forall sym arch proxy
                . IsSymInterface sym
               => proxy arch
               -> sym
               -> C.RegValue sym (MacawBlockEndType arch)
               -> MacawBlockEndCase
               -> IO (Pred sym)
isBlockEndCase arch sym blendC' blendC = do
  Pair e1 e2 <- blockEndCaseEq arch sym blendC' blendC
  isEq sym e1 e2

blockEndCase :: forall sym arch proxy
              . IsSymInterface sym
             => proxy arch
             -> sym
             -> C.RegValue sym (MacawBlockEndType arch)
             -> IO (C.MuxTree sym MacawBlockEndCase)
blockEndCase arch sym blend = do
  foldM addCase (C.toMuxTree sym MacawBlockEndFail) [minBound..maxBound]
  where
    addCase mt blendC = do
      p <- isBlockEndCase arch sym blend blendC
      C.mergeMuxTree sym p (C.toMuxTree sym blendC) mt

blockEndReturn :: forall sym arch proxy
                . proxy arch
               -> C.RegValue sym (MacawBlockEndType arch)
               -> (C.RegValue sym (C.MaybeType (MM.LLVMPointerType (M.ArchAddrWidth arch))))
blockEndReturn _ (_ Ctx.:> _ Ctx.:> C.RV mret) = mret

initBlockEnd :: forall sym arch proxy
              . IsSymInterface sym
             => proxy arch
             -> sym
             -> IO (C.RegValue sym (MacawBlockEndType arch))
initBlockEnd _ sym = do
  blendK <- bvLit sym (knownNat @8) (BV.mkBV (knownNat @8) (toInteger $ fromEnum MacawBlockEndReturn))
  return $ (Ctx.empty Ctx.:> C.RV blendK Ctx.:> C.RV Unassigned)

termStmtToBlockEnd :: forall arch ids. HasArchEndCase arch => M.ParsedTermStmt arch ids -> MacawBlockEnd arch
termStmtToBlockEnd tm0 =
  case tm0 of
    M.ParsedReturn {} -> MacawBlockEnd MacawBlockEndReturn Nothing
    M.ParsedCall _ ret -> MacawBlockEnd MacawBlockEndCall ret
    M.ParsedJump {} -> MacawBlockEnd MacawBlockEndJump Nothing
    M.ParsedBranch {} -> MacawBlockEnd MacawBlockEndBranch Nothing
    M.ParsedLookupTable {} -> MacawBlockEnd MacawBlockEndJump Nothing
    M.ParsedArchTermStmt stmt _ ret -> MacawBlockEnd (archTermCase stmt) ret
    M.ClassifyFailure {} -> MacawBlockEnd MacawBlockEndFail Nothing
    M.PLTStub {} -> MacawBlockEnd MacawBlockEndCall Nothing
    M.ParsedTranslateError{} -> MacawBlockEnd MacawBlockEndFail Nothing


blockEndSliceFns ::
  HasArchEndCase arch =>
  MSB.MacawSymbolicArchFunctions arch ->
  CR.GlobalVar (MacawBlockEndType arch) ->
  MS.MacawSlicingFunctions arch
blockEndSliceFns archFns bvar = MS.MacawSlicingFunctions (assignBlockEnd archFns bvar)
