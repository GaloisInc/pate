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
  ( -- * Translating slices of CFGs
    mkBlockSliceRegCFG
  , mkBlockSliceCFG
    -- * Classifying the original block exit in a sliced CFG
  , HasArchEndCase
  , HasArchTermEndCase(..)
  , MacawBlockEndCase(..)
  , MacawBlockEndType
  , MacawBlockEnd(..)
  , isBlockEndCase
  , blockEndCase
  , blockEndReturn
  , initBlockEnd
  , termStmtToBlockEnd
  ) where

import           Control.Monad

import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Maybe
import qualified Data.BitVector.Sized as BV
import qualified Data.Kind as Kind

import           Data.Parameterized.Context (EmptyCtx, (::>), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import           What4.Partial
import qualified What4.Utils.StringLiteral as C
import qualified What4.ProgramLoc as WPL

import           Lang.Crucible.Backend
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.FunctionHandle as C

import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.LLVM.MemModel as MM

import qualified Lang.Crucible.Utils.MuxTree as C
import qualified Data.Macaw.Symbolic as MS

import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.Symbolic.CrucGen as CG

-- | See the documentation for 'MS.mkBlockSliceCFG'
mkBlockSliceRegCFG :: forall arch ids
                    . HasArchEndCase arch
                   => MS.MacawSymbolicArchFunctions arch
                   -> C.HandleAllocator
                   -> (M.ArchSegmentOff arch -> WPL.Position)
                   -> M.ParsedBlock arch ids
                   -- ^ Entry block
                   -> [M.ParsedBlock arch ids]
                   -- ^ Non-entry non-terminal blocks
                   -> [M.ParsedBlock arch ids]
                   -- ^ Terminal blocks
                   -> [(M.ArchSegmentOff arch, M.ArchSegmentOff arch)]
                   -- ^ (Source, target) block address pairs to convert to returns
                   -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
                   -- ^ variable to optionally retain how the block originally exited
                   -> IO (CR.SomeCFG (CG.MacawExt arch) (EmptyCtx ::> CG.ArchRegStruct arch) (CG.ArchRegStruct arch))
mkBlockSliceRegCFG archFns halloc posFn entry body0 terms retEdges_ block_end_var = CG.crucGenArchConstraints archFns $ MS.mkCrucRegCFG archFns halloc "" $ do
  -- Build up some initial values needed to set up the entry point to the
  -- function (including the initial value of all registers)
  inputRegId <- CG.mmFreshNonce
  let inputReg = CR.Reg { CR.regPosition = entryPos
                        , CR.regId = inputRegId
                        , CR.typeOfReg = archRegTy
                        }
  ng <- CG.mmNonceGenerator
  inputAtom <- CG.mmExecST (Ctx.last <$> CR.mkInputAtoms ng entryPos (Empty :> archRegTy))

  -- Allocate Crucible CFG labels for all of the blocks provided by the caller
  labelMap0 <- MS.mkBlockLabelMap allBlocks

  -- Add synthetic blocks for all jump targets mentioned by the input blocks,
  -- but not included in the list of all blocks.  The synthetic blocks simply
  -- assume False to indicate to the symbolic execution engine that executions
  -- reaching those missing blocks are not feasible paths.
  (labelMap, syntheticBlocks) <- F.foldlM (makeSyntheticBlocks inputReg) (labelMap0, []) allBlocks

  -- Add synthetic block to act as a target for jumps that we want to be
  -- returns instead.
  (retLabel, retBlocks) <- makeReturnBlock inputReg
  let lookupRetEdges src = Map.fromSet
        (const retLabel)
        (Map.findWithDefault S.empty src retEdges)

  -- Set up a fake entry block that initializes the register file and jumps
  -- to the real entry point
  entryLabel <- CR.Label <$> CG.mmFreshNonce
  (initCrucBlock, initExtraCrucBlocks) <- CG.runCrucGen archFns (offPosFn entryAddr) entryLabel inputReg $ do
    CG.setMachineRegs inputAtom
    CG.addTermStmt $ CR.Jump (CG.parsedBlockLabel labelMap entryAddr)

  -- Add each block in the slice
  --
  -- For blocks marked as terminators, we rewrite their terminator statement
  -- into a return.
  crucBlocks <- forM allBlocks $ \block -> do
    let blockAddr = M.pblockAddr block
    let label = case Map.lookup blockAddr labelMap of
          Just lbl -> lbl
          Nothing -> error ("Missing block label for block at " ++ show blockAddr)

    -- Below, we are going to call addMacawParsedTermStmt to convert the final
    -- instruction in this macaw block into an edge in the CFG. Under normal
    -- circumstances, this happens by keeping a static map from addresses (that
    -- are the targets of jumps) to CFG nodes, and passing that map as ane of
    -- the arguments.
    --
    -- We are going to corrupt that mechanism slightly. We want to allow
    -- callers to break cycles in the CFG by converting some jumps into returns
    -- instead, and the API we've chosen for specifying which jumps is by
    -- identifying source block/target block pairs whose edges we should drop
    -- from the CFG to break the cycles. Right here is where we implement that
    -- breakage. The way we do it is by changing the map from targets to nodes
    -- differently depending on which source block we are currently
    -- interpreting.
    --
    -- So: lookupRetEdges builds an override Map which points some of the
    -- possible target blocks at a special CFG node that just returns
    -- immediately. Then labelMapWithReturns has the usual static map, but with
    -- those targets overridden appropriately.
    let labelMapWithReturns = Map.union (lookupRetEdges blockAddr) labelMap
    (mainCrucBlock, auxCrucBlocks) <- CG.runCrucGen archFns (offPosFn blockAddr) label inputReg $ do
      mapM_ (CG.addMacawStmt blockAddr) (M.pblockStmts block)
      assignBlockEnd archFns block_end_var (M.pblockTermStmt block)
      case S.member blockAddr termAddrs of
        True -> do
          -- NOTE: If the entry block is also a terminator, we'll just
          -- return at the end of the entry block and ignore all other
          -- blocks.  This is the intended behavior, but it is an
          -- interesting consequence.

          -- Convert the existing terminator into a return.  This function
          -- preserves the existing register state, which is important when
          -- generating the Crucible return.
          let retTerm = MS.termStmtToReturn (M.pblockTermStmt block)
          CG.addMacawParsedTermStmt labelMapWithReturns [] blockAddr retTerm
        False -> CG.addMacawParsedTermStmt labelMapWithReturns [] blockAddr (M.pblockTermStmt block)
    return (reverse (mainCrucBlock : auxCrucBlocks))
  return (entryLabel, initCrucBlock : (initExtraCrucBlocks ++ concat crucBlocks ++ concat syntheticBlocks ++ retBlocks))
  where
    entryAddr = M.pblockAddr entry
    entryPos = posFn entryAddr
    archRegTy = C.StructRepr (CG.crucArchRegTypes archFns)
    -- Addresses of blocks marked as terminators
    termAddrs = S.fromList (fmap M.pblockAddr terms)
    retEdges = Map.fromListWith S.union [(src, S.singleton tgt) | (src, tgt) <- retEdges_]

    -- Blocks are "body blocks" if they are not the entry or marked as
    -- terminator blocks.  We need this distinction because we modify terminator
    -- blocks to end in a return (even if they don't naturally do so).
    isBodyBlock :: M.ParsedBlock arch ids -> Bool
    isBodyBlock pb = not (S.member (M.pblockAddr pb) termAddrs) && M.pblockAddr pb /= entryAddr

    -- Blocks that are not the entry or terminators
    realBody = filter isBodyBlock body0
    -- The list of all blocks without duplicates
    allBlocks = entry : (realBody ++ terms)

    offPosFn :: (M.MemWidth (M.ArchAddrWidth arch)) => M.ArchSegmentOff arch -> M.ArchAddrWord arch -> WPL.Position
    offPosFn base = posFn . fromJust . M.incSegmentOff base . toInteger

    -- There may be blocks that are jumped to but not included in the list of
    -- blocks provided in this slice.  We need to add synthetic blocks to stand in
    -- for them.  The blocks are simple: they just assert False to indicate that
    -- those branches are never taken.
    makeSyntheticBlock :: forall s
                        . (M.MemWidth (M.ArchAddrWidth arch))
                       => CR.Reg s (CG.ArchRegStruct arch)
                       -> (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (CG.MacawExt arch) s (CG.ArchRegStruct arch)]])
                       -> M.ArchSegmentOff arch
                       -> CG.MacawMonad arch ids s (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (CG.MacawExt arch) s (CG.ArchRegStruct arch)]])
    makeSyntheticBlock inputReg (lm, blks) baddr =
      case Map.lookup baddr lm of
        Just _ -> return (lm, blks)
        Nothing -> do
          synLabel <- CR.Label <$> CG.mmFreshNonce
          (synBlock, extraSynBlocks) <- CG.runCrucGen archFns (offPosFn baddr) synLabel inputReg $ do
            falseAtom <- CG.valueToCrucible (M.BoolValue False)
            msg <- CG.appAtom (C.StringLit (C.UnicodeLiteral "Elided block"))
            CG.addStmt (CR.Assume falseAtom msg)
            errMsg <- CG.crucibleValue (C.StringLit (C.UnicodeLiteral "Elided block"))
            CG.addTermStmt (CR.ErrorStmt errMsg)
          return (Map.insert baddr synLabel lm, reverse (synBlock : extraSynBlocks) : blks)

    makeSyntheticBlocks :: forall s
                         . (M.MemWidth (M.ArchAddrWidth arch))
                        => CR.Reg s (CG.ArchRegStruct arch)
                        -> (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (CG.MacawExt arch) s (CG.ArchRegStruct arch)]])
                        -> M.ParsedBlock arch ids
                        -> CG.MacawMonad arch ids s (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (CG.MacawExt arch) s (CG.ArchRegStruct arch)]])
    makeSyntheticBlocks inputReg (lm, blks) blk =
      F.foldlM (makeSyntheticBlock inputReg) (lm, blks) (parsedTermTargets (M.pblockTermStmt blk))

    makeReturnBlock :: forall s
                     . (M.MemWidth (M.ArchAddrWidth arch))
                    => CR.Reg s (CG.ArchRegStruct arch)
                    -> CG.MacawMonad arch ids s (CR.Label s, [CR.Block (CG.MacawExt arch) s (CG.ArchRegStruct arch)])
    makeReturnBlock inputReg = do
      lbl <- CR.Label <$> CG.mmFreshNonce
      (blk, blks) <- CG.runCrucGen archFns syntheticPos lbl inputReg $ do
        regs <- CG.getRegs
        CG.addTermStmt (CR.Return regs)
      return (lbl, blk:blks)
      where
      syntheticPos w = WPL.OtherPos ("synthetic return block for mkBlockSliceRegCFG; offset " <> T.pack (show w))

-- | Construct a Crucible CFG from a (possibly incomplete) collection of macaw blocks
--
-- The CFG starts with the provided entry block and returns from the terminal
-- block.  Control flow between the remaining (body) blocks is preserved.  If a
-- block ends in a branch to a block not included in the body, the translation
-- will generate a new block that simply asserts false (i.e., that execution
-- should never reach that block).  The terminal block will have its term
-- statement translated into a return.
--
-- The entry and terminal block can be the same, in which case the body is
-- expected to be empty (and will be ignored).
--
-- The intended use of this function is to ask for models of registers after a
-- subset of code in a function has executed by examining the register state
-- after the fragment executes.
mkBlockSliceCFG :: forall arch ids
                 . HasArchEndCase arch
                => CG.MacawSymbolicArchFunctions arch
                -> C.HandleAllocator
                -> (M.ArchSegmentOff arch -> WPL.Position)
                -> M.ParsedBlock arch ids
                -- ^ Entry block
                -> [M.ParsedBlock arch ids]
                -- ^ Non-entry non-terminal blocks
                -> [M.ParsedBlock arch ids]
                -- ^ Terminal blocks
                -> [(M.ArchSegmentOff arch, M.ArchSegmentOff arch)]
                -- ^ (Source, target) block address pairs to convert to returns
                -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
                -- ^ variable to optionally retain how the block originally exited
                -> IO (C.SomeCFG (CG.MacawExt arch) (EmptyCtx ::> CG.ArchRegStruct arch) (CG.ArchRegStruct arch))
mkBlockSliceCFG archFns halloc posFn entry body terms retEdges block_end_var =
  MS.toCoreCFG archFns <$> mkBlockSliceRegCFG archFns halloc posFn entry body terms retEdges block_end_var

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

blockEndAtom :: forall arch ids s
              . MS.MacawSymbolicArchFunctions arch
             -> MacawBlockEnd arch
             -> CG.CrucGen arch ids s (CR.Atom s (MacawBlockEndType arch))
blockEndAtom archFns (MacawBlockEnd blendK mret) = CG.crucGenArchConstraints archFns $ do
    blendK' <- CG.bvLit knownNat (toInteger $ fromEnum blendK)
    let
      memWidthNatRepr = M.memWidthNatRepr @(M.ArchAddrWidth arch)
      ptrRepr = MM.LLVMPointerRepr memWidthNatRepr
    mret' <- case mret of
      Just addr -> do
        ptr <- CG.valueToCrucible $ M.RelocatableValue (M.addrWidthRepr (Proxy @(M.ArchAddrWidth arch))) (M.segoffAddr addr)
        CG.appAtom $ C.JustValue ptrRepr ptr
      Nothing -> do
        CG.appAtom $ C.NothingValue ptrRepr
    let repr = Ctx.empty Ctx.:> C.BVRepr knownNat Ctx.:> C.MaybeRepr ptrRepr
    CG.appAtom $ C.MkStruct repr (Ctx.empty Ctx.:> blendK' Ctx.:> mret')

assignBlockEnd :: HasArchEndCase arch =>
                  CG.MacawSymbolicArchFunctions arch
               -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
               -> M.ParsedTermStmt arch ids
               -> CG.CrucGen arch ids s ()
assignBlockEnd _ Nothing _ = return ()
assignBlockEnd archFns (Just blendVar) stmt = CG.crucGenArchConstraints archFns $ do
  let blend = termStmtToBlockEnd stmt
  blend' <- blockEndAtom archFns blend
  CG.addStmt $ CR.WriteGlobal blendVar blend'

isBlockEndCase :: IsSymInterface sym
               => Proxy arch
               -> sym
               -> C.RegValue sym (MacawBlockEndType arch)
               -> MacawBlockEndCase
               -> IO (Pred sym)
isBlockEndCase _ sym (_ Ctx.:> C.RV blendC' Ctx.:> _) blendC = do
  blendC'' <- bvLit sym knownNat (BV.mkBV knownNat (toInteger $ fromEnum blendC))
  isEq sym blendC' blendC''

blockEndCase :: IsSymInterface sym
             => Proxy arch
             -> sym
             -> C.RegValue sym (MacawBlockEndType arch)
             -> IO (C.MuxTree sym MacawBlockEndCase)
blockEndCase arch sym blend = do
  foldM addCase (C.toMuxTree sym MacawBlockEndFail) [minBound..maxBound]
  where
    addCase mt blendC = do
      p <- isBlockEndCase arch sym blend blendC
      C.mergeMuxTree sym p (C.toMuxTree sym blendC) mt

blockEndReturn :: Proxy arch
               -> C.RegValue sym (MacawBlockEndType arch)
               -> (C.RegValue sym (C.MaybeType (MM.LLVMPointerType (M.ArchAddrWidth arch))))
blockEndReturn _ (_ Ctx.:> _ Ctx.:> C.RV mret) = mret

initBlockEnd :: IsSymInterface sym
             => Proxy arch
             -> sym
             -> IO (C.RegValue sym (MacawBlockEndType arch))
initBlockEnd _ sym = do
  blendK <- bvLit sym (knownNat @8) (BV.mkBV (knownNat @8) (toInteger $ fromEnum MacawBlockEndReturn))
  return $ (Ctx.empty Ctx.:> C.RV blendK Ctx.:> C.RV Unassigned)

parsedTermTargets :: M.ParsedTermStmt arch ids -> [M.ArchSegmentOff arch]
parsedTermTargets t =
  case t of
    M.ParsedCall _ Nothing -> []
    M.ParsedCall _ (Just ret) -> [ret]
    M.ParsedJump _ addr -> [addr]
    M.ParsedBranch _ _ taddr faddr -> [taddr, faddr]
    M.ParsedLookupTable _layout _ _ addrs -> F.toList addrs
    M.ParsedReturn {} -> []
    M.ParsedArchTermStmt _ _ Nothing -> []
    M.ParsedArchTermStmt _ _ (Just addr) -> [addr]
    M.PLTStub {} -> []
    M.ParsedTranslateError {} -> []
    M.ClassifyFailure {} -> []

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
