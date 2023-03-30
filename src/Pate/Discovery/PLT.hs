{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Discovery.PLT (
    pltStubSymbols
  , pltStubClassifier
  , extraJumpClassifier
  , extraReturnClassifier
  , ExtraJumps
  , ExtraJumpTarget(..)
  ) where

import           Control.Applicative ( (<|>) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as EE
import qualified Data.ElfEdit.Prim as EEP
import qualified Data.Foldable as F
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import           Data.Word ( Word32 )

import qualified Control.Monad.RWS as CMR
import qualified Data.Macaw.Discovery as Parsed
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import qualified Data.Macaw.Architecture.Info as Info
import Control.Lens ((^.), (&))
import Data.Macaw.Types
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.Memory as MM
import Data.Macaw.Architecture.Info
import qualified Data.Macaw.CFG as MM
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Macaw.AbsDomain.AbsState
import Data.Macaw.CFG
import Control.Monad (forM)
import qualified Data.Text as T
import Data.List (find)
-- | A wrapper type to make it easier to extract both Rel and Rela entries
data SomeRel tp where
  SomeRel :: [r tp] -> (r tp -> Word32) -> SomeRel tp

-- | Match up names PLT stub entries
--
-- Calls to functions in shared libraries are issued through PLT stubs. These
-- are short sequences included in the binary by the compiler that jump to the
-- *real* function implementation in the shared library via the Global Offset
-- Table.  The GOT is populated by the dynamic loader.
--
-- See Note [PLT Stub Names] for details
pltStubSymbols
  :: forall arch w proxy reloc
   . ( KnownNat w
     , w ~ EEP.RelocationWidth reloc
     , Integral (EEP.ElfWordType w)
     , EEP.IsRelocationType reloc
     )
  => proxy arch
  -> proxy reloc
  -> EEP.ElfHeaderInfo w
  -> Map.Map BS.ByteString (BVS.BV w)
pltStubSymbols _ _ elfHeaderInfo = Map.fromList $ fromMaybe [] $ do
  let (_, elf) = EE.getElf elfHeaderInfo
  vam <- EEP.virtAddrMap elfBytes phdrs
  rawDynSec <- listToMaybe (EE.findSectionByName (BSC.pack ".dynamic") elf)

  let dynBytes = EE.elfSectionData rawDynSec
  dynSec <- case EEP.dynamicEntries (EE.elfData elf) (EE.elfClass elf) dynBytes of
    Left _dynErr -> Nothing
    Right dynSec -> return dynSec

  SomeRel rels getRelSymIdx <- case EEP.dynPLTRel @reloc dynSec vam of
    Right (EEP.PLTRela relas) -> return (SomeRel relas EEP.relaSym)
    Right (EEP.PLTRel rels) -> return (SomeRel rels EEP.relSym)
    _ -> Nothing

  vreqm <- case EEP.dynVersionReqMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  vdefm <- case EEP.dynVersionDefMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  let revNameRelaMap = F.foldl' (pltStubAddress dynSec vam vdefm vreqm getRelSymIdx) [] rels
  let nameRelaMap = zip [0..] (reverse revNameRelaMap)
  pltGotSec <- listToMaybe (EE.findSectionByName (BSC.pack ".plt.got") elf)
           <|> listToMaybe (EE.findSectionByName (BSC.pack ".plt") elf)
  let pltGotBase = EE.elfSectionAddr pltGotSec

  -- FIXME: This calculation is right for a .plt section; I think that the
  -- .plt.got variant is 16 bytes per entry
  return [ (symName, BVS.mkBV BVS.knownNat addr)
         | (idx, symName) <- nameRelaMap
         , let addr = 20 + idx * 12 + toInteger pltGotBase
         ]
  where
    phdrs = EE.headerPhdrs elfHeaderInfo
    elfBytes = EE.headerFileContents elfHeaderInfo

    pltStubAddress dynSec vam vdefm vreqm getRelSymIdx accum rel
      | Right (symtabEntry, _versionedVal) <- EEP.dynSymEntry dynSec vam vdefm vreqm (getRelSymIdx rel) =
          EE.steName symtabEntry : accum
      | otherwise = accum

{- Note [PLT Stub Names]

In a dynamically linked binary, the compiler issues calls to shared library
functions by jumping to a PLT stub. The PLT stub jumps to an address taken from
the Global Offset Table (GOT), which is populated by the dynamic loader based on
where the shared library is mapped into memory.

These PLT stubs are not inherently assigned names, but we would like to have
sensible names that we can use to specify overrides for dynamically-linked
functions (e.g., libc calls). For example, we might want to install overrides
for both @malloc@ and @malloc\@plt@ (with the latter representing a call to a
dynamically linked library function).

PLT stubs do not have their own names in any symbol table. Instead, entries in
the Global Offset Table have names in the form of dynamic PLT relocations.  We
get those from elf-edit via the 'EEP.dynPLTRel' function. Note that these
relocations do not have their own directly associated names; instead, there is a
list of rela entries and a separate list of symbols. The list of rela entries
contains function relocations while the list of dynamic symbols
('EEP.dynSymEntry') contains both function and object symbols. To align them, we
must just discard the non-function entries. We do this by checking if the
current symbol entry is of function type; if it is not, we just grab the next
function symbol in the list.

That step gives us names for global offset table entries, but *not* names for
PLT stubs. We rely on the fact that the list of PLT stubs is in the same order
as the list of global offset table entries.  The previous step gives us the
*index* of each entry and a name for that entry. To get the name of the PLT stub
itself, we just compute the relevant offset from the base of the .plt.got
section.  Each PLT stub is 16 bytes on most architectures. The address of the
PLT stub of an entry is @addrOf(.plt.got) + 16 * (1 + idx)@. The offset of one
seems to be required because the first entry is some other kind of metadata or
otherwise ignored.

-}

--FIXME: Move

data ExtraJumpTarget arch = 
    DirectTargets (Set (MM.ArchSegmentOff arch))
  | ReturnTarget
  deriving (Eq, Ord)

instance MemWidth (RegAddrWidth (ArchReg arch)) => Show (ExtraJumpTarget arch) where
  show (DirectTargets es) = show es
  show ReturnTarget = "{return}"

instance Semigroup (ExtraJumpTarget arch) where
  (DirectTargets a) <> (DirectTargets b) = DirectTargets (a <> b)
  _ <> _ = ReturnTarget

type ExtraJumps arch = (Map (MM.ArchSegmentOff arch) (ExtraJumpTarget arch))

lastInstructionStart :: [Stmt arch ids] -> Maybe (MM.MemWord (MM.ArchAddrWidth arch), T.Text)
lastInstructionStart stmts = case find (\case {InstructionStart{} -> True; _ -> False}) (reverse stmts) of
  Just (InstructionStart addr nm) -> Just (addr,nm)
  _ -> Nothing

extraReturnClassifier :: ExtraJumps arch -> BlockClassifier arch ids
extraReturnClassifier jumps = classifierName "Extra Return" $ do
  bcc <- CMR.ask
  let ainfo = pctxArchInfo (classifierParseContext bcc)
  Info.withArchConstraints ainfo $ do
    startAddr <- CMR.asks (Info.pctxAddr . Info.classifierParseContext)
    Just (instr_off, instr_txt) <- return $ lastInstructionStart (F.toList (classifierStmts bcc)) 
    Just final_addr <- return $ MM.incSegmentOff startAddr (fromIntegral instr_off)
    case Map.lookup final_addr jumps of
      Just ReturnTarget -> return ()
      _ -> fail $ "No extra returns for instruction: " ++ show final_addr ++ " (" ++ show instr_txt ++ ")"
    pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList (classifierStmts bcc)
                              , Parsed.parsedTerm = Parsed.ParsedReturn (classifierFinalRegState bcc)
                              , Parsed.writtenCodeAddrs = classifierWrittenAddrs bcc
                              , Parsed.intraJumpTargets = []
                              , Parsed.newFunctionAddrs = []
                              }

extraJumpClassifier :: ExtraJumps arch -> BlockClassifier arch ids
extraJumpClassifier jumps = classifierName "Extra Jump" $ do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx

  Info.withArchConstraints ainfo $ do
    startAddr <- CMR.asks (Info.pctxAddr . Info.classifierParseContext)
    -- FIXME: This is not exactly right, but I'm not sure if there's a better way to find the 
    -- address corresponding to this instruction. Maybe examine the statements?
    Just (instr_off, instr_txt) <- return $ lastInstructionStart (F.toList (classifierStmts bcc)) 

    Just final_addr <- return $ MM.incSegmentOff startAddr (fromIntegral instr_off)
    targets <- case Map.lookup final_addr jumps of
      Just (DirectTargets targets)  -> return $ Set.toList targets
      _ -> fail $ "No extra jumps for instruction: " ++ show final_addr ++ " (" ++ show instr_txt ++ ")"

    let abst = finalAbsBlockState (classifierAbsState bcc) (classifierFinalRegState bcc)
    let tgtBnds = Jmp.postJumpBounds (classifierJumpBounds bcc) (classifierFinalRegState bcc)

    termStmt <- case targets of
      [oneTarget] -> return $ Parsed.ParsedJump (classifierFinalRegState bcc) oneTarget
      {- [target1, target2] -> do
        -- we don't have a good way to reify the branch condition here, but
        -- it's not strictly necessary that the ParsedBranch condition be valid, as
        -- long as the two targets are correct
        -- ideally we'd just set this to "undefined", but there's no good way to 
        -- create new macaw terms here
        return $ Parsed.ParsedBranch (classifierFinalRegState bcc) (MM.CValue (MM.BoolCValue True)) target1 target2
      -}
      _ -> fail $ "Unsupported extra targets: " ++ show targets
    
    jumpTargets <- forM targets $ \tgt -> do
      let abst' = abst & setAbsIP tgt
      return $ (tgt, abst', tgtBnds)

    pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList (classifierStmts bcc)
                              , Parsed.parsedTerm  = termStmt
                              , Parsed.writtenCodeAddrs = classifierWrittenAddrs bcc
                              , Parsed.intraJumpTargets = jumpTargets
                              , Parsed.newFunctionAddrs = targets
                              }

-- | Classifier for PLT stubs which uses an externally-defined function to determine if a given
--   macaw value represents an address that jumps to a PLT stub
pltStubClassifier ::
  forall arch ids.
  (Value arch ids (BVType (ArchAddrWidth arch)) -> Maybe (ArchSegmentOff arch, BSC.ByteString)) -> 
  Info.BlockClassifier arch ids
pltStubClassifier f = classifierName "Extra PLT Stub" $ do
  stmts <- CMR.asks Info.classifierStmts
  ainfo <- CMR.asks (Info.pctxArchInfo . Info.classifierParseContext)
  Info.withArchConstraints ainfo $ do
    finalRegs <- CMR.asks Info.classifierFinalRegState
    bcc <- CMR.ask
    startAddr <- CMR.asks (Info.pctxAddr . Info.classifierParseContext)
    blkSz <- CMR.asks Info.classifierBlockSize
    Just ret <- return $ MM.incSegmentOff startAddr (fromIntegral blkSz)
    v <- pure $ Info.classifierFinalRegState bcc ^. boundValue ip_reg
    case f v of
      Just (addr,_) -> do
        return Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts
                                    , Parsed.parsedTerm = Parsed.ParsedCall finalRegs (Just ret)
                                    , Parsed.intraJumpTargets = 
                                        [( ret
                                         , Info.postCallAbsState ainfo (classifierAbsState bcc) finalRegs ret
                                         , Jmp.postCallBounds (Info.archCallParams ainfo) (classifierJumpBounds bcc) finalRegs
                                         )]
                                    , Parsed.newFunctionAddrs = [addr]
                                    , Parsed.writtenCodeAddrs = Info.classifierWrittenAddrs bcc
                                    } 
      Nothing -> fail "Not a PLT stub"



{-

  --(cond, callTarget, returnAddr, fallthroughIP, callBranch, stmts') <- MAI.liftClassifier (identifyConditionalCall mem stmts regs)
  jmpBounds <- CMR.asks MAI.classifierJumpBounds
  ainfo <- CMR.asks (MAI.pctxArchInfo . MAI.classifierParseContext)

  case Jmp.postBranchBounds jmpBounds regs cond of
    Jmp.BothFeasibleBranch trueJumpState falseJumpState -> do
      let abs' = MDC.branchBlockState ainfo absState stmts regs cond (callBranch == CallsOnFalse)
      let fallthroughTarget = ( fallthroughIP
                              , abs'
                              , if callBranch == CallsOnTrue then falseJumpState else trueJumpState
                              )
      return Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts'
                                   , Parsed.parsedTerm = Parsed.PLTStub regs addr
                                   , Parsed.intraJumpTargets = [fallthroughTarget]
                                   , Parsed.newFunctionAddrs = extractCallTargets mem callTarget
                                   , Parsed.writtenCodeAddrs = writtenAddrs
                                   }
    Jmp.TrueFeasibleBranch _ -> fail "Infeasible false branch"
    Jmp.FalseFeasibleBranch _ -> fail "Infeasible true branch"
    Jmp.InfeasibleBranch -> fail "Branch targets are both infeasible"
-}