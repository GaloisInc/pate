{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Discovery.PLT (
  pltStubSymbols
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
import           GHC.TypeLits ( KnownNat )
import           Data.Word ( Word32 )

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

  let revNameRelaMap = F.foldl' (pltStubAddress dynSec vam vreqm getRelSymIdx) [] rels
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

    pltStubAddress dynSec vam vreqm getRelSymIdx accum rel
      | Right (symtabEntry, _versionedVal) <- EEP.dynSymEntry dynSec vam vreqm (getRelSymIdx rel) =
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
