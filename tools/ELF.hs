{-# LANGUAGE DataKinds #-}
module ELF ( parseElfOrDie ) where

import           Data.Binary.Get
import           Data.ElfEdit
import qualified Data.ByteString as BS
import           System.Exit ( die )

-- | Produce a suitable description of an 'ElfHeaderError'.
showElfHeaderError :: ByteOffset -> String -> String
showElfHeaderError off msg = "Error while parsing ELF header at " ++ show off ++ ": " ++ msg

-- | Print a suitable description of an 'ElfHeaderError' and exit
-- unsuccessfully.
dieElfHeaderError :: ByteOffset -> String -> IO a
dieElfHeaderError off msg = die (showElfHeaderError off msg)

-- | Produce a description of some 'ElfParseError's.
showElfParseErrors :: [ElfParseError] -> String
showElfParseErrors errs = "Errors while parsing ELF file: " ++ show errs

-- | Print a description of some 'ElfParseErrors' and exit unsuccessfully.
dieElfParseErrors :: [ElfParseError] -> IO a
dieElfParseErrors = die . showElfParseErrors

-- | Parses a 'ByteString' into an Elf record exactly as 'parseElf' does. If
-- any errors are encountered, they are displayed and the program exits
-- unsuccessfully; but if everything goes smoothly, one of the two
-- continuations are called.
parseElfOrDie :: (Elf 32 -> IO a) -> (Elf 64 -> IO a) -> BS.ByteString -> IO a
parseElfOrDie k32 k64 bs = case parseElf bs of
  ElfHeaderError off msg -> dieElfHeaderError off msg
  Elf32Res [] e32 -> k32 e32
  Elf64Res [] e64 -> k64 e64
  Elf32Res errs _ -> dieElfParseErrors errs
  Elf64Res errs _ -> dieElfParseErrors errs
