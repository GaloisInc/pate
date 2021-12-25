{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
-- | Definitions of the operations that can appear in memory traces
module Pate.Memory.Trace.Operations (
    Condition(..)
  , conditionPred
  , MemoryWrite(..)
  , MemoryRead(..)
  , MemoryOperation(..)
  ) where

import qualified Data.Parameterized.NatRepr as PN
import           GHC.TypeLits ( KnownNat, type (<=), type (*) )
import qualified What4.Interface as WI

import qualified Data.Macaw.Memory as DMM
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM

-- | The conditions under which a write occurs
data Condition sym = Unconditional
                   | Conditional (WI.Pred sym)

-- | The logical predicate corresponding to the condition
conditionPred
  :: (LCB.IsSymInterface sym)
  => sym
  -> Condition sym
  -> WI.Pred sym
conditionPred sym c =
  case c of
    Unconditional -> WI.truePred sym
    Conditional p -> p

-- | The set of information characterizing a memory write operation
data MemoryWrite sym ptrW numBytes =
  MemoryWrite { storeAddress :: LCLM.LLVMPtr sym ptrW
              -- ^ The address written to
              , storeCondition :: Condition sym
              -- ^ The conditions under which the write applies
              , storeBytesRepr :: PN.NatRepr numBytes
              -- ^ A type repr for the number of bytes written
              , storeValue :: LCLM.LLVMPtr sym (8 * numBytes)
              -- ^ The value stored
              , storeEndianness :: DMM.Endianness
              -- ^ The endianness of the operation
              }

-- | The set of information characterizing a memory read operation
data MemoryRead sym ptrW numBytes =
  MemoryRead { loadAddress :: LCLM.LLVMPtr sym ptrW
             -- ^ The address being read from
             , loadCondition :: Condition sym
             -- ^ The condition under which the write applies
             , loadBytesRepr :: PN.NatRepr numBytes
             -- ^ The number of bytes being read (type level representative)
             , loadEndianness :: DMM.Endianness
             -- ^ The endianness of the operation
             }

-- | A memory operation recorded in the memory trace
data MemoryOperation sym ptrW where
  MemoryWriteOperation :: (1 <= ptrW) => MemoryWrite sym ptrW bytes -> MemoryOperation sym ptrW
  MemoryReadOperation :: (1 <= ptrW) => MemoryRead sym ptrW bytes -> MemoryOperation sym ptrW
