{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module JSONReport (
    ProofEventConsumer
  , SomeProofEvent(..)
  , consumeProofEvents
  , sendEvent
  , waitForConsumer
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.Chan as CCC
import qualified Data.Aeson as JSON
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Interval as DII
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Sequence as Seq
import           GHC.Generics ( Generic )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM

import qualified Pate.Address as PA
import qualified Pate.Block as PB
import qualified Pate.Event as PE
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Verification.MemoryLog as PVM

data SomeProofEvent arch where
  SomeProofEvent :: PPa.PatchPair (PE.Blocks arch) -> PFI.SomeProofSym arch tp -> SomeProofEvent arch

data ProofEventConsumer arch where
  ProofEventConsumer :: CCC.Chan (Maybe (SomeProofEvent arch)) -> CCA.Async () -> ProofEventConsumer arch

-- | An address for JSON reports, rendered in hex
data Address where
  Address :: PN.NatRepr w -> BVS.BV w -> Address

instance JSON.ToJSON Address where
  toJSON (Address w bv) = JSON.toJSON (BVS.ppHex w bv)

data SavedProofNode = InlineResultNode { inlineOriginalFunctionAddress :: Address
                                       , inlinePatchedFunctionAddress :: Address
                                       , differingGlobalMemoryLocations :: [(Address, Address)]
                                       }
                    | InlineErrorNode { inlineOriginalErrorAddress :: Address
                                      , inlinePatchedErrorAddress :: Address
                                      , inlineCallError :: String
                                      }
  deriving (Generic)

instance JSON.ToJSON SavedProofNode

blockAddress :: (DMC.MemWidth (DMC.ArchAddrWidth arch)) => PE.Blocks arch bin -> Address
blockAddress (PE.Blocks w cb _) =
  Address w (BVS.mkBV w (toInteger (DMM.addrOffset memAddr)))
  where
    memAddr = PA.addrToMemAddr (PB.concreteAddress cb)

toJSON :: SomeProofEvent arch -> Maybe JSON.Value
toJSON (SomeProofEvent blks proofSym) = do
  PFI.SomeProofSym _sym (PF.ProofNonceExpr _ _ app) <- return proofSym
  case app of
    PF.ProofInlinedCall _blks (Right (PVM.SomeWriteSummary _sym inlineResult)) -> do
      let w = inlineResult ^. PVM.pointerWidth
      let idx = PVM.indexWriteAddresses w (inlineResult ^. PVM.differingGlobalMemoryLocations)
      let node = InlineResultNode { inlineOriginalFunctionAddress = blockAddress (PPa.pOriginal blks)
                                  , inlinePatchedFunctionAddress = blockAddress (PPa.pPatched blks)
                                  , differingGlobalMemoryLocations = [ (Address w lo, Address w hi)
                                                                     | DII.ClosedInterval lo hi <- idx
                                                                     ]
                                  }
      return (JSON.toJSON node)
    PF.ProofInlinedCall _blks (Left err) -> do
      let node = InlineErrorNode { inlineOriginalErrorAddress = blockAddress (PPa.pOriginal blks)
                                 , inlinePatchedErrorAddress = blockAddress (PPa.pPatched blks)
                                 , inlineCallError = err
                                 }
      return (JSON.toJSON node)
    _ -> Nothing


saveJSON :: FilePath -> Seq.Seq (SomeProofEvent arch) -> IO ()
saveJSON outFile evts = do
  let vals = mapMaybe toJSON (F.toList evts)
  JSON.encodeFile outFile vals

consumeProofEvents
  :: FilePath
  -- ^ The file to save to
  -> IO (ProofEventConsumer arch)
consumeProofEvents outFile = do
  c <- CCC.newChan
  consumer <- CCA.async (consumeEvents c Seq.empty)
  return (ProofEventConsumer c consumer)
  where
    consumeEvents c savedEvents = do
      mevt <- CCC.readChan c
      case mevt of
        Nothing -> saveJSON outFile savedEvents
        Just evt -> consumeEvents c (savedEvents <> Seq.singleton evt)

sendEvent :: ProofEventConsumer arch -> Maybe (SomeProofEvent arch) -> IO ()
sendEvent (ProofEventConsumer c _) pevt = CCC.writeChan c pevt

waitForConsumer
  :: ProofEventConsumer arch
  -> IO ()
waitForConsumer (ProofEventConsumer _ consumer) =
  CCA.wait consumer
