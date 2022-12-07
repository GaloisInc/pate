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

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.Chan as CCC
import           Control.Lens ( (^.) )
import qualified Data.Aeson as JSON
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Interval as DII
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Sequence as Seq
import           GHC.Generics ( Generic )
import qualified What4.BaseTypes as WT
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM

import qualified Pate.Address as PA
import qualified Pate.Block as PB
import qualified Pate.Binary as PBi
import qualified Pate.Event as PE
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Solver as PS
import qualified Pate.Verification.MemoryLog as PVM

data SomeProofEvent arch where
  SomeProofEvent :: PPa.PatchPair (PE.Blocks arch) -> PFI.SomeProofNonceExpr arch tp -> SomeProofEvent arch

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
                    | ConditionalEquivalenceNode { differentialSummaryOriginal :: Address
                                                 , differentialSummaryPatched :: Address
                                                 , conditionalModel :: [(String, String)]
                                                 , differentialSummary :: String
                                                 }
  deriving (Generic)

instance JSON.ToJSON SavedProofNode

-- | Turn a ground value into a string
--
-- This is unfortunately a bit verbose because 'WEG.GroundValue' is a type
-- family, and thus has no instances. We have to match on the type repr to
-- resolve the real type on each branch to take advantage of the underlying show
-- instances.
--
-- Note that structs and arrays are not handled here - we don't actually use
-- them, so it doesn't seem very important. If we want, we can actually write
-- those instances instance if we want.
printGroundValue :: PS.Sym sym -> WI.SymExpr sym tp -> WEG.GroundValueWrapper tp -> String
printGroundValue (PS.Sym {}) expr (WEG.GVW gv) =
  case WI.exprType expr of
    WT.BaseBoolRepr -> show gv
    WT.BaseBVRepr {} -> show gv
    WT.BaseIntegerRepr -> show gv
    WT.BaseRealRepr -> show gv
    WT.BaseFloatRepr {} -> show gv
    WT.BaseStringRepr {} -> show gv
    WT.BaseComplexRepr -> show gv
    WT.BaseStructRepr {} -> "<struct>"
    WT.BaseArrayRepr {} -> "<array>"

blockAddress :: (DMC.MemWidth (DMC.ArchAddrWidth arch)) => PE.Blocks arch bin -> Address
blockAddress (PE.Blocks w cb _) =
  Address w (BVS.mkBV w (toInteger (DMM.addrOffset memAddr)))
  where
    memAddr = PA.addrToMemAddr (PB.concreteAddress cb)

-- FIXME: update this code to support singletons PatchPair values?
pOriginal :: PPa.PatchPair tp -> tp PBi.Original
pOriginal (PPa.PatchPair o _) = o
pOriginal (PPa.PatchPairOriginal o) = o
pOriginal (PPa.PatchPairPatched _) = PPa.handleSingletonStub

pPatched :: PPa.PatchPair tp -> tp PBi.Patched
pPatched (PPa.PatchPair _ p) = p
pPatched (PPa.PatchPairPatched p) = p
pPatched (PPa.PatchPairOriginal _) = PPa.handleSingletonStub


toJSON :: SomeProofEvent arch -> Maybe JSON.Value
toJSON (SomeProofEvent blks proofSym) = do
  PFI.SomeProofNonceExpr (sym@PS.Sym {}) (PF.ProofNonceExpr _ _ app) <- return proofSym
  case app of
    PF.ProofInlinedCall _blks (Right inlineResult) -> do
      let w = inlineResult ^. PVM.pointerWidth
      let idx = PVM.indexWriteAddresses w (inlineResult ^. PVM.differingGlobalMemoryLocations)
      let node = InlineResultNode { inlineOriginalFunctionAddress = blockAddress (pOriginal blks)
                                  , inlinePatchedFunctionAddress = blockAddress (pPatched blks)
                                  , differingGlobalMemoryLocations = [ (Address w lo, Address w hi)
                                                                     | DII.ClosedInterval lo hi <- idx
                                                                     ]
                                  }
      return (JSON.toJSON node)
    PF.ProofInlinedCall _blks (Left err) -> do
      let node = InlineErrorNode { inlineOriginalErrorAddress = blockAddress (pOriginal blks)
                                 , inlinePatchedErrorAddress = blockAddress (pPatched blks)
                                 , inlineCallError = err
                                 }
      return (JSON.toJSON node)
    PF.ProofTriple { PF.prfTripleStatus =
                     PF.ProofNonceExpr { PF.prfNonceBody = PF.ProofStatus (PF.VerificationFail _counterexample condEqRes)
                                       }
                   }
      | Nothing <- WI.asConstantPred (PF.condEqPred condEqRes) -> do
          let node = ConditionalEquivalenceNode { differentialSummary = show (WI.printSymExpr (PF.condEqPred condEqRes))
                                                , conditionalModel = [ (show (WI.printSymExpr loc), printGroundValue sym loc gv)
                                                                     | MapF.Pair loc gv <- MapF.toList (PF.condEqExample condEqRes)
                                                                     ]
                                                , differentialSummaryOriginal = blockAddress (pOriginal blks)
                                                , differentialSummaryPatched = blockAddress (pPatched blks)
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
