{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module Pate.Metrics (
    BinaryMetrics(..)
  , Metrics(..)
  , emptyMetrics
  , summarize
  ) where

import qualified Data.IntervalMap as IM
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Time as TM

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT

data BinaryMetrics =
  BinaryMetrics { executableBytes :: !Int
                , numFunctions :: !Int
                , numBlocks :: !Int
                }
  deriving (Show)

-- | Aggregate metrics extracted from the verifier
data Metrics =
  Metrics { duration :: Maybe TM.NominalDiffTime
          , usedDiscoveryHints :: !Int
          , invalidHints :: !Int
          , verifiedGoals :: !Int
          , originalBinaryMetrics :: Maybe BinaryMetrics
          , patchedBinaryMetrics :: Maybe BinaryMetrics
          }
  deriving (Show)

emptyMetrics :: Metrics
emptyMetrics =
  Metrics { duration = Nothing
          , usedDiscoveryHints = 0
          , invalidHints = 0
          , verifiedGoals = 0
          , originalBinaryMetrics = Nothing
          , patchedBinaryMetrics = Nothing
          }

loadedBinaryMetrics
  :: (MM.MemWidth (MC.ArchAddrWidth arch))
  => PB.LoadedELF arch
  -> PT.ParsedFunctionMap arch
  -> BinaryMetrics
loadedBinaryMetrics le pfm =
  BinaryMetrics { executableBytes = byteCount
                , numFunctions = length (IM.keys pfm)
                , numBlocks = blockCount
                }
  where
    isExec = MMP.isExecutable . MM.segmentFlags
    segs = MM.memSegments (MBL.memoryImage (PB.loadedBinary le))

    byteCount = sum [ if isExec seg then fromIntegral (MM.segmentSize seg) else 0
                    | seg <- segs
                    ]

    blockCount = sum [ length (IM.elems pbm)
                     | bmap <- IM.elems pfm
                     , Some (PT.ParsedBlockMap pbm) <- Map.elems bmap
                     ]



-- | Summarize a single verifier event into the currently accumulated metrics
summarize :: (MM.MemWidth (MC.ArchAddrWidth arch)) => PE.Event arch -> Metrics -> Metrics
summarize e m =
  case e of
    PE.AnalysisEnd _ dur -> m { duration = Just dur }
    PE.FunctionsDiscoveredFromHints entryPoints -> m { usedDiscoveryHints = length entryPoints }
    PE.FunctionEntryInvalidHints invalid -> m { invalidHints = length invalid }
    PE.LoadedBinaries (origElf, origPFM) (patchedElf, patchedPFM) ->
      m { originalBinaryMetrics = Just (loadedBinaryMetrics origElf origPFM)
        , patchedBinaryMetrics = Just (loadedBinaryMetrics patchedElf patchedPFM)
        }
    PE.ProofIntermediate _bp (PFI.SomeProofSym _sym nonceExpr) _tm ->
      case PPr.prfNonceBody nonceExpr of
        PPr.ProofTriple {} -> m { verifiedGoals = verifiedGoals m + 1 }
        _ -> m
    -- The following cases don't contribute to the aggregate metrics
    PE.CheckedEquivalence {} -> m
    PE.ComputedPrecondition {} -> m
    PE.ElfLoaderWarnings {} -> m
    PE.AnalysisStart {} -> m
    PE.ErrorRaised {} -> m
    PE.Warning {} -> m
    PE.CheckedBranchCompleteness {} -> m
    PE.ProvenGoal {} -> m
    PE.ProofStarted {} -> m
    PE.DiscoverBlockPair {} -> m
    PE.HintErrorsCSV {} -> m
    PE.HintErrorsJSON {} -> m
    PE.HintErrorsDWARF {} -> m
