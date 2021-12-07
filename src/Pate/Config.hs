{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Pate.Config (
  Hex(..),
  BlockData,
  PatchData(..),
  noPatchData,
  RunConfig(..),
  VerificationConfig(..),
  defaultVerificationCfg
  ) where

import           Data.Word ( Word64 )

import qualified Lumberjack as LJ
import           Text.Printf ( PrintfArg, printf )

import qualified Pate.Arch as PA
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Solver as PS
import qualified Pate.Timeout as PT

newtype Hex a = Hex a
  deriving (Eq, Ord, Num, PrintfArg)

instance (Num a, Show a, PrintfArg a) => Show (Hex a) where
  show (Hex a) = printf "0x%x" a

instance (Read a) => Read (Hex a) where
  readsPrec i s = [ (Hex a, s') | (a, s') <- readsPrec i s ]

type BlockData = Hex Word64

data PatchData =
  PatchData { patchPairs :: [(BlockData, BlockData)]
            , ignorePointers :: ([BlockData],[BlockData])
            }
  deriving (Read, Show, Eq)

noPatchData :: PatchData
noPatchData = PatchData [] ([],[])

----------------------------------
-- Verification configuration
data VerificationConfig =
  VerificationConfig
    { cfgPairMain :: Bool
    -- ^ start by pairing the entry points of the binaries
    , cfgDiscoverFuns :: Bool
    -- ^ discover additional functions pairs during analysis
    , cfgComputeEquivalenceFrames :: Bool
    -- ^ compute fine-grained equivalence frames using heuristics
    -- if false, pre-domains will simply be computed as any possible
    -- relevant state. A failed result in this mode will fallback
    -- to attempting to use fine-grained domains.
    , cfgEmitProofs :: Bool
    -- ^ emit a structured spine of the equivalence proofs
    , cfgSolver :: PS.Solver
    -- ^ The SMT solver to use to discharge proof goals
    , cfgHeuristicTimeout :: PT.Timeout
    -- ^ The timeout to use for short heuristic queries that are allowed to fail
    -- (where there is a reasonable default)
    , cfgGoalTimeout :: PT.Timeout
    -- ^ The timeout to apply to proof goals
    , cfgGroundTimeout :: PT.Timeout
    -- ^ The timeout to use when grounding terms. We expect this to be
    -- fast and therefore a delay indicates a problem with the solver
    , cfgMacawDir :: Maybe FilePath
    -- ^ The directory to save macaw CFGs to
    }

defaultVerificationCfg :: VerificationConfig
defaultVerificationCfg =
  VerificationConfig { cfgPairMain = True
                     , cfgDiscoverFuns = True
                     , cfgComputeEquivalenceFrames = True
                     , cfgEmitProofs = True
                     , cfgSolver = PS.Yices
                     , cfgHeuristicTimeout = PT.Seconds 10
                     , cfgGoalTimeout = PT.Minutes 5
                     , cfgGroundTimeout = PT.Seconds 5
                     , cfgMacawDir = Nothing
                     }

data RunConfig arch =
  RunConfig
    { archProxy :: PA.SomeValidArch arch
    , infoPath :: Either FilePath PatchData
    , origPath :: FilePath
    , patchedPath :: FilePath
    , logger :: LJ.LogAction IO (PE.Event arch)
    , verificationCfg :: VerificationConfig
    , origHints :: PH.VerificationHints
    , patchedHints :: PH.VerificationHints
    }
