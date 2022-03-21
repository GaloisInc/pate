{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Pate.Config (
  Hex(..),
  BlockData,
  FunctionAddr,
  PatchData(..),
  noPatchData,
  RunConfig(..),
  VerificationConfig(..),
  VerificationMethod(..),
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
type FunctionAddr = Hex Word64

data PatchData =
  PatchData { patchPairs :: [(BlockData, BlockData)]
            , ignorePointers :: ([(BlockData,Hex Word64)],[(BlockData,Hex Word64)])
            -- ^ For the original and patched program, each may come with a list of
            --   "ignorable" pointers.  Each pair in the list consists of a location
            --   and a length.  The locations refer to positions in the global memory
            --   of the programs where pointers may be stored during the program run.
            --   The regions of memory pointed to (with the given length) are inteded
            --   to be ignored by the verifier, so that differences between the two runs
            --   do not result in equivalence failures. Note that this is an _indirect_
            --   notion of ignorability; the locations specified here are themselves
            --   are not ignored, but rather the memory to which they point.

            , equatedFunctions :: [(FunctionAddr, FunctionAddr)]
            -- ^ Pairs of functions (named by their address) that should be
            -- considered to be equivalent, even if they actually have different
            -- effects. This is intended to work with the 'ignorePointers'
            -- feature to enable users to specify that memory changes to certain
            -- memory locations should be ignored, while verifying that the side
            -- effects of the 'equatedFunctions' are benign.
            --
            -- The functions in this list are paired up by call site, and must
            -- be called at aligned call sites in the original and patched
            -- binaries, respectively.
            --
            -- See the documentation on the function replacement verification
            -- feature.
            }
  deriving (Read, Show, Eq)

noPatchData :: PatchData
noPatchData = PatchData { patchPairs = []
                        , ignorePointers = ([],[])
                        , equatedFunctions = []
                        }

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
    , cfgSolverInteractionFile :: Maybe FilePath
    -- ^ A file to save online SMT solver interactions to
    --
    -- This only captures the interaction with the solver during symbolic
    -- execution, and not the one-off queries issued by the rest of the verifier

    , cfgVerificationMethod :: VerificationMethod
    }

data VerificationMethod
  = HoareTripleVerification
  | StrongestPostVerification
 deriving (Eq,Ord,Show)

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
                     , cfgSolverInteractionFile = Nothing
                     , cfgVerificationMethod = HoareTripleVerification
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
