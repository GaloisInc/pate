{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Pate.Monad.Environment (
    EquivEnv(..)
  , envCtxL
  , BlockCache(..)
  , freshBlockCache
  , ProofCache
  , ExitPairCache
  , VerificationFailureMode(..)
  ) where

import qualified Control.Concurrent as IO
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Lens as L

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Time as TM

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Lumberjack as LJ

import qualified Lang.Crucible.Simulator as CS
import qualified Data.Macaw.Symbolic as MS

import qualified What4.Interface as W4

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Config as PC
import           Pate.Equivalence
import qualified Pate.Equivalence.Statistics as PES
import qualified Pate.Event as PE
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Monad.Context as PMC
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import           Pate.SimState
import qualified Pate.Solver as PSo
import           Pate.Types

data VerificationFailureMode =
    ThrowOnAnyFailure
  | ContinueAfterFailure

data EquivEnv sym arch where
  EquivEnv ::
    { envWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
    , envValidArch :: PA.SomeValidArch arch
    , envCtx :: PMC.EquivalenceContext sym arch
    , envArchVals :: MS.GenArchVals MT.MemTraceK arch
    , envExtensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
    , envPCRegion :: W4.SymNat sym
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MS.MacawBlockEndType arch)
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envConfig :: PC.VerificationConfig
    , envFailureMode :: VerificationFailureMode
    , envBaseEquiv :: EquivRelation sym arch
    , envGoalTriples :: [PF.EquivTriple sym arch]
    -- ^ input equivalence problems to solve
    , envValidSym :: PSo.Sym sym
    -- ^ expression builder, wrapped with a validity proof
    , envStartTime :: TM.UTCTime
    -- ^ start checkpoint for timed events - see 'startTimer' and 'emitEvent'
    , envCurrentFrame :: AssumptionFrame sym
    -- ^ the current assumption frame, accumulated as assumptions are added
    , envNonceGenerator :: N.NonceGenerator IO (PF.ProofScope (PFI.ProofSym sym arch))
    , envParentNonce :: Some (PF.ProofNonce (PFI.ProofSym sym arch))
    -- ^ nonce of the parent proof node currently in scope
    , envUndefPointerOps :: MT.UndefinedPtrOps sym
    , envParentBlocks :: [PPa.BlockPair arch]
    -- ^ all block pairs on this path from the toplevel
    , envProofCache :: ProofCache sym arch
    -- ^ cache for intermediate proof results
    , envExitPairsCache :: ExitPairCache arch
    -- ^ cache for intermediate proof results
    , envStatistics :: MVar.MVar PES.EquivalenceStatistics
    -- ^ Statistics collected during verification
    } -> EquivEnv sym arch

type ProofCache sym arch = BlockCache arch [(PF.EquivTriple sym arch, Par.Future (PFI.ProofSymNonceApp sym arch PF.ProofBlockSliceType))]

type ExitPairCache arch = BlockCache arch [PPa.PatchPair (BlockTarget arch)]

data BlockCache arch a where
  BlockCache :: IO.MVar (Map (PPa.BlockPair arch) a) -> BlockCache arch a

envCtxL :: L.Lens' (EquivEnv sym arch) (PMC.EquivalenceContext sym arch)
envCtxL f ee = fmap (\c' -> ee { envCtx = c' }) (f (envCtx ee))

freshBlockCache ::
  IO (BlockCache arch a)
freshBlockCache = BlockCache <$> IO.newMVar M.empty
