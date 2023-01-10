{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}

module Pate.Monad.Environment (
    EquivEnv(..)
  , envCtxL
  , BlockCache(..)
  , freshBlockCache
  , ExitPairCache
  ) where

import qualified Control.Concurrent as IO
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Lens as L

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.Time as TM

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Data.IORef as IO
import qualified Data.Parameterized.SetF as SetF

import qualified Lumberjack as LJ

import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.CFG as MC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as CS

import qualified What4.Interface as W4

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence.Statistics as PES
import qualified Pate.Event as PE
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Location as PL
import qualified Pate.Proof as PF
import qualified Pate.Solver as PSo
import qualified Pate.SymbolTable as PSym
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Override.Library as PVOL
import           Pate.TraceTree

data EquivEnv sym arch where
  EquivEnv ::
    { envWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
    , envValidArch :: PA.SomeValidArch arch
    , envCtx :: PMC.EquivalenceContext sym arch
    , envArchVals :: MS.GenArchVals MT.MemTraceK arch
    , envLLVMArchVals :: MS.GenArchVals MS.LLVMMemory arch
    , envExtensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
    , envPCRegion :: W4.SymNat sym
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MCS.MacawBlockEndType arch)
    -- ^ The global variable used to hold memory for the LLVM memory model while
    -- symbolically executing functions in the "inline callee" feature
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envConfig :: PC.VerificationConfig PA.ValidRepr
    -- ^ input equivalence problems to solve
    , envValidSym :: PSo.Sym sym
    -- ^ expression builder, wrapped with a validity proof
    , envStartTime :: TM.UTCTime
    -- ^ start checkpoint for timed events - see 'startTimer' and 'emitEvent'
    , envCurrentFrame :: PAS.AssumptionSet sym
    -- ^ the current assumption frame, accumulated as assumptions are added
    , envPathCondition :: PAS.AssumptionSet sym
    -- ^ assumptions specific to a particular path (subsumed by envCurrentFrame)
    , envNonceGenerator :: N.NonceGenerator IO (PF.SymScope sym)
    , envParentNonce :: Some (PF.ProofNonce sym)
    -- ^ nonce of the parent proof node currently in scope
    , envUndefPointerOps :: MT.UndefinedPtrOps sym
    , envParentBlocks :: [PB.BlockPair arch]
    -- ^ all block pairs on this path from the toplevel
    , envEqCondFns :: Map (PB.FunPair arch) (PL.SomeLocation sym arch -> Bool)
    -- ^ functions that should be considered for generating equivalence conditions
    , envExitPairsCache :: ExitPairCache arch
    -- ^ cache for intermediate proof results
    , envStatistics :: MVar.MVar PES.EquivalenceStatistics
    -- ^ Statistics collected during verification
    , envOverrides :: forall w
                    . (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w)
                   => PVOL.OverrideConfig sym w
                   -> M.Map PSym.Symbol (PVO.SomeOverride arch sym)
    -- ^ Overrides to apply in the inline-callee symbolic execution mode
    , envTreeBuilder :: TreeBuilder '(sym, arch)
    , envUnsatCacheRef :: IO.IORef (SolverCache sym)
    , envSatCacheRef :: IO.IORef (SolverCache sym)
    , envTargetEquivRegs :: Set.Set (Some (MC.ArchReg arch))
    , envPtrAssertions :: MT.PtrAssertions sym
    } -> EquivEnv sym arch

-- pushing assumption contexts should:
--    preserve the Unsat cache from the outer context into the inner context
--    (i.e. adding assumptions cannot make an unsatsfiable predicate satisfiable)
--    discard the Sat cache from the outer context
--    (i.e. previously satisfiable predicate may become unsatisfiable with more assumpionts)
-- popping assumption contexts should
--    discard any discovered Unsat results from inner context
--    (i.e. relaxing assumptions may cause previously unsatsfiable results to now be satisfiable)
--    preserve any learned Sat results from inner context
--    (i.e. relaxing assumptions cannot may a satsifiable result unsatisfiable)
type SolverCache sym = SetF.SetF (W4.SymExpr sym) W4.BaseBoolType

type ExitPairCache arch = BlockCache arch (Set.Set (PPa.PatchPair (PB.BlockTarget arch)))

data BlockCache arch a where
  BlockCache :: IO.MVar (Map (PB.BlockPair arch) a) -> BlockCache arch a

envCtxL :: L.Lens' (EquivEnv sym arch) (PMC.EquivalenceContext sym arch)
envCtxL f ee = fmap (\c' -> ee { envCtx = c' }) (f (envCtx ee))

freshBlockCache ::
  IO (BlockCache arch a)
freshBlockCache = BlockCache <$> IO.newMVar M.empty
