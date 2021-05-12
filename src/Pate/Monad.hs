{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module Pate.Monad
  ( EquivEnv(..)
  , EquivState(..)
  , EquivM
  , EquivM_
  , runEquivM
  , ValidSym
  , EquivalenceContext(..)
  , BinaryContext(..)
  , VerificationFailureMode(..)
  , SimBundle(..)
  , withBinary
  , withValid
  , withValidEnv
  , withSymIO
  , withSym
  , archFuns
  , runInIO1
  , manifestError
  , implicitError
  , throwHere
  , getDuration
  , startTimer
  , emitEvent
  , emitWarning
  , getBinCtx
  , execGroundFn
  , getFootprints
  , memOpCondition
  -- sat helpers
  , checkSatisfiableWithModel
  , isPredTrue
  , isPredSat
  , isPredTrue'
  , isPredTruePar'
  -- working under a 'SimSpec' context
  , withSimSpec
  , withFreshVars
  -- assumption management
  , withAssumption_
  , withAssumption
  , withSatAssumption
  , withAssumptionFrame
  , withAssumptionFrame'
  , withAssumptionFrame_
  , applyAssumptionFrame
  , applyCurrentFrame
  -- nonces
  , freshNonce
  , withProofNonce
  )
  where

import           GHC.Stack ( HasCallStack, callStack )

import qualified Control.Monad.Fail as MF
import qualified Control.Monad.IO.Unlift as IO
import           Control.Exception hiding ( try )
import           Control.Monad.Catch hiding ( catch, catches, Handler )
import           Control.Monad.Reader
import           Control.Monad.Except
import           Control.Monad.State

import qualified Data.ElfEdit as E
import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Time as TM
import           Data.Typeable

import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Lumberjack as LJ

import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MM
import qualified Data.Macaw.Symbolic as MS


import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R
import qualified What4.Solver.Adapter as WSA
import qualified What4.Symbol as WS

import           What4.ExprHelpers

import qualified Pate.Arch as PA
import qualified Pate.Config as PC
import           Pate.Equivalence
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Timeout as PT
import           Pate.Types
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Parallel as Par

data BinaryContext sym arch (bin :: WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , parsedFunctionMap :: ParsedFunctionMap arch
  , binEntry :: MM.ArchSegmentOff arch
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    forall sym ids arch.
    (PA.ValidArch arch, ValidSym sym) =>
    { nonces :: N.NonceGenerator IO ids
    , handles :: CFH.HandleAllocator
    , exprBuilder :: sym
    , originalCtx :: BinaryContext sym arch Original
    , rewrittenCtx :: BinaryContext sym arch Patched
    } -> EquivalenceContext sym arch

data EquivEnv sym arch where
  EquivEnv ::
    forall sym arch .
    (PA.ValidArch arch, ValidSym sym) =>
    { envWhichBinary :: Maybe (Some WhichBinaryRepr)
    , envCtx :: EquivalenceContext sym arch
    , envArchVals :: MS.GenArchVals MT.MemTraceK arch
    , envExtensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
    , envStackRegion :: W4.SymNat sym
    , envGlobalRegion :: W4.SymNat sym
    , envPCRegion :: W4.SymNat sym
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MS.MacawBlockEndType arch)
    , envBlockMapping :: BlockMapping arch
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envConfig :: PC.VerificationConfig
    , envFailureMode :: VerificationFailureMode
    , envBaseEquiv :: EquivRelation sym arch
    , envGoalTriples :: [PF.EquivTriple sym arch]
    -- ^ input equivalence problems to solve
    , envValidSym :: Sym sym
    -- ^ expression builder, wrapped with a validity proof
    , envStartTime :: TM.UTCTime
    -- ^ start checkpoint for timed events - see 'startTimer' and 'emitEvent'
    , envTocs :: PA.HasTOCReg arch => (TOC.TOC (MM.ArchAddrWidth arch), TOC.TOC (MM.ArchAddrWidth arch))
    -- ^ table of contents for the original and patched binaries, if defined by the
    -- architecture
    , envCurrentFunc :: BlockPair arch
    -- ^ start of the function currently under analysis
    , envCurrentFrame :: AssumptionFrame sym
    -- ^ the current assumption frame, accumulated as assumptions are added
    , envNonceGenerator :: N.NonceGenerator IO (PF.ProofScope (PFI.ProofSym sym arch))
    , envParentNonce :: Some (PF.ProofNonce (PFI.ProofSym sym arch))
    -- ^ nonce of the parent proof node currently in scope
    } -> EquivEnv sym arch

freshNonce :: EquivM sym arch (N.Nonce (PF.ProofScope (PFI.ProofSym sym arch)) tp)
freshNonce = do
  gen <- asks envNonceGenerator
  liftIO $ N.freshNonce gen

withProofNonce ::
  forall tp sym arch a.
  (PF.ProofNonce (PFI.ProofSym sym arch) tp -> EquivM sym arch a) ->
  EquivM sym arch a
withProofNonce f = withValid $do
  nonce <- freshNonce
  let proofNonce = PF.ProofNonce nonce
  local (\env -> env { envParentNonce = Some proofNonce }) (f proofNonce)

data VerificationFailureMode =
    ThrowOnAnyFailure
  | ContinueAfterFailure

-- | Start the timer to be used as the initial time when computing
-- the duration in a nested 'emitEvent'
startTimer :: EquivM sym arch a -> EquivM sym arch a
startTimer f = do
  startTime <- liftIO TM.getCurrentTime
  local (\env -> env { envStartTime = startTime}) f

-- | Time since the most recent 'startTimer'
getDuration :: EquivM sym arch TM.NominalDiffTime
getDuration = do
  startedAt <- asks envStartTime
  finishedBy <- liftIO TM.getCurrentTime
  return $ TM.diffUTCTime finishedBy startedAt

emitWarning ::
  HasCallStack =>
  PE.BlocksPair arch ->
  InnerEquivalenceError arch ->
  EquivM sym arch ()
emitWarning blks innererr = do
  wb <- asks envWhichBinary
  let err = EquivalenceError
        { errWhichBinary = wb
        , errStackTrace = Just callStack
        , errEquivError = innererr
        }
  emitEvent (\_ -> PE.Warning blks err)

emitEvent :: (TM.NominalDiffTime -> PE.Event arch) -> EquivM sym arch ()
emitEvent evt = do
  duration <- getDuration
  logAction <- asks envLogger
  IO.liftIO $ LJ.writeLog logAction (evt duration)


data EquivState sym arch where
  EquivState ::
    { stProofs :: [PFI.ProofSymExpr sym arch PF.ProofBlockSliceType]
    -- ^ all intermediate triples that were proven for each block slice
    , stSimResults ::  Map (BlockPair arch) (SimSpec sym arch (SimBundle sym arch))
    -- ^ cached results of symbolic execution for a given block pair
    , stEqStats :: EquivalenceStatistics
    } -> EquivState sym arch

newtype EquivM_ sym arch a = EquivM { unEQ :: ReaderT (EquivEnv sym arch) (StateT (EquivState sym arch) ((ExceptT (EquivalenceError arch) IO))) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MonadReader (EquivEnv sym arch)
           , MonadState (EquivState sym arch)
           , MonadThrow
           , MonadCatch
           , MonadMask
           , MonadError (EquivalenceError arch)
           )

-- instance MonadError (EquivalenceError arch) (EquivM_ sym arch) where
--   throwError e = EquivM ( throwError e)
--   catchError (EquivM f) h = withValid $ do
--     sym <- asks envSym
--     asmSt <- liftIO $ CB.saveAssumptionState sym
--     EquivM $ catchError f (\e -> (liftIO $ CB.restoreAssumptionState sym asmSt) >> unEQ (h e))
  
type EquivM sym arch a = (PA.ValidArch arch, ValidSym sym) => EquivM_ sym arch a

withBinary ::
  forall bin sym arch a.
  KnownBinary bin =>
  EquivM sym arch a ->
  EquivM sym arch a
withBinary f =
  let
    repr :: WhichBinaryRepr bin = knownRepr
  in local (\env -> env { envWhichBinary = Just (Some repr) }) f

getBinCtx ::
  forall bin sym arch.
  KnownRepr WhichBinaryRepr bin => 
  EquivM sym arch (BinaryContext sym arch bin)
getBinCtx = getBinCtx' knownRepr

getBinCtx' ::
  WhichBinaryRepr bin ->
  EquivM sym arch (BinaryContext sym arch bin)
getBinCtx' repr = case repr of
  OriginalRepr -> asks (originalCtx . envCtx)
  PatchedRepr -> asks (rewrittenCtx . envCtx)

withValid :: forall a sym arch.
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, PA.ValidArch arch, ValidSym sym) => EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f

withValidEnv ::
  EquivEnv sym arch ->
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, PA.ValidArch arch, ValidSym sym) => a) ->
  a
withValidEnv (EquivEnv { envValidSym = Sym {}}) f = f

withSymSolver ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> WSA.SolverAdapter st -> EquivM sym arch a) ->
  EquivM sym arch a
withSymSolver f = withValid $ do
  Sym _ sym adapter <- asks envValidSym
  f sym adapter

withSym ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  Sym _ sym _ <- asks envValidSym
  f sym

withSymIO :: forall sym arch a.
  ( sym -> IO a ) ->
  EquivM sym arch a
withSymIO f = withSym (\sym -> liftIO (f sym))

archFuns :: forall sym arch.
  EquivM sym arch (MS.MacawSymbolicArchFunctions arch)
archFuns = do
  archVals <- asks envArchVals
  return $ MS.archFunctions archVals

-----------------------------------------------
-- State and assumption management

unconstrainedRegister ::
  forall sym arch tp.
  HasCallStack =>
  MM.ArchReg arch tp ->
  EquivM sym arch (PSR.MacawRegVar sym tp)
unconstrainedRegister reg = do
  let repr = MM.typeRepr reg
  case repr of
    MM.BVTypeRepr n -> withSymIO $ \sym -> do
      ptr@(CLM.LLVMPointer region off) <- freshPtr sym n
      iRegion <- W4.natToInteger sym region
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> iRegion Ctx.:> off)
    MM.BoolTypeRepr -> withSymIO $ \sym -> do
      var <- W4.freshConstant sym (WS.safeSymbol "boolArg") W4.BaseBoolRepr
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) var) (Ctx.empty Ctx.:> var)
    MM.TupleTypeRepr PL.Nil -> do
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) Ctx.Empty) Ctx.empty
    _ -> throwHere $ UnsupportedRegisterType (Some (MS.typeToCrucible repr))

withSimSpec ::
  PEM.ExprMappable sym f =>
  SimSpec sym arch f ->
  (SimState sym arch Original -> SimState sym arch Patched -> f -> EquivM sym arch g) ->
  EquivM sym arch (SimSpec sym arch g)
withSimSpec spec f = withSym $ \sym -> do
  withFreshVars $ \stO stP -> do
    (asm, body) <- liftIO $ bindSpec sym stO stP spec
    withAssumption (return asm) $ f stO stP body

freshSimVars ::
  forall bin sym arch.
  EquivM sym arch (SimVars sym arch bin)
freshSimVars = do
  (memtrace, memtraceVar) <- withSymIO $ \sym -> MT.initMemTraceVar sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  regs <- MM.mkRegStateM unconstrainedRegister
  return $ SimVars memtraceVar regs (SimState memtrace (MM.mapRegsWith (\_ -> PSR.macawVarEntry) regs))


withFreshVars ::
  (SimState sym arch Original -> SimState sym arch Patched -> EquivM sym arch (W4.Pred sym, f)) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshVars f = do
  varsO <- freshSimVars @Original
  varsP <- freshSimVars @Patched
  (asm, result) <- f (simVarState varsO) (simVarState varsP)
  return $ SimSpec (PatchPair varsO varsP) asm result

-- | Compute and assume the given predicate, then execute the inner function in a frame that assumes it.
-- The resulting predicate is the conjunction of the initial assumptions and
-- any produced by the given function.
withAssumption' ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch (W4.Pred sym, f) ->
  EquivM sym arch (W4.Pred sym, f)
withAssumption' asmf f = withSym $ \sym -> do
  asm <- asmf
  frame <- asks envCurrentFrame
  (asm', a) <- local (\env -> env { envCurrentFrame = frameAssume asm <> frame }) $ f
  asm'' <- liftIO $ W4.andPred sym asm asm'
  return (asm'', a)

-- | Compute and assume the given predicate, then execute the inner function in a frame that assumes it. Return the given assumption along with the function result.
withAssumption ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
withAssumption asmf f =
  withSym $ \sym -> withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

-- | Run the given function under the given assumption frame, and rebind the resulting
-- value according to any explicit bindings. The returned predicate is the conjunction of
-- the given assumption frame and the frame produced by the function.
withAssumptionFrame' ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  EquivM sym arch (AssumptionFrame sym) ->
  EquivM sym arch (AssumptionFrame sym, f) ->
  EquivM sym arch (W4.Pred sym, f)
withAssumptionFrame' asmf f = withSym $ \sym -> do
  asmFrame <- asmf
  envFrame <- asks envCurrentFrame
  local (\env -> env { envCurrentFrame = asmFrame <> envFrame }) $ do
    withAssumption' (liftIO $ getAssumedPred sym (asmFrame <> envFrame)) $ do
      (frame', a) <- f
      applyAssumptionFrame (asmFrame <> frame') a

applyCurrentFrame ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
applyCurrentFrame f = snd <$> withAssumptionFrame (asks envCurrentFrame) (return f)

applyAssumptionFrame ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  AssumptionFrame sym ->
  f ->
  EquivM sym arch (W4.Pred sym, f)
applyAssumptionFrame frame f = withSym $ \sym -> do
  cache <- W4B.newIdxCache
  let
    doRebind :: forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)
    doRebind = rebindWithFrame' sym cache frame
  f' <- liftIO $ PEM.mapExpr sym doRebind f
  p <- liftIO $ getAssumedPred sym frame
  p' <- liftIO $ PEM.mapExpr sym doRebind p
  return (p',f')

-- | Run the given function under the given assumption frame, and rebind the resulting
-- value according to any explicit bindings. The returned predicate is the conjunction
-- of all the assumptions in the given frame.
withAssumptionFrame ::
  PEM.ExprMappable sym f =>
  EquivM sym arch (AssumptionFrame sym) ->
  EquivM sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
withAssumptionFrame asmf f = withAssumptionFrame' asmf ((\a -> (mempty, a)) <$> f)

withAssumptionFrame_ ::
  PEM.ExprMappable sym f =>
  EquivM sym arch (AssumptionFrame sym) ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumptionFrame_ asmf f = fmap snd $ withAssumptionFrame asmf f

-- | Compute and assume the given predicate, then execute the inner function in a frame that assumes it.
withAssumption_ ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption_ asmf f =
  withSym $ \sym -> fmap snd $ withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

-- | First check if an assumption is satisfiable before assuming it. If it is not
-- satisfiable, return Nothing.
withSatAssumption ::
  HasCallStack =>
  PT.Timeout ->
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch (Maybe (W4.Pred sym, f))
withSatAssumption timeout asmf f = do
  asm <- asmf
  isPredSat timeout asm >>= \case
    True ->  Just <$> (withAssumption (return asm) $ f)
    False -> return Nothing

--------------------------------------
-- Sat helpers

-- | Check a predicate for satisfiability (in our monad)
--
-- FIXME: Add a facility for saving the SMT problem under the given name
checkSatisfiableWithModel ::
  PT.Timeout ->
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM sym arch a) ->
  EquivM sym arch a
checkSatisfiableWithModel timeout _desc p k = withSymSolver $ \sym adapter -> do
  envFrame <- asks envCurrentFrame
  assumptions <- liftIO $ getAssumedPred sym envFrame
  goal <- liftIO $ W4.andPred sym assumptions p

  -- Set up a wrapper around the ground evaluation function that removes some
  -- unwanted terms and performs an equivalent substitution step to remove
  -- unbound variables (consistent with the initial query)
  let mkResult r = W4R.traverseSatResult (\r' -> pure $ SymGroundEvalFn r') pure r
  runInIO1 (mkResult >=> k) $ checkSatisfiableWithoutBindings timeout sym adapter goal

checkSatisfiableWithoutBindings
  :: (sym ~ W4B.ExprBuilder t st fs)
  => PT.Timeout
  -> sym
  -> WSA.SolverAdapter st
  -> W4B.BoolExpr t
  -> (W4R.SatResult (W4G.GroundEvalFn t) () -> IO a)
  -> IO a
checkSatisfiableWithoutBindings timeout sym adapter p k =
  case PT.timeoutAsMicros timeout of
    Nothing -> doCheckSat
    Just micros -> do
      mres <- PT.timeout micros doCheckSat
      case mres of
        Nothing -> k W4R.Unknown
        Just r -> return r
  where
    doCheckSat = WSA.solver_adapter_check_sat adapter sym WSA.defaultLogData [p] $ \sr ->
      case sr of
        W4R.Unsat core -> k (W4R.Unsat core)
        W4R.Unknown -> k W4R.Unknown
        W4R.Sat (evalFn, _) -> k (W4R.Sat evalFn)

isPredSat ::
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredSat timeout p = case W4.asConstantPred p of
  Just b -> return b
  Nothing -> checkSatisfiableWithModel timeout "isPredSat" p $ \case
    W4R.Sat _ -> return True
    W4R.Unsat _ -> return False
    W4R.Unknown -> throwHere InconclusiveSAT

isPredTrue ::
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredTrue timeout p = case W4.asConstantPred p of
  Just True -> return True
  _ -> do
    frame <- asks envCurrentFrame
    case isAssumedPred frame p of
      True -> return True
      False -> do
        notp <- withSymIO $ \sym -> W4.notPred sym p
        not <$> isPredSat timeout notp

-- | Same as 'isPredTrue' but does not throw an error if the result is inconclusive
isPredTrue' ::
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredTrue' timeout p = join $ isPredTruePar' timeout p

isPredTruePar' ::
  Par.IsFuture (EquivM_ sym arch) future =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch (future Bool)
isPredTruePar' timeout p = case W4.asConstantPred p of
  Just b -> Par.present $ return b
  _ -> do
    frame <- asks envCurrentFrame
    case isAssumedPred frame p of
      True -> Par.present $ return True
      False -> Par.promise $ do
        notp <- withSymIO $ \sym -> W4.notPred sym p
        checkSatisfiableWithModel timeout "isPredTrue'" notp $ \case
            W4R.Sat _ -> return False
            W4R.Unsat _ -> return True
            W4R.Unknown -> return False


instance Par.IsFuture (EquivM_ sym arch) Par.Future where
  present m = IO.withRunInIO $ \runInIO -> Par.present (runInIO m)
  -- here we can implement scheduling of IOFutures, which can be tracked
  -- in the equivM state
  promise m = IO.withRunInIO $ \runInIO -> Par.promise (runInIO m)
  joinFuture future = withValid $ catchInIO $ Par.joinFuture future
  forFuture future f = IO.withRunInIO $ \runInIO -> Par.forFuture future (runInIO . f)

execGroundFn ::
  forall sym arch tp.
  HasCallStack =>
  SymGroundEvalFn sym  -> 
  W4.SymExpr sym tp -> 
  EquivM sym arch (W4G.GroundValue tp)  
execGroundFn gfn e = do
  groundTimeout <- asks (PC.cfgGroundTimeout . envConfig)
  result <- liftIO $ (PT.timeout' groundTimeout $ execGroundFnIO gfn e) `catches`
    [ Handler (\(ae :: ArithException) -> liftIO (putStrLn ("ArithEx: " ++ show ae)) >> return Nothing)
    , Handler (\(ie :: IOException) -> liftIO (putStrLn ("IOEx: " ++ show ie)) >> return Nothing)
    ]
  case result of
    Just a -> return a
    Nothing -> throwHere InvalidSMTModel

getFootprints ::
  SimBundle sym arch ->
  EquivM sym arch (Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)))
getFootprints bundle = withSym $ \sym -> do
  footO <- liftIO $ MT.traceFootprint sym (MT.memSeq $ simOutMem $ simOutO bundle)
  footP <- liftIO $ MT.traceFootprint sym (MT.memSeq $ simOutMem $ simOutP bundle)
  return $ S.union footO footP

memOpCondition :: MT.MemOpCondition sym -> EquivM sym arch (W4.Pred sym)
memOpCondition = \case
  MT.Unconditional -> withSymIO $ \sym -> return $ W4.truePred sym
  MT.Conditional p -> return p

--------------------------------------
-- UnliftIO

-- FIXME: state updates are not preserved
instance forall sym arch. IO.MonadUnliftIO (EquivM_ sym arch) where
  withRunInIO f = withValid $ do
    env <- ask
    st <- get
    catchInIO (f (runEquivM' env st))

catchInIO ::
  forall sym arch a.
  IO a ->
  EquivM sym arch a
catchInIO f =
  (liftIO $ catch (Right <$> f) (\(e :: EquivalenceError arch) -> return $ Left e)) >>= \case
    Left err -> throwError err
    Right result -> return result

runInIO1 ::
  IO.MonadUnliftIO m =>
  (a -> m b) ->
  ((a -> IO b) -> IO b) ->
  m b
runInIO1 f g = IO.withRunInIO $ \runInIO -> g (\a -> runInIO (f a))


----------------------------------------
-- Running

runEquivM' ::
  EquivEnv sym arch ->
  EquivState sym arch ->
  EquivM sym arch a ->
  IO a
runEquivM' env st f = withValidEnv env $ (runExceptT $ evalStateT (runReaderT (unEQ f) env) st) >>= \case
  Left err -> throwIO err
  Right result -> return $ result

runEquivM ::
  EquivEnv sym arch ->
  EquivState sym arch ->
  EquivM sym arch a ->
  ExceptT (EquivalenceError arch) IO a
runEquivM env st f = withValidEnv env $ evalStateT (runReaderT (unEQ f) env) st

----------------------------------------
-- Errors

throwHere ::
  HasCallStack =>
  InnerEquivalenceError arch ->
  EquivM_ sym arch a
throwHere err = withValid $ do
  wb <- asks envWhichBinary
  throwError $ EquivalenceError
    { errWhichBinary = wb
    , errStackTrace = Just callStack
    , errEquivError = err
    }


instance MF.MonadFail (EquivM_ sym arch) where
  fail msg = throwHere $ EquivCheckFailure $ "Fail: " ++ msg

manifestError :: MonadError e m => m a -> m (Either e a)
manifestError act = catchError (Right <$> act) (pure . Left)

implicitError :: MonadError e m => Either e a -> m a
implicitError (Left e) = throwError e
implicitError (Right a) = pure a

----------------------------------------
-- Proof instances

instance PF.IsBoolLike (PFI.ProofSym sym arch) (EquivM_ sym arch) where
  proofPredAnd p1 p2 = withValid $ withSymIO $ \sym -> W4.andPred sym p1 p2
  proofPredOr p1 p2 = withValid $ withSymIO $ \sym -> W4.orPred sym p1 p2
  proofPredEq p1 p2 = withValid $ withSymIO $ \sym -> W4.isEq sym p1 p2
  proofPredTrue = withValid $ withSym $ \sym -> return $ W4.truePred sym
  proofPredFalse = withValid $ withSym $ \sym -> return $ W4.falsePred sym
  proofPredAssertEqual p1 p2 = withValid $ case p1 == p2 of
    True -> return ()
    False -> throwHere $ IncompatibleDomainPolarities
