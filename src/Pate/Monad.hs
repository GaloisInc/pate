{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
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

module Pate.Monad
  ( EquivEnv(..)
  , EquivState(..)
  , EquivM
  , EquivM_
  , runEquivM
  , ValidSym
  , ValidArch(..)
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
  -- working under a 'SimSpec' context
  , withSimSpec
  , withFreshVars
  -- assumption management
  , withAssumption_
  , withAssumption
  , withSatAssumption
  , withAssumptionFrame
  , withAssumptionFrame'
  )
  where

import           GHC.Stack ( HasCallStack, callStack )

import qualified Control.Monad.Fail as MF
import qualified Control.Monad.IO.Unlift as IO
import           Control.Exception hiding ( try )
import           Control.Monad.Catch hiding ( catch, catches, Handler )
import           Control.Monad.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Except
import           Control.Monad.State


import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Time as TM
import           Data.Typeable

import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Lumberjack as LJ

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MM
import qualified Data.Macaw.Symbolic as MS


import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R
import qualified What4.SemiRing as SR
import qualified What4.Solver.Adapter as WSA
import qualified What4.Symbol as WS

import           What4.ExprHelpers

import           Pate.Equivalence
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import           Pate.Types
import qualified Pate.Proof as PP

data BinaryContext sym arch (bin :: WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , parsedFunctionMap :: ParsedFunctionMap arch
  , binEntry :: MM.ArchSegmentOff arch
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    forall sym ids arch.
    (ValidArch arch, ValidSym sym) =>
    { nonces :: N.NonceGenerator IO ids
    , handles :: CFH.HandleAllocator
    , exprBuilder :: sym
    , originalCtx :: BinaryContext sym arch Original
    , rewrittenCtx :: BinaryContext sym arch Patched
    } -> EquivalenceContext sym arch

data EquivEnv sym arch where
  EquivEnv ::
    forall sym arch .
    (ValidArch arch, ValidSym sym) =>
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
    , envConfig :: VerificationConfig
    , envFailureMode :: VerificationFailureMode
    , envBaseEquiv :: EquivRelation sym arch
    , envGoalTriples :: [PP.EquivTriple sym arch]
    -- ^ input equivalence problems to solve
    , envValidSym :: Sym sym
    -- ^ expression builder, wrapped with a validity proof
    , envStartTime :: TM.UTCTime
    -- ^ start checkpoint for timed events - see 'startTimer' and 'emitEvent'
    , envTocs :: HasTOCReg arch => (TOC.TOC (MM.ArchAddrWidth arch), TOC.TOC (MM.ArchAddrWidth arch))
    -- ^ table of contents for the original and patched binaries, if defined by the
    -- architecture
    , envCurrentFunc :: PatchPair arch
    -- ^ start of the function currently under analysis
    , envCurrentAsm :: W4.Pred sym
    -- ^ conjunction of all assumptions currently in scope
    , envCurrentVars :: [Some (W4.BoundVar sym)]
    -- ^ The variables currently introduced by a call to 'withFreshVars' that
    -- *must* be bound before an SMT query is issued (because we cannot pass
    -- unbound variables to the solver).  These will be concretized to arbitrary
    -- values when invoking the SMT solver.
    } -> EquivEnv sym arch

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
    { stProofs :: [PP.ProofBlockSlice sym arch]
    -- ^ all intermediate triples that were proven for each block slice
    , stSimResults ::  Map (PatchPair arch) (SimSpec sym arch (SimBundle sym arch))
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
  
type EquivM sym arch a = (ValidArch arch, ValidSym sym) => EquivM_ sym arch a

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
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, ValidArch arch, ValidSym sym) => EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f



withValidEnv ::
  EquivEnv sym arch ->
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, ValidArch arch, ValidSym sym) => a) ->
  a
withValidEnv (EquivEnv { envValidSym = Sym {}}) f = f

withSymSolver ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> WSA.SolverAdapter st -> EquivM sym arch a) ->
  EquivM sym arch a
withSymSolver f = withValid $ do
  Sym sym adapter <- asks envValidSym
  f sym adapter

withSym ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  Sym sym _ <- asks envValidSym
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
  archFs <- archFuns
  let
    symbol = MS.crucGenArchRegName archFs reg
    repr = MM.typeRepr reg
  case repr of
    MM.BVTypeRepr n -> withSymIO $ \sym -> do
      (ptr, regVar, offVar) <- freshPtrVar sym n symbol
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> regVar Ctx.:> offVar)
    MM.BoolTypeRepr -> withSymIO $ \sym -> do
      var <- W4.freshBoundVar sym (WS.safeSymbol "boolArg") W4.BaseBoolRepr
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) (W4.varExpr sym var)) (Ctx.empty Ctx.:> var)
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
  withSimVars varsO varsP $ do
    (asm, result) <- f (simVarState varsO) (simVarState varsP)
    return $ SimSpec varsO varsP asm result

-- | Add an assumption that the given variable is in fact a natural if its declared type is Nat
--
-- This is required because what4 does not correctly manage all of the axioms
-- necessary for natural numbers.  Naturals are not an SMT type, so what4
-- emulates them by emitting axioms (sometimes).  To solvers, they are just
-- Integers.  If they generate a negative counterexample, the ground term
-- evaluator will throw an error.  To work around that, we assume (in our local
-- frame) that these variables are in fact positive.
initVar :: W4.BoundVar sym tp -> EquivM sym arch ()
initVar bv = withSym $ \sym -> case W4.exprType (W4.varExpr sym bv) of
  W4.BaseNatRepr -> withValid $ do
    let e = W4.varExpr sym bv
    zero <- liftIO $ W4.natLit sym 0
    isPos <- liftIO $ W4B.sbMakeExpr sym $ W4B.SemiRingLe SR.OrderedSemiRingNatRepr zero e
    addAssumption isPos "natural numbers are positive"
  _ -> return ()

withSimVars ::
  SimVars sym arch Original ->
  SimVars sym arch Patched ->
  EquivM sym arch a ->
  EquivM sym arch a
withSimVars varsO varsP f = withSym $ \sym -> do
  let vars = flatVars varsO ++ flatVars varsP
  local (\env -> env { envCurrentVars = vars ++ envCurrentVars env }) $ do
    fr <- liftIO $ CB.pushAssumptionFrame sym
    mapM_ (\(Some var) -> initVar var) vars
    a <- manifestError f
    _ <- liftIO $ CB.popAssumptionFrame sym fr
    implicitError a

addAssumption ::
  HasCallStack =>
  W4.Pred sym ->
  String ->
  EquivM sym arch ()
addAssumption p msg = withSym $ \sym -> do
  here <- liftIO $ W4.getCurrentProgramLoc sym
  (liftIO $ try (CB.addAssumption sym (CB.LabeledPred p (CB.AssumptionReason here msg)))) >>= \case
    Left (reason :: CB.AbortExecReason) -> do
      liftIO $ putStrLn $ "Invalid SMT model:" ++ show reason
      throwHere $ InvalidSMTModel
    Right _ -> return ()

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
  envAsms <- asks envCurrentAsm
  allAsms <- liftIO $ W4.andPred sym asm envAsms
  fr <- liftIO $ CB.pushAssumptionFrame sym
  result <- local (\env -> env { envCurrentAsm = allAsms }) $ manifestError $ do
    addAssumption asm "withAssumption"
    f
  _ <- liftIO $ CB.popAssumptionFrame sym fr
  case result of
    Left err -> throwError err
    Right (asm', a) -> do
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
withAssumptionFrame' asmf f = withValid $ withSym $ \sym -> do
  asm <- asmf
  asm_pred <- liftIO $ getAssumedPred sym asm
  withAssumption' (return asm_pred) $ do
    (asm', a) <- f
    cache <- W4B.newIdxCache
    let
      doRebind :: forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)
      doRebind = rebindWithFrame' sym cache (asm <> asm')
    a' <- liftIO $ PEM.mapExpr sym doRebind a
    asm_pred' <- liftIO $ getAssumedPred sym asm'
    return (asm_pred', a')

-- | Run the given function under the given assumption frame, and rebind the resulting
-- value according to any explicit bindings. The returned predicate is the conjunction
-- of all the assumptions in the given frame.
withAssumptionFrame ::
  PEM.ExprMappable sym f =>
  EquivM sym arch (AssumptionFrame sym) ->
  EquivM sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
withAssumptionFrame asmf f = withAssumptionFrame' asmf ((\a -> (mempty, a)) <$> f)

-- | Compute and assume the given predicate, then execute the inner function in a frame that assumes it.
withAssumption_ ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption_ asmf f =
  withSym $ \sym -> fmap snd $ withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

-- | First check if an assumption is satisfiable before assuming it. If it is not
-- satisfiable, return the given default value under the "false" assumption.
withSatAssumption ::
  HasCallStack =>
  f ->
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
withSatAssumption default_ asmf f = withSym $ \sym -> do
  asm <- asmf
  isPredSat asm >>= \case
    True ->  withAssumption (return asm) $ f
    False -> return (W4.falsePred sym, default_)

--------------------------------------
-- Sat helpers

-- | Check a predicate for satisfiability (in our monad)
--
-- FIXME: Add a facility for saving the SMT problem under the given name
checkSatisfiableWithModel ::
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM sym arch a) ->
  EquivM sym arch a
checkSatisfiableWithModel _desc p k = withSymSolver $ \sym adapter -> do
  -- Bind all of our introduced variables in this scope to defaults
  unboundVars <- asks envCurrentVars
  bindings <- F.foldrM (addSingletonBinding sym) MapF.empty unboundVars
  let frame = AssumptionFrame { asmPreds = []
                              , asmBinds = bindings
                              }
  p' <- liftIO $ rebindWithFrame sym frame p
  let mkResult r = W4R.traverseSatResult (\r' -> SymGroundEvalFn <$> (liftIO $ mkSafeAsserts sym r')) pure r
  runInIO1 (mkResult >=> k) $ checkSatisfiableWithoutBindings sym adapter p'
  where
    addSingletonBinding sym (Some boundVar) m = do
      fresh <- liftIO $ W4.freshConstant sym (WS.safeSymbol "freeVar") (W4.exprType (W4.varExpr sym boundVar))
      return (MapF.insert (W4.varExpr sym boundVar) (singletonExpr fresh) m)

checkSatisfiableWithoutBindings
  :: W4B.ExprBuilder t st fs
  -> WSA.SolverAdapter st
  -> W4B.BoolExpr t
  -> (W4R.SatResult (W4G.GroundEvalFn t) () -> IO a)
  -> IO a
checkSatisfiableWithoutBindings sym adapter p k = do
  WSA.solver_adapter_check_sat adapter sym WSA.defaultLogData [p] $ \sr ->
    case sr of
      W4R.Unsat core -> k (W4R.Unsat core)
      W4R.Unknown -> k W4R.Unknown
      W4R.Sat (evalFn, _) -> k (W4R.Sat evalFn)

isPredSat ::
  W4.Pred sym ->
  EquivM sym arch Bool
isPredSat p = case W4.asConstantPred p of
  Just b -> return b
  Nothing -> checkSatisfiableWithModel "isPredSat" p $ \case
    W4R.Sat _ -> return True
    W4R.Unsat _ -> return False
    W4R.Unknown -> throwHere InconclusiveSAT

isPredTrue ::
  W4.Pred sym ->
  EquivM sym arch Bool
isPredTrue p = case W4.asConstantPred p of
  Just True -> return True
  _ -> do
    notp <- withSymIO $ \sym -> W4.notPred sym p
    not <$> isPredSat notp

-- | Same as 'isPredTrue' but does not throw an error if the result is inconclusive
isPredTrue' ::
  W4.Pred sym ->
  EquivM sym arch Bool
isPredTrue' p = case W4.asConstantPred p of
  Just b -> return b
  _ -> do
    notp <- withSymIO $ \sym -> W4.notPred sym p
    checkSatisfiableWithModel "isPredTrue'" notp $ \case
        W4R.Sat _ -> return False
        W4R.Unsat _ -> return True
        W4R.Unknown -> return False

execGroundFn ::
  forall sym arch tp.
  HasCallStack =>
  SymGroundEvalFn sym  -> 
  W4.SymExpr sym tp -> 
  EquivM sym arch (W4G.GroundValue tp)  
execGroundFn gfn e = do  
  result <- liftIO $ (Just <$> execGroundFnIO gfn e) `catches`
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
