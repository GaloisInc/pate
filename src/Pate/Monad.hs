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
  , ValidSolver
  , ValidArch(..)
  , EquivalenceContext(..)
  , BinaryContext(..)
  , PreconditionPropagation(..)
  , VerificationFailureMode(..)
  , ProofEmitMode(..)
  , SimBundle(..)
  , ExprMappableEquiv(..)
  , FromExprMappable(..)
  , FromSpecExprMappable(..)
  , bindSpecEq
  , withBinary
  , withValid
  , withValidEnv
  , withSymIO
  , withSym
  , withProc
  , archFuns
  , runInIO1
  , manifestError
  , implicitError
  , throwHere
  , getDuration
  , startTimer
  , emitEvent
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
  , withAssumption'
  , withSatAssumption
  )
  where

import           Prelude hiding ( fail )
import           GHC.Stack

import           Control.Monad.Fail
import qualified Control.Monad.IO.Unlift as IO
import           Control.Exception hiding ( try )
import           Control.Monad.Catch hiding ( catch, catches, Handler )
import           Control.Monad.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Except
import           Control.Monad.State


import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Typeable
import qualified Data.ElfEdit as E
import qualified Data.Time as TM

import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some

import qualified Lumberjack as LJ

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.FunctionHandle as CFH

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Types as MM
import qualified Data.Macaw.Symbolic as MS


import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Protocol.Online as W4O
import qualified What4.Protocol.SMTWriter as W4W
import qualified What4.SemiRing as SR
import qualified What4.SatResult as W4R
import qualified What4.Expr.GroundEval as W4G

import           What4.ExprHelpers

import qualified Pate.Event as PE
import           Pate.Types
import           Pate.SimState
import qualified Pate.Memory.MemTrace as MT
import           Pate.Equivalence
import qualified Pate.Proof as PP

data BinaryContext sym arch (bin :: WhichBinary) = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , parsedFunctionMap :: ParsedFunctionMap arch
  , binEntry :: MM.ArchSegmentOff arch
  }

data EquivalenceContext sym arch where
  EquivalenceContext ::
    forall sym ids arch scope solver fs.
    (ValidArch arch, ValidSym sym, ValidSolver sym scope solver fs) =>
    { nonces :: N.NonceGenerator IO ids
    , handles :: CFH.HandleAllocator
    , exprBuilder :: sym
    , originalCtx :: BinaryContext sym arch Original
    , rewrittenCtx :: BinaryContext sym arch Patched
    } -> EquivalenceContext sym arch

type ValidSolver sym scope solver fs =
  (sym ~ CBO.OnlineBackend scope solver fs
  , W4O.OnlineSolver solver
  , W4W.SMTReadWriter solver
  )

data EquivEnv sym arch where
  EquivEnv ::
    forall sym arch scope solver fs.
    (ValidArch arch, ValidSym sym, ValidSolver sym scope solver fs) =>
    { envSym :: sym
    , envWhichBinary :: Maybe (Some WhichBinaryRepr)
    , envProc :: W4O.SolverProcess scope solver
    , envCtx :: EquivalenceContext sym arch
    , envArchVals :: MS.GenArchVals MT.MemTraceK arch
    , envExtensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
    , envStackRegion :: W4.SymNat sym
    , envGlobalRegion :: W4.SymNat sym
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MS.MacawBlockEndType arch)
    , envBlockMapping :: BlockMapping arch
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envDiscoveryCfg :: DiscoveryConfig
    , envPrecondProp :: PreconditionPropagation
    , envFailureMode :: VerificationFailureMode
    , envProofEmitMode :: ProofEmitMode
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
    } -> EquivEnv sym arch



data PreconditionPropagation =
    PropagateExactEquality
  | PropagateComputedDomains

data VerificationFailureMode =
    ThrowOnAnyFailure
  | ContinueAfterFailure

data ProofEmitMode =
    ProofEmitAll
  | ProofEmitNone

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
  (forall scope solver fs.
    ValidSolver sym scope solver fs =>
    EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f



withValidEnv ::
  EquivEnv sym arch ->
  (forall scope solver fs.
    ValidArch arch =>
    ValidSym sym =>
    ValidSolver sym scope solver fs =>
    a) ->
  a
withValidEnv (EquivEnv {}) f = f

withSym ::
  (sym -> EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  sym <- asks envSym
  f sym

withProc ::
  forall a sym arch.
  ( forall scope solver fs.
    ValidSolver sym scope solver fs =>
    W4O.SolverProcess scope solver ->
   EquivM sym arch a) ->
  EquivM sym arch a
withProc f = withValid $ do
  EquivEnv { envProc = p } <- ask
  f p

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
  MM.ArchReg arch tp ->
  EquivM sym arch (MacawRegVar sym tp)
unconstrainedRegister reg = do
  archFs <- archFuns
  let
    symbol = MS.crucGenArchRegName archFs reg
    repr = MM.typeRepr reg
  case repr of
    MM.BVTypeRepr n -> withSymIO $ \sym -> do
      (ptr, regVar, offVar) <- freshPtrVar sym n symbol
      return $ MacawRegVar (MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> regVar Ctx.:> offVar)
    _ -> throwHere $ UnsupportedRegisterType (Some (MS.typeToCrucible repr))

withSimSpec ::
  ExprMappableEquiv sym arch f =>
  SimSpec sym arch f ->
  (SimState sym arch Original -> SimState sym arch Patched -> f -> EquivM sym arch g) ->
  EquivM sym arch (SimSpec sym arch g)
withSimSpec spec f = do
  withFreshVars $ \stO stP -> do
    (asm, body) <- bindSpecEq stO stP spec
    withAssumption (return asm) $ f stO stP body

freshSimVars ::
  forall bin sym arch.
  EquivM sym arch (SimVars sym arch bin)
freshSimVars = do
  (memtrace, memtraceVar) <- withSymIO $ \sym -> MT.initMemTraceVar sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  regs <- MM.mkRegStateM unconstrainedRegister
  return $ SimVars memtraceVar regs (SimState memtrace (MM.mapRegsWith (\_ -> macawVarEntry) regs))


withFreshVars ::
  (SimState sym arch Original -> SimState sym arch Patched -> EquivM sym arch (W4.Pred sym, f)) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshVars f = do
  varsO <- freshSimVars @Original
  varsP <- freshSimVars @Patched
  withSimVars varsO varsP $ do
    (asm, result) <- f (simVarState varsO) (simVarState varsP)
    return $ SimSpec varsO varsP asm result

-- FIXME: what4 bug fails to correctly emit axioms for Natural numbers for bound variables
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
withSimVars varsO varsP f = withProc $ \proc -> withSym $ \sym -> do
  let
    flatO = flatVars varsO
    flatP = flatVars varsP
    vars = flatO ++ flatP

  fr <- liftIO $ CB.pushAssumptionFrame sym
  a <- W4O.inNewFrameWithVars proc vars $ do
    mapM_ (\(Some var) -> initVar var) vars
    manifestError $ f
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

-- | Compute and assume the given predicate, then execute the inner function in a frame that assumes it.
withAssumption_ ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption_ asmf f =
  fmap snd $ withSym $ \sym -> withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

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

checkSatisfiableWithModel ::
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM sym arch a) ->
  EquivM sym arch a
checkSatisfiableWithModel desc p k = withSym $ \sym -> withProc $ \proc -> do
  let mkResult r = W4R.traverseSatResult (\r' -> SymGroundEvalFn <$> (liftIO $ mkSafeAsserts sym r')) pure r
  runInIO1 (mkResult >=> k) $ W4O.checkSatisfiableWithModel proc desc p

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
    [ Handler (\(_ :: ArithException) -> return Nothing)
    , Handler (\(_ :: IOException) -> return Nothing)
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


-- | Mapping under a 'SimSpec' requires re-establishing the correct logical context, which
-- currently is best supported in the 'EquivM' monad, so we specialize 'ExprMappable' to
-- it here.
class ExprMappableEquiv sym arch f where
  mapExprEq ::
    (forall tp. W4.SymExpr sym tp -> EquivM_ sym arch (W4.SymExpr sym tp)) ->
    f ->
    EquivM_ sym arch f

bindSpecEq ::
  ExprMappableEquiv sym arch f =>
  SimState sym arch Original ->
  SimState sym arch Patched ->
  SimSpec sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
bindSpecEq stO stP spec = withSym $ \sym -> do
  ul <- IO.askUnliftIO
  (asm, TM _ body) <- liftIO $ bindSpec sym stO stP (spec { specBody = TM ul (specBody spec) })
  return (asm, body)

instance ExprMappableEquiv sym arch f => ExprMappableEquiv sym arch (SimSpec sym arch f) where
  mapExprEq f spec = withValid $ withFreshVars $ \stO stP -> do
    (asm, body) <- bindSpecEq stO stP spec
    asm' <- f asm
    withAssumption (return asm') $ mapExprEq f body

data FromExprMappable sym f where
  EM :: ExprMappable sym f => { unEM :: f } -> FromExprMappable sym f

data FromSpecExprMappable sym arch f where
  SEM :: forall sym arch f. ExprMappable sym f => SimSpec sym arch f -> FromSpecExprMappable sym arch f

data ToExprMappable sym arch f where
  TM :: ExprMappableEquiv sym arch f =>
    IO.UnliftIO (EquivM_ sym arch) -> f -> ToExprMappable sym arch f

instance ExprMappableEquiv sym arch (FromExprMappable sym f) where
  mapExprEq f (EM x) = withValid $ do
    x' <- withSym $ \sym -> IO.withRunInIO $ \runInIO ->  mapExpr sym (\e -> runInIO (f e)) x
    return $ EM x'

instance ExprMappableEquiv sym arch (FromSpecExprMappable sym arch f) where
  mapExprEq f (SEM x) = withValid $ do
    x' <- mapExprEq f (specMap (EM @sym) x)
    return $ SEM (specMap unEM x')

instance ExprMappable sym (ToExprMappable sym arch f) where
  mapExpr _ f (TM ul@(IO.UnliftIO runInIO) x) = do
    x' <- runInIO $ mapExprEq (\e -> liftIO (f e)) x
    return $ TM ul x'

instance ExprMappableEquiv sym arch (SimBundle sym arch) where
  mapExprEq f bundle = unEM <$> mapExprEq f (EM @sym bundle)

instance ExprMappableEquiv sym arch (PP.EquivTripleBody sym arch) where
  mapExprEq f triple = do
    EM eqPreDomain' <- mapExprEq f (EM @sym (PP.eqPreDomain triple))
    SEM eqPostDomain' <- mapExprEq f (SEM @sym @arch (PP.eqPostDomain triple))
    return $ PP.EquivTripleBody (PP.eqPair triple) eqPreDomain' eqPostDomain' (PP.eqStatus triple) (PP.eqValidSym triple)

instance ExprMappableEquiv sym arch (PP.ProofFunctionCall sym arch) where
  mapExprEq f prf = do
    prfFunPre' <- mapExprEq f (PP.prfFunPre prf)
    prfFunCont' <- mapExprEq f (PP.prfFunCont prf)
    case prf of
      PP.ProofFunctionCall{} -> do
        prfFunBody' <- mapExprEq f (PP.prfFunBody prf)
        return $ PP.ProofFunctionCall prfFunPre' prfFunBody' prfFunCont'
      PP.ProofTailCall{} -> return $ PP.ProofTailCall prfFunPre' prfFunCont'

instance ExprMappableEquiv sym arch (PP.ProofBlockSliceBody sym arch) where
  mapExprEq f prf = do
    prfTriple' <- mapExprEq f (PP.prfTriple prf)
    prfFunCalls' <- mapM (mapExprEq f) (PP.prfFunCalls prf)
    prfReturn' <- mapM (mapExprEq f) (PP.prfReturn prf)
    prfUnknownExit' <- mapM (mapExprEq f) (PP.prfUnknownExit prf)
    prfArchExit' <- mapM (mapExprEq f) (PP.prfArchExit prf)
    return $ PP.ProofBlockSliceBody prfTriple' prfFunCalls' prfReturn' prfUnknownExit' prfArchExit'

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
throwHere err = do
  wb <- asks envWhichBinary
  throwError $ EquivalenceError
    { errWhichBinary = wb
    , errStackTrace = Just callStack
    , errEquivError = err
    }


instance MonadFail (EquivM_ sym arch) where
  fail msg = throwHere $ EquivCheckFailure $ "Fail: " ++ msg

manifestError :: MonadError e m => m a -> m (Either e a)
manifestError act = catchError (Right <$> act) (pure . Left)

implicitError :: MonadError e m => Either e a -> m a
implicitError (Left e) = throwError e
implicitError (Right a) = pure a
