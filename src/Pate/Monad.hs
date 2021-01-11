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
  , SimBundle(..)
  , PrePostMap
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
  , emitEvent
  , getBinCtx
  , freshRegEntry
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

class
  ( Typeable arch
  , MBL.BinaryLoader arch (E.ElfHeaderInfo (MM.ArchAddrWidth arch))
  , MS.SymArchConstraints arch
  , MS.GenArchInfo MT.MemTraceK arch
  , MM.ArchConstraints arch
  ) => ValidArch arch where
  toc_reg :: Maybe (MM.ArchReg arch (MM.BVType (MM.RegAddrWidth (MM.ArchReg arch))))
  -- ^ FIXME: the table of contents register on PPC. Required in order to assert that it is stable
  -- at the top-level.


type ValidSym sym =
  ( W4.IsExprBuilder sym
  , CB.IsSymInterface sym
  , ShowF (W4.SymExpr sym)
  )

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
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MS.MacawBlockEndType arch)
    , envBlockMapping :: BlockMapping arch
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envDiscoveryCfg :: DiscoveryConfig
    , envPrecondProp :: PreconditionPropagation
    , envBaseEquiv :: EquivRelation sym arch
    } -> EquivEnv sym arch

data PreconditionPropagation =
    PropagateExactEquality
  | PropagateComputedDomains

emitEvent :: PE.Event arch -> EquivM sym arch ()
emitEvent evt = do
  logAction <- asks envLogger
  IO.liftIO $ LJ.writeLog logAction evt



data EquivState sym arch where
  EquivState ::
    {
   
      stOpenTriples :: PrePostMap sym arch
    , stProvenTriples :: PrePostMap sym arch
    , stFailedTriples :: PrePostMap sym arch
    -- ^ proven function equivalence pre and postconditions
    , stSimResults ::  Map (PatchPair arch) (SimSpec sym arch (SimBundle sym arch))
    
    } -> EquivState sym arch

type PrePostMap sym arch = Map (PatchPair arch) [(StatePredSpec sym arch, StatePredSpec sym arch)]

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

freshRegEntry ::
  MacawRegEntry sym tp ->
  EquivM sym arch (MacawRegEntry sym tp)
freshRegEntry entry = withSym $ \sym -> case macawRegRepr entry of
  CLM.LLVMPointerRepr w -> liftIO $ do
    ptr <- freshPtr sym w
    return $ MacawRegEntry (macawRegRepr entry) ptr
  repr -> throwHere $ UnsupportedRegisterType $ Some repr

withSimSpec ::
  ExprMappable sym f =>
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
    Left (_ :: CB.AbortExecReason) -> throwHere $ InvalidSMTModel
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
  fr <- liftIO $ CB.pushAssumptionFrame sym
  addAssumption asm "withAssumption"
  result <- manifestError f
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
