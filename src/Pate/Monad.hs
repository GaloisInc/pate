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

module Pate.Monad
  ( EquivEnv(..)
  , EquivM
  , EquivM_
  , runEquivM
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
  , ifConfig
  , traceBundle
  , traceBlockPair
  , SymGroundEvalFn
  , execGroundFn
  , withGroundEvalFn
  , getFootprints
  , memOpCondition
  -- sat helpers
  , checkSatisfiableWithModel
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
  , withEmptyAssumptionFrame
  , applyAssumptionFrame
  , applyCurrentFrame
  -- nonces
  , freshNonce
  , withProofNonce
  -- caching
  , BlockCache
  , lookupBlockCache
  , modifyBlockCache
  , freshBlockCache
  )
  where

import           GHC.Stack ( HasCallStack, callStack )

import qualified Control.Monad.Fail as MF
import qualified System.IO as IO
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Concurrent as IO
import           Control.Exception hiding ( try )
import           Control.Monad.Catch hiding ( catch, catches, tryJust, Handler )
import           Control.Monad.Reader
import           Control.Monad.Except

import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Time as TM
import           Data.Typeable

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Lumberjack as LJ

import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MM

import           What4.Utils.Process (filterAsync)
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R
import qualified What4.Solver.Adapter as WSA
import qualified What4.Symbol as WS

import           What4.ExprHelpers

import qualified Pate.Arch as PA
import qualified Pate.Block as PB
import qualified Pate.Binary as PBi
import qualified Pate.Config as PC
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Monad.Context as PMC
import           Pate.Monad.Environment as PME
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo
import qualified Pate.Timeout as PT

lookupBlockCache ::
  (EquivEnv sym arch -> BlockCache arch a) ->
  PPa.BlockPair arch ->
  EquivM sym arch (Maybe a)
lookupBlockCache f pPair = do
  BlockCache cache <- asks f
  cache' <- liftIO $ IO.readMVar cache
  case M.lookup pPair cache' of
    Just r -> return $ Just r
    Nothing -> return Nothing

modifyBlockCache ::
  (EquivEnv sym arch -> BlockCache arch a) ->
  PPa.BlockPair arch ->
  (a -> a -> a) ->
  a ->
  EquivM sym arch ()
modifyBlockCache f pPair merge val = do
  BlockCache cache <- asks f
  liftIO $ IO.modifyMVar_ cache
    (\m -> return $ M.insertWith merge pPair val m)  

-- | Execute actions if the given configuration flag is set (not set)
--
-- If the flag is set in the environment, execute the first action. Otherwise,
-- execute the second.
ifConfig ::
  (PC.VerificationConfig -> Bool) ->
  EquivM sym arch a ->
  EquivM sym arch a ->
  EquivM sym arch a
ifConfig checkCfg ifT ifF = (asks $ checkCfg . envConfig) >>= \case
  True -> ifT
  False -> ifF

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
  PEE.InnerEquivalenceError arch ->
  EquivM sym arch ()
emitWarning blks innererr = do
  wb <- asks envWhichBinary
  let err = PEE.EquivalenceError
        { PEE.errWhichBinary = wb
        , PEE.errStackTrace = Just callStack
        , PEE.errEquivError = innererr
        }
  emitEvent (\_ -> PE.Warning blks err)

emitEvent :: (TM.NominalDiffTime -> PE.Event arch) -> EquivM sym arch ()
emitEvent evt = do
  duration <- getDuration
  logAction <- asks envLogger
  IO.liftIO $ LJ.writeLog logAction (evt duration)

newtype EquivM_ sym arch a = EquivM { unEQ :: ReaderT (EquivEnv sym arch) (ExceptT (PEE.EquivalenceError arch) IO) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MonadReader (EquivEnv sym arch)
           , MonadThrow
           , MonadCatch
           , MonadMask
           , MonadError (PEE.EquivalenceError arch)
           )

type EquivM sym arch a = (PA.ValidArch arch, PSo.ValidSym sym) => EquivM_ sym arch a

withBinary ::
  forall bin sym arch a.
  PBi.KnownBinary bin =>
  EquivM sym arch a ->
  EquivM sym arch a
withBinary f =
  let
    repr :: PBi.WhichBinaryRepr bin = knownRepr
  in local (\env -> env { envWhichBinary = Just (Some repr) }) f

getBinCtx ::
  forall bin sym arch.
  KnownRepr PBi.WhichBinaryRepr bin =>
  EquivM sym arch (PMC.BinaryContext sym arch bin)
getBinCtx = getBinCtx' knownRepr

getBinCtx' ::
  PBi.WhichBinaryRepr bin ->
  EquivM sym arch (PMC.BinaryContext sym arch bin)
getBinCtx' repr = case repr of
  PBi.OriginalRepr -> asks (PMC.originalCtx . envCtx)
  PBi.PatchedRepr -> asks (PMC.rewrittenCtx . envCtx)

withValid :: forall a sym arch.
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, PA.ValidArch arch, PSo.ValidSym sym) => EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f

withValidEnv ::
  EquivEnv sym arch ->
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs, PA.ValidArch arch, PSo.ValidSym sym) => a) ->
  a
withValidEnv (EquivEnv { envValidSym = PSo.Sym {}, envValidArch = PA.SomeValidArch {}}) f = f

withSymSolver ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> WSA.SolverAdapter st -> EquivM sym arch a) ->
  EquivM sym arch a
withSymSolver f = withValid $ do
  PSo.Sym _ sym adapter <- asks envValidSym
  f sym adapter

withSym ::
  (forall t st fs . (sym ~ W4B.ExprBuilder t st fs) => sym -> EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  PSo.Sym _ sym _ <- asks envValidSym
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
  (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  MM.ArchReg arch tp ->
  EquivM sym arch (PSR.MacawRegVar sym tp)
unconstrainedRegister reg = do
  let repr = MM.typeRepr reg
  case repr of
    MM.BVTypeRepr n
      | Just Refl <- testEquality n (MM.memWidthNatRepr @(MM.ArchAddrWidth arch)) -> withSymIO $ \sym -> do
          ptr@(CLM.LLVMPointer region off) <- freshPtr sym (showF reg) n
          iRegion <- W4.natToInteger sym region
          return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> iRegion Ctx.:> off)
      | otherwise -> withSymIO $ \sym -> do
          -- For bitvector types that are not pointer width, fix their region number to 0 since they cannot be pointers
          bits <- W4.freshConstant sym (WS.safeSymbol (showF reg)) (W4.BaseBVRepr n)
          ptr <- CLM.llvmPointer_bv sym bits
          zero <- W4.intLit sym 0
          return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> zero Ctx.:> bits)
    MM.BoolTypeRepr -> withSymIO $ \sym -> do
      var <- W4.freshConstant sym (WS.safeSymbol "boolArg") W4.BaseBoolRepr
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) var) (Ctx.empty Ctx.:> var)
    MM.TupleTypeRepr PL.Nil -> do
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) Ctx.Empty) Ctx.empty
    _ -> throwHere $ PEE.UnsupportedRegisterType (Some (MS.typeToCrucible repr))

withSimSpec ::
  PEM.ExprMappable sym f =>
  SimSpec sym arch f ->
  (SimState sym arch PBi.Original -> SimState sym arch PBi.Patched -> f -> EquivM sym arch g) ->
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
  (SimState sym arch PBi.Original -> SimState sym arch PBi.Patched -> EquivM sym arch (W4.Pred sym, f)) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshVars f = do
  varsO <- freshSimVars @PBi.Original
  varsP <- freshSimVars @PBi.Patched
  (asm, result) <- f (simVarState varsO) (simVarState varsP)
  return $ SimSpec (PPa.PatchPair varsO varsP) asm result

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

withEmptyAssumptionFrame ::
  EquivM sym arch f ->
  EquivM sym arch f
withEmptyAssumptionFrame f =
  local (\env -> env { envCurrentFrame = mempty }) $ f

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

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (W4B.ExprBuilder scope solver fs)

-- | Check a predicate for satisfiability (in our monad) subject to a timeout
--
-- This function wraps some lower-level functions and invokes the SMT solver in
-- a way that allows async exceptions to propagate up (e.g., ctrl+c or signals),
-- but it converts synchronous exceptions (e.g., errors raised by the solver or
-- the code the parses the solver response) into values.
--
-- FIXME: Add a facility for saving the SMT problem under the given name
checkSatisfiableWithModel ::
  PT.Timeout ->
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM sym arch a) ->
  EquivM sym arch (Either SomeException a)
checkSatisfiableWithModel timeout _desc p k = withSymSolver $ \sym adapter -> do
  envFrame <- asks envCurrentFrame
  assumptions <- liftIO $ getAssumedPred sym envFrame
  goal <- liftIO $ W4.andPred sym assumptions p
 -- handle <- liftIO $ IO.openFile "solver.out" IO.WriteMode
  
  -- Set up a wrapper around the ground evaluation function that removes some
  -- unwanted terms and performs an equivalent substitution step to remove
  -- unbound variables (consistent with the initial query)
  let mkResult r = W4R.traverseSatResult (\r' -> pure $ SymGroundEvalFn r') pure r
  IO.withRunInIO $ \runInIO -> do
    tryJust filterAsync $ checkSatisfiableWithoutBindings timeout sym Nothing adapter goal (\r -> runInIO (mkResult r >>= k))

-- | Check the satisfiability of a predicate, with the result (including model,
-- if applicable) available in the callback. This function implements all of the
-- timeout logic. Note that it converts timeouts into 'W4R.Unknown' results.
--
-- Note that this can percolate up both async and synchronous exceptions. That
-- can include errors in parsing the responses from the SMT solver.
--
-- Note that this should not be used directly /because/ it can expose those
-- exceptions.  See 'checkSatisfiableWithModel' instead.
--
-- FIXME: Document what the bindings that we are doing without here.
checkSatisfiableWithoutBindings
  :: (sym ~ W4B.ExprBuilder t st fs)
  => PT.Timeout
  -> sym
  -> Maybe IO.Handle
  -> WSA.SolverAdapter st
  -> W4B.BoolExpr t
  -> (W4R.SatResult (W4G.GroundEvalFn t) () -> IO a)
  -> IO a
checkSatisfiableWithoutBindings timeout sym mhandle adapter p k =
  case PT.timeoutAsMicros timeout of
    Nothing -> doCheckSat
    Just micros -> do
      mres <- PT.timeout micros doCheckSat
      case mres of
        Nothing -> k W4R.Unknown
        Just r -> return r
  where
    doCheckSat = WSA.solver_adapter_check_sat adapter sym (WSA.defaultLogData { WSA.logHandle = mhandle }) [p] $ \sr -> case sr of
         W4R.Unsat core -> k (W4R.Unsat core)
         W4R.Unknown -> k W4R.Unknown
         W4R.Sat (evalFn, _) -> k (W4R.Sat evalFn)

-- | Returns True if the given predicate is satisfiable, and False otherwise
--
-- Note that this is strict: unsat and unknown are both treated as False.  Any
-- exceptions thrown during this process (due to timeout or solver error) are
-- also treated as False.
isPredSat ::
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredSat timeout p = case W4.asConstantPred p of
  Just b -> return b
  Nothing -> either (const False) id <$> checkSatisfiableWithModel timeout "isPredSat" p asSat

-- | Convert a 'W4R.Sat' result to True, and other results to False
asSat :: Monad m => W4R.SatResult mdl core -> m Bool
asSat satRes =
  case satRes of
    W4R.Sat _ -> return True
    W4R.Unsat _ -> return False
    W4R.Unknown -> return False

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
        -- Convert exceptions into False because we can't prove that it is true
        either (const False) id <$> checkSatisfiableWithModel timeout "isPredTrue'" notp asProve

-- | Convert a 'W4R.Unsat' result into True
--
-- Other SAT results become False
asProve :: Monad m => W4R.SatResult mdl core -> m Bool
asProve satRes =
  case satRes of
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

withGroundEvalFn ::
  SymGroundEvalFn sym ->
  (forall t st fs. sym ~ W4B.ExprBuilder t st fs => W4G.GroundEvalFn t -> IO a) ->
  EquivM sym arch a
withGroundEvalFn fn f = withValid $
  IO.withRunInIO $ \runInIO -> f $ W4G.GroundEvalFn (\e -> runInIO (execGroundFn fn e))

execGroundFn ::
  forall sym arch tp.
  HasCallStack =>
  SymGroundEvalFn sym  -> 
  W4.SymExpr sym tp -> 
  EquivM sym arch (W4G.GroundValue tp)  
execGroundFn (SymGroundEvalFn fn) e = do
  groundTimeout <- asks (PC.cfgGroundTimeout . envConfig)
  result <- liftIO $ (PT.timeout' groundTimeout $ W4G.groundEval fn e) `catches`
    [ Handler (\(ae :: ArithException) -> liftIO (putStrLn ("ArithEx: " ++ show ae)) >> return Nothing)
    , Handler (\(ie :: IOException) -> liftIO (putStrLn ("IOEx: " ++ show ie)) >> return Nothing)
    , Handler (\(ie :: IOError) -> liftIO (putStrLn ("IOErr: " ++ show ie)) >> return Nothing)
    ]
  case result of
    Just a -> return a
    Nothing -> throwHere PEE.InvalidSMTModel

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

-- | Emit a trace event to the frontend
--
-- This variant takes a 'BlockPair' as an input to provide context
traceBlockPair
  :: (HasCallStack)
  => PPa.BlockPair arch
  -> String
  -> EquivM sym arch ()
traceBlockPair bp msg =
  emitEvent (PE.ProofTraceEvent callStack origAddr patchedAddr (T.pack msg))
  where
    origAddr = PB.concreteAddress (PPa.pOriginal bp)
    patchedAddr = PB.concreteAddress (PPa.pPatched bp)

-- | Emit a trace event to the frontend
--
-- This variant takes a 'SimBundle' as an input to provide context
traceBundle
  :: (HasCallStack)
  => SimBundle sym arch
  -> String
  -> EquivM sym arch ()
traceBundle bundle msg =
  emitEvent (PE.ProofTraceEvent callStack origAddr patchedAddr (T.pack msg))
  where
    origAddr = PB.concreteAddress (simInBlock (simInO bundle))
    patchedAddr = PB.concreteAddress (simInBlock (simInP bundle))

--------------------------------------
-- UnliftIO

instance forall sym arch. IO.MonadUnliftIO (EquivM_ sym arch) where
  withRunInIO f = withValid $ do
    env <- ask
    catchInIO (f (runEquivM' env))

catchInIO ::
  forall sym arch a.
  IO a ->
  EquivM sym arch a
catchInIO f =
  (liftIO $ catch (Right <$> f) (\(e :: PEE.EquivalenceError arch) -> return $ Left e)) >>= \case
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
  EquivM sym arch a ->
  IO a
runEquivM' env f = withValidEnv env $ (runExceptT $ runReaderT (unEQ f) env) >>= \case
  Left err -> throwIO err
  Right result -> return result

runEquivM ::
  EquivEnv sym arch ->
  EquivM sym arch a ->
  ExceptT (PEE.EquivalenceError arch) IO a
runEquivM env f = withValidEnv env $ runReaderT (unEQ f) env

----------------------------------------
-- Errors

throwHere ::
  HasCallStack =>
  PEE.InnerEquivalenceError arch ->
  EquivM_ sym arch a
throwHere err = withValid $ do
  wb <- asks envWhichBinary
  throwError $ PEE.EquivalenceError
    { PEE.errWhichBinary = wb
    , PEE.errStackTrace = Just callStack
    , PEE.errEquivError = err
    }


instance MF.MonadFail (EquivM_ sym arch) where
  fail msg = throwHere $ PEE.EquivCheckFailure $ "Fail: " ++ msg

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
    False -> throwHere $ PEE.IncompatibleDomainPolarities
