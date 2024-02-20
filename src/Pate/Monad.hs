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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Pate.Monad
  ( EquivEnv(..)
  , EquivM
  , EquivM_
  , ValidSymArch
  , ExprLabel(..)
  , runEquivM
  , SimBundle(..)
  , withBinary
  , withValid
  , withValidEnv
  , withSymIO
  , withSym
  , withSolverProcess
  , withOnlineBackend
  , withPair
  , archFuns
  , runInIO1
  , manifestError
  , throwHere
  , getDuration
  , startTimer
  , emitEvent
  , emitWarning
  , emitError
  , emitError'
  , getBinCtx
  , getBinCtx'
  , blockToSegOff
  , ifConfig
  , traceBundle
  , traceBlockPair
  , lookupArgumentNames
  , SymGroundEvalFn(..)
  , execGroundFn
  , withGroundEvalFn
  , wrapGroundEvalFn
  , extractBindings
  , getFootprints
  -- sat helpers
  , checkSatisfiableWithModel
  , goalSat
  , heuristicSat
  , isPredSat
  , isPredSat'
  , isPredTrue'
  , concretePred
  -- working under a 'SimSpec' context
  , withSimSpec
  , withFreshVars
  , withFreshScope
  -- assumption management
  , withAssumption
  , withSatAssumption
  , withAssumptionSet
  , withPathCondition
  , applyCurrentAsms
  , applyCurrentAsmsExpr
  , currentAsm
  -- nonces
  , freshNonce
  , withProofNonce
  -- caching
  , lookupBlockCache
  , modifyBlockCache
  , resetBlockCache
  -- equivalence
  , equivalenceContext
  , safeIO
  , concretizeWithSolver
  , concretizeWithModel
  , emitTrace
  , emitTraceLabel
  , withSubTraces
  , subTrace
  , subTree
  , fnTrace
  , getWrappedSolver
  , joinPatchPred
  , module PME
  , atPriority, currentPriority, thisPriority)
  where

import           GHC.Stack ( HasCallStack, callStack )

import           Control.Lens ( (&), (.~) )
import qualified Control.Monad.Fail as MF
import           Control.Monad (void)
import           Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Concurrent as IO
import           Control.Exception hiding ( try, finally, catch, mask )
import           Control.Monad.Catch hiding ( catches, tryJust, Handler )
import qualified Control.Monad.Reader as CMR
import           Control.Monad.Reader ( asks, ask )
import           Control.Monad.Except

import           Data.Maybe ( fromMaybe )
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.IORef as IO
import qualified Data.Text as T
import qualified Data.Time as TM
import           Data.Kind ( Type )
import           Data.Typeable
import           Data.Default
import           Data.String ( IsString(..) )

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.SetF as SetF
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some

import qualified Data.Parameterized.TraversableF as TF

import qualified Lumberjack as LJ

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.Backend as LCB

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MM
import qualified Data.Macaw.BinaryLoader as MBL

import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R
import qualified What4.Symbol as WS
import           What4.Utils.Process (filterAsync)
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as W4
import           What4.ExprHelpers
import           What4.ProgramLoc

import qualified Pate.Arch as PA
import qualified Pate.Address as PB
import           Pate.AssumptionSet ( AssumptionSet )
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Monad.Context as PMC
import           Pate.Monad.Environment as PME
import           Pate.Panic
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo
import qualified Pate.Timeout as PT
import qualified Pate.Verification.Concretize as PVC
import           Pate.TraceTree
import Data.Functor.Const (Const(..))
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace
import Data.List

atPriority :: 
  NodePriority ->
  Maybe String ->
  EquivM_ sym arch a ->
  EquivM sym arch a
atPriority p Nothing f = CMR.local (\env -> env { envCurrentPriority = p }) f
atPriority p (Just msg) f = CMR.local (\env -> env { envCurrentPriority = (tagPriority msg p) }) f

currentPriority ::
  EquivM sym arch NodePriority
currentPriority = CMR.asks envCurrentPriority

thisPriority ::
  EquivM sym arch (NodePriorityK -> NodePriority)
thisPriority = do
  priority <- currentPriority
  return $ (\pK -> mkPriority pK priority)

lookupBlockCache ::
  (EquivEnv sym arch -> BlockCache arch a) ->
  PB.BlockPair arch ->
  EquivM sym arch (Maybe a)
lookupBlockCache f pPair = do
  BlockCache cache <- CMR.asks f
  cache' <- liftIO $ IO.readMVar cache
  case M.lookup pPair cache' of
    Just r -> return $ Just r
    Nothing -> return Nothing

resetBlockCache :: 
  (EquivEnv sym arch -> BlockCache arch a) ->
  EquivM sym arch ()
resetBlockCache f = do
  BlockCache cache <- CMR.asks f
  liftIO $ IO.modifyMVar_ cache (\_ -> return M.empty)

modifyBlockCache ::
  (EquivEnv sym arch -> BlockCache arch a) ->
  PB.BlockPair arch ->
  (a -> a -> a) ->
  a ->
  EquivM sym arch ()
modifyBlockCache f pPair merge val = do
  BlockCache cache <- CMR.asks f
  liftIO $ IO.modifyMVar_ cache
    (\m -> return $ M.insertWith merge pPair val m)

-- | Execute actions if the given configuration flag is set (not set)
--
-- If the flag is set in the environment, execute the first action. Otherwise,
-- execute the second.
ifConfig ::
  (PC.VerificationConfig PA.ValidRepr -> Bool) ->
  EquivM sym arch a ->
  EquivM sym arch a ->
  EquivM sym arch a
ifConfig checkCfg ifT ifF = (CMR.asks $ checkCfg . envConfig) >>= \case
  True -> ifT
  False -> ifF

freshNonce :: EquivM sym arch (N.Nonce (PF.SymScope sym) tp)
freshNonce = do
  gen <- CMR.asks envNonceGenerator
  liftIO $ N.freshNonce gen

withProofNonce ::
  forall tp sym arch a.
  (PF.ProofNonce sym tp -> EquivM sym arch a) ->
  EquivM sym arch a
withProofNonce f = withValid $ do
  nonce <- freshNonce
  let proofNonce = PF.ProofNonce nonce
  CMR.local (\env -> env { envParentNonce = Some proofNonce }) (f proofNonce)


-- | Start the timer to be used as the initial time when computing
-- the duration in a nested 'emitEvent'
startTimer :: EquivM sym arch a -> EquivM sym arch a
startTimer f = do
  startTime <- liftIO TM.getCurrentTime
  CMR.local (\env -> env { envStartTime = startTime}) f

-- | Time since the most recent 'startTimer'
getDuration :: EquivM sym arch TM.NominalDiffTime
getDuration = do
  startedAt <- CMR.asks envStartTime
  finishedBy <- liftIO TM.getCurrentTime
  return $ TM.diffUTCTime finishedBy startedAt

emitWarning ::
  HasCallStack =>
  PEE.InnerEquivalenceError arch ->
  EquivM sym arch ()
emitWarning innererr = do
  err <- CMR.asks envWhichBinary >>= \case
    Just (Some wb) -> return $ PEE.equivalenceErrorFor wb innererr
    Nothing -> return $ PEE.equivalenceError innererr
  case PEE.isTracedWhenWarning err of
    True -> emitTraceWarning err
    False -> return ()
  emitEvent (\_ -> PE.Warning err)

-- | Emit an event declaring that an error has been raised, but only throw
-- the error if it is not recoverable (according to 'PEE.isRecoverable')
emitError' :: HasCallStack => PEE.InnerEquivalenceError arch -> EquivM_ sym arch PEE.EquivalenceError
emitError' err = withValid $ do
  Left err' <- manifestError (throwHere err >> return ())
  emitEvent (\_ -> PE.ErrorRaised err')
  return err'

emitError :: HasCallStack => PEE.InnerEquivalenceError arch -> EquivM_ sym arch ()
emitError err = void $ emitError' err

emitEvent :: (TM.NominalDiffTime -> PE.Event arch) -> EquivM sym arch ()
emitEvent evt = do
  duration <- getDuration
  logAction <- CMR.asks envLogger
  IO.liftIO $ LJ.writeLog logAction (evt duration)

newtype EquivM_ sym arch a = EquivM { unEQ :: (CMR.ReaderT (EquivEnv sym arch) IO) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , CMR.MonadReader (EquivEnv sym arch)
           , MonadThrow
           , MonadMask
           , MonadCatch
           )

-- Treat PEE.EquivalenceError specially, although it is just raised like any other exception
instance MonadError PEE.EquivalenceError (EquivM_ sym arch) where
  throwError e = throwM e
  catchError f hdl = f `catch` (\(e :: PEE.EquivalenceError) -> hdl e)

instance MonadTreeBuilder '(sym, arch) (EquivM_ sym arch) where
  getTreeBuilder = CMR.asks envTreeBuilder
  withTreeBuilder treeBuilder f = CMR.local (\env -> env { envTreeBuilder = treeBuilder }) f

instance PPa.PatchPairM (EquivM_ sym arch) where
  throwPairErr :: HasCallStack => EquivM_ sym arch a
  throwPairErr = throwHere $ PEE.InconsistentPatchPairAccess
  catchPairErr a b = catchError a (\e -> case PEE.errEquivError e of
                                      Left (PEE.SomeInnerError PEE.InconsistentPatchPairAccess) -> b
                                      _ -> throwError e)

joinPatchPred ::
  (forall bin. PBi.KnownBinary bin => PBi.WhichBinaryRepr bin -> EquivM_ sym arch (W4.Pred sym)) ->
  EquivM sym arch (W4.Pred sym)
joinPatchPred f = (PPa.forBinsC f) >>= \case
  PPa.PatchPairC a b -> withSym $ \sym -> liftIO $ W4.andPred sym a b
  PPa.PatchPairSingle _ (Const a) -> return a

type ValidSymArch (sym :: Type) (arch :: Type) = (PSo.ValidSym sym, PA.ValidArch arch)
type EquivM sym arch a = ValidSymArch sym arch => EquivM_ sym arch a


newtype ExprLabel = ExprLabel String
  deriving (Eq, Ord, Show)

instance Default ExprLabel where
  def = ExprLabel ""

instance IsString ExprLabel where
  fromString str = ExprLabel str

instance Semigroup ExprLabel where
  (ExprLabel a) <> (ExprLabel b) = ExprLabel (a ++ b)

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "expr" where
  type TraceNodeType '(sym,arch) "expr" = Some (W4.SymExpr sym)
  type TraceNodeLabel "expr" = ExprLabel
  
  prettyNode _lbl (Some e) = W4.printSymExpr e
  nodeTags = 
    [(Summary, printExprTruncated @sym)
    ,(Simplified, printExprTruncated @sym)
    -- TODO: how to present simplified view of expressions?
    ,(Simplified_Detail, prettyNode @_ @'(sym,arch) @"expr")
    ]

printExprTruncated ::
  PSo.ValidSym sym =>
  ExprLabel ->
  Some (W4.SymExpr sym) ->
  PP.Doc a
printExprTruncated (ExprLabel lbl) (Some e) = 
  let pfx = case lbl of
        "" -> ""
        _ -> "(" <> PP.pretty lbl <> ") "
      ls = lines (show (W4.printSymExpr e))
  in case ls of
    [] -> pfx
    [a] -> pfx <> PP.pretty a
    (a:as) -> pfx <> PP.pretty a <> ".." <> PP.pretty (last as)
              
withBinary ::
  forall bin sym arch a.
  PBi.KnownBinary bin =>
  EquivM sym arch a ->
  EquivM sym arch a
withBinary f =
  let
    repr :: PBi.WhichBinaryRepr bin = knownRepr
  in CMR.local (\env -> env { envWhichBinary = Just (Some repr) }) f

getBinCtx ::
  forall bin sym arch.
  KnownRepr PBi.WhichBinaryRepr bin =>
  EquivM sym arch (PMC.BinaryContext arch bin)
getBinCtx = getBinCtx' knownRepr

getBinCtx' ::
  PBi.WhichBinaryRepr bin ->
  EquivM sym arch (PMC.BinaryContext arch bin)
getBinCtx' repr = PPa.get repr =<< (CMR.asks (PMC.binCtxs . envCtx))

blockToSegOff ::
  PB.ConcreteBlock arch bin ->
  EquivM sym arch (MM.ArchSegmentOff arch)
blockToSegOff blk = do
  binCtx <- getBinCtx' (PB.blockBinRepr blk)
  let mem = MBL.memoryImage $ PMC.binary binCtx
  case PB.addrAsSegOff mem (PB.concreteAddress blk) of
    Just segOff -> return segOff
    Nothing -> throwHere $ PEE.InvalidBlockAddress blk

withValid :: forall a sym arch.
  (forall t st fs . (sym ~ WE.ExprBuilder t st fs, PA.ValidArch arch, PSo.ValidSym sym) => EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- CMR.ask
  withValidEnv env $ f

withValidEnv :: forall a sym arch.
  EquivEnv sym arch ->
  (forall t st fs . (sym ~ WE.ExprBuilder t st fs, PA.ValidArch arch, PSo.ValidSym sym) => a) ->
  a
withValidEnv (EquivEnv { envValidSym = PSo.Sym {}, envValidArch = PA.SomeValidArch {}}) f = f

withSym ::
  (forall t st fs . (sym ~ WE.ExprBuilder t st fs) => sym -> EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  PSo.Sym _ sym _ <- CMR.asks envValidSym
  f sym

withSolverProcess ::
  (forall scope st fs solver.
     (sym ~ WE.ExprBuilder scope st fs) => WPO.OnlineSolver solver =>
     WPO.SolverProcess scope solver -> EquivM sym arch a) ->
  EquivM sym arch a
withSolverProcess f = withOnlineBackend $ \bak -> do
  let doPanic = panic Solver "withSolverProcess" ["Online solving not enabled"]
  IO.withRunInIO $ \runInIO -> LCBO.withSolverProcess bak doPanic $ \sp ->
    runInIO (f sp)

withOnlineBackend ::
  (forall scope st fs solver.
     (sym ~ WE.ExprBuilder scope st fs) => WPO.OnlineSolver solver =>
     LCBO.OnlineBackend solver scope st fs -> EquivM sym arch a) ->
  EquivM sym arch a
withOnlineBackend f = do
  PSo.Sym _ _ bak <- CMR.asks envValidSym
  f bak

withSymIO :: forall sym arch a.
  (forall t st fs . (sym ~ WE.ExprBuilder t st fs) => sym -> IO a) ->
  EquivM sym arch a
withSymIO f = withSym (\sym -> liftIO (f sym))

archFuns :: forall sym arch.
  EquivM sym arch (MS.MacawSymbolicArchFunctions arch)
archFuns = do
  archVals <- CMR.asks envArchVals
  return $ MS.archFunctions archVals

-----------------------------------------------
-- State and assumption management

unconstrainedRegister ::
  forall sym arch bin tp.
  (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  PBi.WhichBinaryRepr bin ->
  [T.Text] ->
  MM.ArchReg arch tp ->
  EquivM sym arch (PSR.MacawRegVar sym tp)
unconstrainedRegister bin argNames reg = do
  let repr = MM.typeRepr reg
  let suffix = PBi.short bin
  let name = case PA.fromRegisterDisplay (PA.displayRegister reg) of
        Just nm -> nm
        Nothing -> showF reg
  case repr of
    MM.BVTypeRepr n
      | Just Refl <- testEquality n (MM.memWidthNatRepr @(MM.ArchAddrWidth arch)) -> withSymIO $ \sym -> do
          let margName = PA.argumentNameFrom argNames reg
          let name' = maybe name T.unpack margName
          ptr@(CLM.LLVMPointer region off) <- freshPtr sym (name' ++ suffix) n
          let iRegion = W4.natToIntegerPure region
          return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> iRegion Ctx.:> off)
      | otherwise -> withSymIO $ \sym -> do
          -- For bitvector types that are not pointer width, fix their region number to 0 since they cannot be pointers
          bits <- W4.freshConstant sym (WS.safeSymbol (name ++ suffix)) (W4.BaseBVRepr n)
          ptr <- CLM.llvmPointer_bv sym bits
          zero <- W4.intLit sym 0
          return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> zero Ctx.:> bits)
    MM.BoolTypeRepr -> withSymIO $ \sym -> do
      var <- W4.freshConstant sym (WS.safeSymbol (name ++ suffix)) W4.BaseBoolRepr
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) var) (Ctx.empty Ctx.:> var)
    MM.TupleTypeRepr PL.Nil -> do
      return $ PSR.MacawRegVar (PSR.MacawRegEntry (MS.typeToCrucible repr) Ctx.Empty) Ctx.empty
    _ -> throwHere $ PEE.UnsupportedRegisterType (Some (MS.typeToCrucible repr))

withSimSpec ::
  Scoped f =>
  Scoped g =>
  (forall v. PEM.ExprMappable sym (f v)) =>
  PB.BlockPair arch ->
  SimSpec sym arch f ->
  (forall v. SimScope sym arch v -> f v -> EquivM sym arch (g v)) ->
  EquivM sym arch (SimSpec sym arch g)
withSimSpec blocks spec f = withSym $ \sym -> do
  spec_fresh <- withFreshVars blocks $ \vars -> liftIO $ bindSpec sym vars spec
  forSpec spec_fresh $ \scope body ->
    withAssumptionSet (scopeAsm scope) (f scope body)

lookupArgumentNamesSingle
  :: PBi.WhichBinaryRepr bin
  -> PB.ConcreteBlock arch bin
  -> EquivM sym arch [T.Text]
lookupArgumentNamesSingle bin blk = do
  let addr = PB.concreteAddress blk
  ctx <- CMR.asks envCtx
  binCtx <- PPa.get bin (PMC.binCtxs ctx)
  let funcHintIdx = PMC.functionHintIndex binCtx
  case M.lookup addr funcHintIdx of
    Nothing -> return []
    Just fd -> return (PH.functionArguments fd)

-- | Look up the arguments for this block slice if it is a function entry point
-- (and there are sufficient metadata hints)
lookupArgumentNames
  :: PB.BlockPair arch
  -> EquivM sym arch [T.Text]
lookupArgumentNames pp = PPa.oneBin $ \bin -> do
  blk <- PPa.get bin pp
  lookupArgumentNamesSingle bin blk

-- Although 'AssumptionSet' has a scope parameter, the current interface doesn't have a
-- good mechanism for enforcing the fact that we are only pushing assumptions that
-- are actually scoped properly.
-- This is manifest in the fact that the background frame in 'envCurrentFrame' doesn't
-- track any scope, and is therefore unsafely coerced into any target scope.
-- TODO: Rather than trying to enforce this statically (which would be difficult and require
-- tracking scopes in many more places) we can add runtime checks in places where scope
-- violations would be problematic (i.e. when attempting to safely coerce one scope into another)
-- see: https://github.com/GaloisInc/pate/issues/310

-- | Project the current background 'AssumptionSet' into any scope 'v'
currentAsm :: EquivM sym arch (AssumptionSet sym)
currentAsm = CMR.asks envCurrentFrame

withFreshScope ::
  forall sym arch f.
  Scoped f =>
  PB.BlockPair arch ->
  (forall v. SimScope sym arch v -> EquivM sym arch (f v)) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshScope bPair f = do
  dummy_spec <- withFreshVars @sym @arch @(WithScope ()) bPair $ \_ -> do
    return (mempty, WithScope ())
  forSpec dummy_spec $ \scope _ -> f scope

-- | Create a new 'SimSpec' by evaluating the given function under a fresh set
-- of bound variables. The returned 'AssumptionSet' is set as the assumption
-- in the resulting 'SimSpec'.
withFreshVars ::
  forall sym arch f.
  Scoped f =>
  PB.BlockPair arch ->
  (forall v. (SimVars sym arch v PBi.Original, SimVars sym arch v PBi.Patched) -> EquivM sym arch (AssumptionSet sym,(f v))) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshVars blocks f = do
  argNames <- lookupArgumentNames blocks
  let
    mkMem :: forall bin. PBi.WhichBinaryRepr bin -> EquivM sym arch (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))
    mkMem bin = do
      binCtx <- getBinCtx' bin
      let baseMem = MBL.memoryImage $ PMC.binary binCtx
      withSymIO $ \sym -> MT.initMemTrace @_ @arch sym baseMem (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))

    mkStackBase :: forall bin v. PBi.WhichBinaryRepr bin -> EquivM_ sym arch (StackBase sym arch v)
    mkStackBase bin = withSymIO $ \sym -> freshStackBase sym bin (Proxy @arch)

    mkMaxRegion :: forall bin v. PBi.WhichBinaryRepr bin -> EquivM_ sym arch (ScopedExpr sym W4.BaseIntegerType v)
    mkMaxRegion bin = withSymIO $ \sym -> liftScope0 sym $ \sym' ->
      W4.freshConstant sym' (W4.safeSymbol ("max_region" ++ PBi.short bin)) W4.BaseIntegerRepr

  freshSimSpec (\bin r -> unconstrainedRegister bin argNames r) (\x -> mkMem x) mkStackBase mkMaxRegion (\v -> f v)
 
-- should we clear this between nodes?
withFreshSatCache ::
  EquivM_ sym arch f ->
  EquivM sym arch f
withFreshSatCache f = do
  unsatCacheRef <- asks envUnsatCacheRef
  unsatCache <- liftIO $ IO.readIORef unsatCacheRef
  satCache <- asks envSatCacheRef
  -- preserve any known unsat results
  freshUnsatCacheRef <- liftIO $ IO.newIORef unsatCache
  -- discard any known sat results
  freshSatCacheRef <- liftIO $ IO.newIORef SetF.empty
  result <- CMR.local (\env -> env { envUnsatCacheRef = freshUnsatCacheRef, envSatCacheRef = freshSatCacheRef }) f
  -- preserve learned sat results
  newSatResults <- liftIO $ IO.readIORef freshSatCacheRef
  liftIO $ IO.modifyIORef satCache (SetF.union newSatResults)
  return result

withNoSatCache ::
  EquivM_ sym arch f ->
  EquivM sym arch f
withNoSatCache f = do
  freshUnsatCacheRef <- liftIO $ IO.newIORef SetF.empty
  freshSatCacheRef <- liftIO $ IO.newIORef SetF.empty
  CMR.local (\env -> env { envUnsatCacheRef = freshUnsatCacheRef, envSatCacheRef = freshSatCacheRef }) f


markPredSat ::
  W4.Pred sym ->
  EquivM sym arch ()
markPredSat p = do
  satCache <- asks envSatCacheRef
  liftIO $ IO.modifyIORef satCache (SetF.insert p)

markPredUnsat ::
  W4.Pred sym ->
  EquivM sym arch ()
markPredUnsat p = do
  unsatCache <- asks envUnsatCacheRef
  liftIO $ IO.modifyIORef unsatCache (SetF.insert p)

-- | Mark the result as sat or unsat as appropriate
processSatResult ::
  W4.Pred sym ->
  W4R.SatResult a b ->
  EquivM sym arch ()
processSatResult p r =
  void $ W4R.traverseSatResult (\a -> markPredSat p >> return a) (\b -> markPredUnsat p >> return b) r

-- | Evaluate the given function in an assumption context augmented with the given
-- 'AssumptionSet', which is also added to the current path condition.
-- Returns 'Nothing' of the assumption is not satisfiable (i.e. the path is infeasible)
withPathCondition ::
  HasCallStack =>
  AssumptionSet sym ->
  EquivM_ sym arch f ->
  EquivM sym arch (Maybe f)
withPathCondition asm f = CMR.local (\env -> env { envPathCondition = (asm <> (envPathCondition env)) }) $ withSatAssumption asm f

-- | Evaluate the given function in an assumption context augmented with the given
-- 'AssumptionSet'.
withAssumptionSet ::
  HasCallStack =>
  forall sym arch f.
  AssumptionSet sym ->
  EquivM_ sym arch f ->
  EquivM sym arch f
withAssumptionSet asm f = withSym $ \sym -> do
  curAsm <- currentAsm
  p <- liftIO $ PAS.toPred sym asm
  case PAS.isAssumedPred curAsm p of
    True -> f
    _ ->
        CMR.local (\env -> env { envCurrentFrame = (asm <> curAsm) }) $ do
        (frame, st) <- withOnlineBackend $ \bak ->  do
          st <- liftIO $ LCB.saveAssumptionState bak
          frame <- liftIO $ LCB.pushAssumptionFrame bak
          safeAssumedFalseIO mempty asm $ 
            LCB.addAssumption bak (LCB.GenericAssumption initializationLoc "withAssumptionSet" p)
          return (frame, st)
        withFreshSatCache $ do
          result <- goalSat "validateAssumptions" (W4.truePred sym) $ return
          case result of
            W4R.Sat{} -> return ()
            W4R.Unknown{} -> return ()
            W4R.Unsat{} -> withNoSatCache $ do
              safePop frame st
              asm' <- getUnsatAsm asm
              throwAssumeFalse mempty asm'
          propagateAssumeFalse asm (safePop frame st) f

safeAssumedFalseIO ::
  forall sym arch a.
  HasCallStack =>
  PAS.AssumptionSet sym ->
  PAS.AssumptionSet sym ->
  IO a ->
  EquivM sym arch a 
safeAssumedFalseIO context asm f = safeIO (\_ -> PEE.InnerSymEquivalenceError (PEE.AssumedFalse context asm)) f


throwAssumeFalse ::
  HasCallStack =>
  PAS.AssumptionSet sym ->
  PAS.AssumptionSet sym ->
  EquivM sym arch a
throwAssumeFalse context asm = throwHere $ PEE.InnerSymEquivalenceError (PEE.AssumedFalse context asm)

-- | This attempts to refine any inner 'AssumedFalse' exceptions thrown by the
--   given function, by determining which of the most recently added assumptions were
--   necessary for the predicate in the exception to be unsatisfiable
--   This is a rough approximation of computing an unsatisfiable core, but without
--   relying on solver support for it.
propagateAssumeFalse ::
  HasCallStack =>
  AssumptionSet sym {- ^ most recently pushed assumption -} ->
  EquivM_ sym arch () {- ^ function that pops this assumption from the stack -} ->
  EquivM_ sym arch a {- ^ inner computation that may throw 'PEE.AssumedFalse' -} ->
  EquivM sym arch a
propagateAssumeFalse asm doPop f = withSym $ \sym -> do

  catchError (f >>= \a -> doPop >> return a)
    (\e -> case PEE.errEquivError e of 
      Left (PEE.SomeInnerError (PEE.InnerSymEquivalenceError (PEE.AssumedFalse asm_context badasm))) -> do
        -- an inner computation assumed false and returned the offending
        -- predicate
        -- check if any individual assumption we just pushed was the cause
        -- of the error

        -- this is a sanity check that the predicate from the exception
        -- is unsatisfiable in the current assumption context (plus any additional context
        -- it has accumulated)
        bad_pred_total <- PAS.toPred sym (asm_context <> badasm)

        heuristicSat "validateIndividualAsms" bad_pred_total $ \case
          W4R.Sat{} -> 
            -- if the predicate is satisfiable here, then something has gone wrong
            -- with our assumption stack management
            throwHere PEE.SolverStackMisalignment
          _ -> return ()

        doPop
        -- we need to avoid clobbering the cache after popping, since
        -- we're now in a different satisfiability context
        withNoSatCache $ do
          -- after popping this assumption, we see if the previously-unsatisfiable
          -- predicate is now satisfiable
          -- if it still isn't, then 'asm' has no effect on the satisfiability of
          -- the predicate, and we don't need to add anything to the context
          asm' <- fmap (fromMaybe mempty) $ withSatAssumption (asm_context <> badasm) $ do
            -- if 'badasm' is now satisfiable without 'asms' being assumed, then
            -- we know that there is some incompatibility between them, and we
            -- want to refine this to exactly the subset of assumptions from
            -- 'asm' that are needed to cause unsatisfiability
            p <- PAS.toPred sym asm
            result <- heuristicSat "validateIndividualAsms" p return
            case result of
              W4R.Sat{} -> 
                -- another sanity check, 'asms' should now be unsatisfiable
                -- if our assumption stack is wellformed
                throwHere PEE.SolverStackMisalignment
              -- finally, we can refine 'asm' to exactly the subset
              -- of assumptions that are now unsatisfiable
              _ -> getUnsatAsm asm
          
          throwAssumeFalse (asm_context <> asm') badasm
      _ -> do
        doPop
        throwError e)

getUnsatAsm ::
  forall sym arch. 
  HasCallStack =>
  AssumptionSet sym  ->
  EquivM sym arch (AssumptionSet sym)
getUnsatAsm asms = do
  let atoms = PAS.toAtomList asms
  atoms' <- go_fix atoms
  return $ mconcat atoms'
  where
    -- continue sweeping the list of assumptions until
    -- no change is made
    go_fix :: [AssumptionSet sym] -> EquivM_ sym arch [AssumptionSet sym]
    go_fix asms_list = do
      asms_list' <- go 0 asms_list
      case (length asms_list == length asms_list') of
        True -> return asms_list
        False -> go_fix asms_list'
    -- prune the list down to exactly what's necessary for unsatisfiability
    go :: Int -> [AssumptionSet sym] -> EquivM_ sym arch [AssumptionSet sym]
    go idx asms_list = withSym $ \sym -> case splitAt idx asms_list of
      (_,[]) -> return asms_list
      (hd,_:tl) -> do
        let asm' = (mconcat hd) <> (mconcat tl)
        p <- PAS.toPred sym asm'
        res <- checkSatisfiableWithModel (PT.Seconds 5) "getUnsat" p return
        case res of
          Right (W4R.Unsat{}) -> go idx (hd++tl)
          _ -> go (idx+1) asms_list

-- | try to pop the assumption frame, but restore the solver state
--   if this fails
safePop ::
  LCB.FrameIdentifier ->
  LCB.AssumptionState sym ->
  EquivM sym arch ()
safePop frame st = withOnlineBackend $ \bak -> 
  catchError
    (safeIO (\_ -> PEE.SolverStackMisalignment) (void $ LCB.popAssumptionFrame bak frame)) $ \_ -> do 
      void $ liftIO $ tryJust filterAsync $ LCBO.restoreSolverState bak st

-- | Evaluate the given function in an assumption context augmented with the given
-- predicate.
withAssumption ::
  HasCallStack =>
  W4.Pred sym ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption asm f = withAssumptionSet (PAS.fromPred asm) f

-- | Rewrite the given 'f' with any in bindings the current 'AssumptionSet'
-- (set when evaluating under 'withAssumptionSet' and 'withAssumption').
applyCurrentAsms ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
applyCurrentAsms f = withSym $ \sym -> do
  asm <- currentAsm
  PAS.apply sym asm f


applyCurrentAsmsExpr ::
  forall sym arch tp.
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
applyCurrentAsmsExpr e = withSym $ \sym -> do
  PEM.SymExprMappable aEM <- return $ PEM.symExprMappable sym
  aEM @tp $ applyCurrentAsms e

-- | First check if an assumption is satisfiable before assuming it. If it is not
-- satisfiable, return Nothing.
withSatAssumption ::
  HasCallStack =>
  AssumptionSet sym ->
  EquivM_ sym arch f ->
  EquivM sym arch (Maybe f)
withSatAssumption asm f = withSym $ \sym -> do
  p <- liftIO $ PAS.toPred sym asm
  case W4.asConstantPred p of
    Just False -> return Nothing
    Just True -> Just <$> f
    _ ->  do
      curAsm <- currentAsm
      CMR.local (\env -> env { envCurrentFrame = (asm <> curAsm) }) $ do
        mst <- withOnlineBackend $ \bak -> do
          st <- liftIO $ LCB.saveAssumptionState bak
          frame <- liftIO $  LCB.pushAssumptionFrame bak
          catchError
            (safeAssumedFalseIO mempty asm $ do
              LCB.addAssumption bak (LCB.GenericAssumption initializationLoc "withAssumptionSet" p)
              return $ Just (frame, st))
            (\_ -> (safeIO (\_ -> PEE.SolverStackMisalignment) (LCB.popAssumptionFrame bak frame)) >> return Nothing)
        case mst of
          Just (frame, st) -> do
            -- it's critical that we don't execute the inner action inside
            -- the 'goalSat' continuation, since we're popping the outer frame
            -- after it's finished (or on an error result)
            res <- goalSat "check assumptions" (W4.truePred sym) return
            case res of
              W4R.Sat{} -> Just <$> propagateAssumeFalse asm (safePop frame st) (withFreshSatCache f)
              -- on an inconclusive result we can't safely return 'Nothing' since
              -- that may unsoundly exclude viable paths
              W4R.Unknown -> safePop frame st >> throwHere PEE.InconclusiveSAT
              W4R.Unsat{} -> safePop frame st >> return Nothing
          -- crucible failed to push the assumption, so we double check that
          -- it is not satisfiable
          Nothing -> goalSat "check assumptions" p $ \case
            W4R.Sat{} -> throwHere $ PEE.InconclusiveSAT
            W4R.Unknown -> throwHere $ PEE.InconclusiveSAT
            W4R.Unsat{} -> return Nothing

--------------------------------------
-- Sat helpers

data SymGroundEvalFn sym where
  SymGroundEvalFn :: W4G.GroundEvalFn scope -> SymGroundEvalFn (WE.ExprBuilder scope solver fs)

-- | Check satisfiability of the given predicate in the current assumption sate
-- Any thrown exceptions are captured and passed to the continuation as an
-- 'Unknown' result.
-- Times out the solver according to the "goal" timeout
goalSat ::
  HasCallStack =>
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM_ sym arch a) ->
  EquivM sym arch a
goalSat desc p k = do
  isPredSat_cache p >>= \case
    Just False -> k (W4R.Unsat ())
    _ -> do
      goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
      checkSatisfiableWithModel goalTimeout desc p k >>= \case
        Left _err -> k W4R.Unknown
        Right a -> return a

-- | Check satisfiability of the given predicate in the current assumption sate
-- Any thrown exceptions are captured and passed to the continuation as an
-- 'Unknown' result.
-- Times out the solver according to the "heuristic" timeout
heuristicSat ::
  HasCallStack =>
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM_ sym arch a) ->
  EquivM sym arch a
heuristicSat desc p k = do
  isPredSat_cache p >>= \case
    Just False -> k (W4R.Unsat ())
    _ -> do
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      checkSatisfiableWithModel heuristicTimeout desc p k >>= \case
        Left _err -> k W4R.Unknown
        Right a -> return a

getWrappedSolver ::
  EquivM sym arch (PVC.WrappedSolver sym IO)
getWrappedSolver = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  IO.withRunInIO $ \inIO -> return $ PVC.WrappedSolver sym $ \_desc p k -> inIO $ do
    isPredSat_cache p >>= \case
      Just False -> liftIO $ (k (W4R.Unsat ()))
      _ -> do
        r <- checkSatisfiableWithModel heuristicTimeout "concretizeWithSolver" p $ \res -> IO.withRunInIO $ \inIO' -> do
          res' <- W4R.traverseSatResult (\r' -> return $ W4G.GroundEvalFn (\e' -> inIO' (execGroundFn r' e'))) pure res
          k res'
        case r of
          Left _err -> liftIO $ k W4R.Unknown
          Right a -> return a
  

concretizeWithModel ::
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
concretizeWithModel fn e = withSym $ \sym -> do
  grnd <- execGroundFn fn e
  liftIO $ PVC.symbolicFromConcrete sym grnd e

-- | Concretize a symbolic expression in the current assumption context
concretizeWithSolver ::
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
concretizeWithSolver e = withSym $ \sym -> do
  
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  let wsolver = PVC.WrappedSolver sym $ \_desc p k -> do
        isPredSat_cache p >>= \case
          Just False -> (k (W4R.Unsat ()))
          _ -> do
            r <- checkSatisfiableWithModel heuristicTimeout "concretizeWithSolver" p $ \res -> IO.withRunInIO $ \inIO -> do
              res' <- W4R.traverseSatResult (\r' -> return $ W4G.GroundEvalFn (\e' -> inIO (execGroundFn r' e'))) pure res
              inIO (k res')
            case r of
              Left _err -> k W4R.Unknown
              Right a -> return a

  PVC.resolveSingletonSymbolicAsDefault wsolver e

-- | Check a predicate for satisfiability (in our monad) subject to a timeout
--
-- This function wraps some lower-level functions and invokes the SMT solver in
-- a way that allows async exceptions to propagate up (e.g., ctrl+c or signals),
-- but it converts synchronous exceptions (e.g., errors raised by the solver or
-- the code the parses the solver response) into values.
--
-- FIXME: Add a facility for saving the SMT problem under the given name
checkSatisfiableWithModel ::
  forall sym arch a.
  HasCallStack =>
  PT.Timeout ->
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM_ sym arch a) ->
  EquivM sym arch (Either SomeException a)
checkSatisfiableWithModel timeout desc p k = withSym $ \sym -> do
  (frame, st) <- withOnlineBackend $ \bak -> liftIO $ do
    st <- LCB.saveAssumptionState bak
    frame <- LCB.pushAssumptionFrame bak
    return (frame, st)
  mres <- withSolverProcess $ \sp -> liftIO $ do
    W4.assume (WPO.solverConn sp) p
    tryJust filterAsync $ do
      res <- checkSatisfiableWithoutBindings timeout sym desc $ WPO.checkAndGetModel sp "checkSatisfiableWithModel"
      W4R.traverseSatResult (\r' -> pure $ SymGroundEvalFn r') pure res
  case mres of
    Left err -> do
      safePop frame st
      return $ Left err
    Right res -> do
      processSatResult p res
      fmap Right $ k res `finally` (safePop frame st)

-- | Check the satisfiability of a predicate, returning with the result (including model,
-- if applicable). This function implements all of the
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
  :: (sym ~ WE.ExprBuilder t st fs)
  => PT.Timeout
  -> sym
  -> String
  -> IO (W4R.SatResult (W4G.GroundEvalFn t) ())
  -> IO (W4R.SatResult (W4G.GroundEvalFn t) ())
checkSatisfiableWithoutBindings timeout _sym _desc doCheckSat =
  case PT.timeoutAsMicros timeout of
    Nothing -> doCheckSat
    Just micros -> do
      mres <- PT.timeout micros doCheckSat
      case mres of
        Nothing -> return W4R.Unknown
        Just r -> return r

-- | Returns True if the given predicate is satisfiable, and False otherwise
--
-- Note that this is strict: unsat and unknown are both treated as False.  Any
-- exceptions thrown during this process (due to timeout or solver error) are
-- also treated as False.
isPredSat ::
  forall sym arch .
  HasCallStack =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredSat timeout p = fromMaybe False <$> isPredSat' timeout p

isPredSat' ::
  forall sym arch .
  HasCallStack =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch (Maybe Bool)
isPredSat' timeout p = isPredSat_cache p >>= \case
  Just b -> return $ Just b
  Nothing -> 
    either (const Nothing) Just <$> checkSatisfiableWithModel timeout "isPredSat" p (\x -> asSat x)

-- | Do we have a cached result for this predicate?
isPredSat_cache :: 
  W4.Pred sym ->
  EquivM sym arch (Maybe Bool)
isPredSat_cache p = case W4.asConstantPred p of
  Just b -> return $ Just b
  Nothing -> do
    satCacheRef <- asks envSatCacheRef
    satCache <- liftIO $ IO.readIORef satCacheRef

    unSatCacheRef <- asks envUnsatCacheRef
    unSatCache <- liftIO $ IO.readIORef unSatCacheRef
    case SetF.member p satCache of
      True -> return $ Just True
      False -> case SetF.member p unSatCache of
        True -> return $ Just False
        False -> return Nothing

-- | Convert a 'W4R.Sat' result to True, and other results to False
asSat :: Monad m => W4R.SatResult mdl core -> m Bool
asSat satRes =
  case satRes of
    W4R.Sat _ -> return True
    W4R.Unsat _ -> return False
    W4R.Unknown -> return False

-- | Same as 'isPredTrue' but does not throw an error if the result is inconclusive
isPredTrue' ::
  HasCallStack =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch Bool
isPredTrue' timeout p = case W4.asConstantPred p of
  Just b -> return b
  _ -> do
    frame <- currentAsm
    case PAS.isAssumedPred frame p of
      True -> return True
      False -> do
        notp <- withSymIO $ \sym -> W4.notPred sym p
        isPredSat' timeout notp >>= \case
          Just True -> return False
          Just False -> return True
          Nothing -> return False -- TODO!!! This swallows the exception!

concretePred ::
  HasCallStack =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch (Maybe Bool)
concretePred timeout p = case W4.asConstantPred p of
  Just b -> return $ Just b
  _ -> do
    
    notp <- withSymIO $ \sym -> W4.notPred sym p
    
    r <- isPredSat' timeout notp >>= \case
      Just True -> return $ Just False
      Just False -> return $ Just True
      Nothing -> return Nothing
    case r of
      Nothing -> return Nothing
      Just True -> return $ Just True
      -- the predicate is maybe false, but not necessarily false
      Just False -> do
        isPredSat' timeout p >>= \case
          -- p can be true or false
          Just True -> return Nothing
          -- p is necessarily false
          Just False -> return $ Just False
          Nothing -> return Nothing

instance Par.IsFuture (EquivM_ sym arch) Par.Future where
  present m = IO.withRunInIO $ \runInIO -> Par.present (runInIO m)
  -- here we can implement scheduling of IOFutures, which can be tracked
  -- in the equivM state
  promise m = IO.withRunInIO $ \runInIO -> Par.promise (runInIO m)
  joinFuture future = withValid $ liftIO $ Par.joinFuture future
  forFuture future f = IO.withRunInIO $ \runInIO -> Par.forFuture future (runInIO . f)

{-
data SolverOutput sym where  
  SolverOutput :: WSat.SatResult (SymGroundEvalFn sym) () -> SolverOutput sym
  SolverErr :: String -> SolverOutput sym

data SolverInput sym where
  SolverInput :: PT.Timeout -> W4.Pred sym -> SolverInput sym
  -- solver thread that picked up this input
  SolverQueued :: IO.MVar (SolverOutput sym) -> SolverInput sym

data ForkedSolver sym where
  ForkedSolver ::
    IO.ThreadId ->
    IO.MVar (SolverOutput sym) ->
    ForkedSolver sym

data ForkedSolverPool sym where
  ForkedSolverPool ::
    IO.MVar (SolverInput sym) -> [ForkedSolver sym] -> ForkedSolverPool sym

forkedSat ::
  PT.Timeout ->
  W4.Pred sym ->
  ForkedSolverPool sym ->
  EquivM sym arch (IO (WSat.SatResult (SymGroundEvalFn sym) ()))
forkedSat timeout p (ForkedSolverPool inVar _) = do
  IO.putMVar inVar (SolverInput timeout p)
  -- TODO: is putMVar blocking until a thread picks it up?
  st <- IO.takeMVar inVar
  case st of
    SolverInput{} -> fail "Nobody picked up"
    SolverQueued outVar -> return $ do
      result <- IO.takeMVar outVar
      case result of
        SolverOutput r -> return r
        SolverErr msg -> fail msg

forkSolverPool :: Integer -> EquivM sym arch (ForkedSolverPool sym)
forkSolverPool i = do
  inVar <- IO.newEmptyVar
  solvers <- mapM (\_ -> forkSolver inVar) [0..i-1]
  return $ ForkedSolverPool inVar solvers
  
forkSolver ::
  IO.MVar (SolverInput sym) ->
  EquivM sym arch (ForkedSolver sym)
forkSolver inVar = do
  st <- withOnlineBackend $ \bak -> liftIO $ LCB.saveAssumptionState bak
  IO.withRunInIO $ \runinIO -> do
    outVar <- IO.newEmptyVar
    let
      f :: IO ()
      f = do
        
        lastInput <- IO.modifyMVarMasked stVar $ \case
          SolverInput timeout goal -> do
            _ <- IO.tryTakeMVar outVar
            return $ (SolverQueued outVar, SolverInput timeout goal)
          SolverQueued outVar' -> return $ (SolverQueued outVar', SolverQueued outVar')
          
        case lastInput of
          SolverQueued{} -> f
          SolverInput timeout goal -> runinIO $ do
            out <- withSolverProcess $ \sp -> do
              mres <- liftIO $ do
                WPO.pop sp
                WPI.push sp
                W4.assume (WPO.solverConn sp) p
                tryJust filterAsync $ do
                  res <- checkSatisfiableWithoutBindings timeout sym desc $ WPO.checkAndGetModel sp "checkSatisfiableWithModel"
                  W4R.traverseSatResult (\r' -> pure $ SymGroundEvalFn r') pure res
              case mres of
                Left err -> withOnlineBackend $ \bak -> do
                  _ <- liftIO $ tryJust filterAsync (LCBO.restoreSolverState bak st)
                    withSolverProcess $ \sp -> do
                      liftIO $ LCBO.restoreSolverState bak st
                      WPI.push sp
                      return $ SolverErr (show err)
                Right r -> return $ SolverOutput r
        IO.putMVar outVar out
        f
    thistid <- IO.myThreadId
    tid <- IO.forkFinally (runInIO (withSolverProcess $ \sp -> WPI.push sp) >> f) \case
      Left _ -> IO.putMVar outVar (SolverErr "Thread Killed") >> return ()
      Right _ -> IO.putMVar outVar (SolverErr "Thread Killed") >> return ()
-}

wrapGroundEvalFn ::
  SymGroundEvalFn sym ->
  Set (Some (W4.SymExpr sym)) ->
  EquivM sym arch (SymGroundEvalFn sym)
wrapGroundEvalFn fn@(SymGroundEvalFn gfn) es = withSym $ \sym -> do
  binds <- extractBindings fn es
  let fn' = W4G.GroundEvalFn (\e' -> (stripAnnotations sym e' >>= applyExprBindings sym binds >>= (W4G.groundEval gfn)))
  return $ SymGroundEvalFn fn'

{-
-- | Modified grounding that first applies some manual rewrites
safeGroundEvalFn ::
  SymGroundEvalFn sym ->
  W4.SymExpr sym tp ->
  (forall t st fs. sym ~ WE.ExprBuilder t st fs => W4G.GroundEvalFn t -> IO a) ->
  EquivM sym arch a  
safeGroundEvalFn fn e f = withSym $ \sym -> do
  binds <- extractBindings fn e
  IO.withRunInIO $ \runInIO -> do
    let fn' = W4G.GroundEvalFn (\e' -> (stripAnnotations sym e' >>= applyExprBindings sym binds >>= \e'' -> runInIO (emitTraceLabel @"expr" "safeGroundInput" (Some e'') >> execGroundFn fn e'')))
    f fn'
-}

extractBindings ::
  SymGroundEvalFn sym ->
  Set (Some (W4.SymExpr sym)) ->
  EquivM sym arch (ExprBindings sym)
extractBindings fn e = withSym $ \sym -> do
  vars <- (S.toList . S.unions) <$> mapM (\(Some e') -> liftIO $ boundVars e') (S.toList e)
  fmap MapF.fromList $ mapM (\(Some var) -> do
    let varE = W4.varExpr sym var
    gv <- execGroundFn fn varE
    val <- liftIO $ PVC.symbolicFromConcrete sym gv varE
    return $ MapF.Pair varE val) vars
  

withGroundEvalFn ::
  SymGroundEvalFn sym ->
  (forall t st fs. sym ~ WE.ExprBuilder t st fs => W4G.GroundEvalFn t -> IO a) ->
  EquivM sym arch a
withGroundEvalFn fn f = withValid $
  IO.withRunInIO $ \runInIO -> f $ W4G.GroundEvalFn (\e -> runInIO (execGroundFn fn e))

execGroundFn ::
  forall sym arch tp.
  HasCallStack =>
  SymGroundEvalFn sym  ->
  W4.SymExpr sym tp ->
  EquivM_ sym arch (W4G.GroundValue tp)
execGroundFn (SymGroundEvalFn fn) e = do
  groundTimeout <- CMR.asks (PC.cfgGroundTimeout . envConfig)
  result <- liftIO $ (PT.timeout' groundTimeout $ W4G.groundEval fn e) `catches`
    [ Handler (\(ae :: ArithException) -> liftIO (putStrLn ("ArithEx: " ++ show ae)) >> return Nothing)
    , Handler (\(ie :: IOException) -> liftIO (putStrLn ("IOEx: " ++ show ie)) >> return Nothing)
    , Handler (\(ie :: IOError) -> liftIO (putStrLn ("IOErr: " ++ show ie)) >> return Nothing)
    ]
  case result of
    Just a -> return a
    Nothing -> throwHere $ PEE.FailedToGroundExpr (PEE.SomeExpr @_ @sym e)

getFootprints ::
  SimBundle sym arch v ->
  EquivM sym arch (Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)))
getFootprints bundle = withSym $ \sym -> PPa.catBins $ \bin -> do
  mem <- simOutMem <$> PPa.get bin (simOut bundle)
  liftIO $ MT.traceFootprint sym mem

-- | Update 'envCurrentFunc' if the given pair is a function entry point
withPair :: PB.BlockPair arch -> EquivM sym arch a -> EquivM sym arch a
withPair pPair f = do
  env <- CMR.ask
  let env' = env { envParentBlocks = pPair:envParentBlocks env }
  let entryPair = TF.fmapF (\b -> PB.functionEntryToConcreteBlock (PB.blockFunctionEntry b)) pPair
  CMR.local (\_ -> env' & PME.envCtxL . PMC.currentFunc .~ entryPair) f

-- | Emit a trace event to the frontend
--
-- This variant takes a 'BlockPair' as an input to provide context
traceBlockPair
  :: (HasCallStack)
  => PB.BlockPair arch
  -> String
  -> EquivM sym arch ()
traceBlockPair bp msg =
  emitEvent (PE.ProofTraceEvent callStack (TF.fmapF (Const . PB.concreteAddress) bp) (T.pack msg))

-- | Emit a trace event to the frontend
--
-- This variant takes a 'SimBundle' as an input to provide context
traceBundle
  :: (HasCallStack)
  => SimBundle sym arch v
  -> String
  -> EquivM sym arch ()
traceBundle bundle msg = do
  let bp = TF.fmapF (Const . PB.concreteAddress . simInBlock) (simIn bundle)
  emitEvent (PE.ProofTraceEvent callStack bp (T.pack msg))

fnTrace :: 
  forall k e m a.
  IsTreeBuilder k e m =>
  TraceNodeType k "function_name" ->
  m a ->
  m a
fnTrace nm f = withTracing @"function_name" nm f

--------------------------------------
-- UnliftIO

instance forall sym arch. IO.MonadUnliftIO (EquivM_ sym arch) where
  withRunInIO f = withValid $ do
    env <- CMR.ask
    liftIO $ (f (\x -> runEquivM env x >>= \case
                     Left err -> throwIO err
                     Right r -> return r))

runInIO1 ::
  IO.MonadUnliftIO m =>
  (a -> m b) ->
  ((a -> IO b) -> IO b) ->
  m b
runInIO1 f g = IO.withRunInIO $ \runInIO -> g (\a -> runInIO (f a))


----------------------------------------
-- Running

runEquivM ::
  forall sym arch a.
  EquivEnv sym arch ->
  EquivM sym arch a ->
  IO (Either PEE.EquivalenceError a)
runEquivM env f = withValidEnv env $ do
  (Right <$> CMR.runReaderT (unEQ f) env) `catch` (\(e :: PEE.EquivalenceError) -> return $ Left e)

----------------------------------------
-- Errors

throwHere ::
  HasCallStack =>
  PEE.InnerEquivalenceError arch ->
  EquivM_ sym arch a
throwHere err = withValid $ do
  CMR.asks envWhichBinary >>= \case
    Just (Some wb) -> throwError $ PEE.equivalenceErrorFor wb err
    Nothing -> throwError $ PEE.equivalenceError err

instance MF.MonadFail (EquivM_ sym arch) where
  fail msg = throwHere $ PEE.EquivCheckFailure $ "Fail: " ++ msg

manifestError :: EquivM_ sym arch a -> EquivM sym arch (Either PEE.EquivalenceError a)
manifestError act = do
  catchError (Right <$> act) (pure . Left) >>= \case
    r@(Left er) -> CMR.asks (PC.cfgFailureMode . envConfig) >>= \case
      PC.ThrowOnAnyFailure -> throwError er
      PC.ContinueAfterRecoverableFailures -> case PEE.isRecoverable er of
        True -> emitTraceError er >> return r
        False -> throwError er
      PC.ContinueAfterFailure -> emitTraceError er >> return r
    r -> return r

-- | Run an IO operation, internalizing any exceptions raised
safeIO ::
  forall sym arch a.
  HasCallStack =>
  (SomeException -> PEE.InnerEquivalenceError arch) ->
  IO a ->
  EquivM_ sym arch a
safeIO mkex f = withValid $ (liftIO $ tryJust filterAsync f) >>= \case
  Left err | Just (ex :: PEE.EquivalenceError) <- fromException err ->
    throwError ex
  Left err -> throwHere (mkex err)
  Right a -> return a

----------------------------------------

equivalenceContext ::
  EquivM sym arch (PEq.EquivContext sym arch)
equivalenceContext = withValid $ do
  PA.SomeValidArch d <- CMR.asks envValidArch
  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  return $ PEq.EquivContext (PA.validArchDedicatedRegisters d) stackRegion (\x -> x)
