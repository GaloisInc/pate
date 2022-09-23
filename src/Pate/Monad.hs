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

module Pate.Monad
  ( EquivEnv(..)
  , EquivM
  , EquivM_
  , ValidSymArch
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
  , getBinCtx
  , getBinCtx'
  , ifConfig
  , traceBundle
  , traceBlockPair
  , lookupArgumentNames
  , SymGroundEvalFn(..)
  , execGroundFn
  , withGroundEvalFn
  , getFootprints
  -- sat helpers
  , checkSatisfiableWithModel
  , goalSat
  , heuristicSat
  , isPredSat
  , isPredTrue'
  , concretePred
  -- working under a 'SimSpec' context
  , withSimSpec
  , withFreshVars
  -- assumption management
  , validateAssumptions
  , withAssumption
  , withSatAssumption
  , withAssumptionSet
  , applyCurrentAsms
  , currentAsm
  -- nonces
  , freshNonce
  , withProofNonce
  -- caching
  , BlockCache
  , lookupBlockCache
  , modifyBlockCache
  , freshBlockCache
  -- equivalence
  , equivalenceContext
  , safeIO
  , concretizeWithSolver
  , emitTrace
  , emitTraceLabel
  , withSubTraces
  , subTrace
  , subTree
  )
  where

import           GHC.Stack ( HasCallStack, CallStack, callStack, prettyCallStack )

import           GHC.TypeLits ( Symbol, KnownSymbol )
import           Control.Lens ( (&), (.~) )
import qualified Control.Monad.Fail as MF
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Concurrent as IO
import           Control.Exception hiding ( try, finally )
import           Control.Monad.Catch hiding ( catch, catches, tryJust, Handler )
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Writer as CMW
import           Control.Monad.Except

import qualified Data.IORef as IO
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Time as TM
import           Data.Kind ( Type )
import           Data.Typeable
import           Data.Default
import           Data.String ( IsString(..) )

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableF
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr ( SymbolRepr, knownSymbol, symbolRepr )

import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC


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
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R
import qualified What4.Symbol as WS
import           What4.Utils.Process (filterAsync)
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as W4
import           What4.ExprHelpers
import           What4.ProgramLoc

import qualified Pate.Arch as PA
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

lookupBlockCache ::
  (EquivEnv sym arch -> BlockCache arch a) ->
  PPa.BlockPair arch ->
  EquivM sym arch (Maybe a)
lookupBlockCache f pPair = do
  BlockCache cache <- CMR.asks f
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
emitError :: HasCallStack => PEE.InnerEquivalenceError arch -> EquivM_ sym arch PEE.EquivalenceError
emitError err = withValid $ do
  Left err' <- manifestError (throwHere err >> return ())
  emitEvent (\_ -> PE.ErrorRaised err')
  return err'

emitEvent :: (TM.NominalDiffTime -> PE.Event arch) -> EquivM sym arch ()
emitEvent evt = do
  duration <- getDuration
  logAction <- CMR.asks envLogger
  IO.liftIO $ LJ.writeLog logAction (evt duration)

newtype EquivM_ sym arch a = EquivM { unEQ :: (CMR.ReaderT (EquivEnv sym arch) (ExceptT PEE.EquivalenceError IO)) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , CMR.MonadReader (EquivEnv sym arch)
           , MonadThrow
           , MonadCatch
           , MonadMask
           , MonadError PEE.EquivalenceError
           )

instance MonadTreeBuilder '(sym, arch) (EquivM_ sym arch) where
  getTreeBuilder = CMR.asks envTreeBuilder
  withTreeBuilder treeBuilder f = CMR.local (\env -> env { envTreeBuilder = treeBuilder }) f

type ValidSymArch (sym :: Type) (arch :: Type) = (PSo.ValidSym sym, PA.ValidArch arch)
type EquivM sym arch a = ValidSymArch sym arch => EquivM_ sym arch a

{-
withSubTraces ::
  forall nm sym arch a.
  IsTraceNode '(sym, arch) nm =>
  EquivSubTrace sym arch nm a ->
  EquivM sym arch a
withSubTraces (EquivSubTrace f) = do
  treeBuilder <- CMR.asks envTreeBuilder
  (node, nodeBuilder) <- IO.liftIO ((startNode treeBuilder) @nm )
  IO.liftIO $ addNode treeBuilder node
  r <- catchError
        (CMR.runReaderT f nodeBuilder >>= \r -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeStatus True)) >> return r)
        (\e -> (IO.liftIO $ updateNodeStatus nodeBuilder (NodeError (show e) True)) >> throwError e)
  return r

subTree ::
  forall nm sym arch a.
  IsTraceNode '(sym, arch) nm =>
  String ->
  EquivSubTrace sym arch nm a ->
  EquivM sym arch a
subTree lbl f =
  withSubTraces @"subtree" $
    subTrace @"subtree" lbl $
      withSubTraces @nm f

subTraceLabel ::
  forall nm sym arch a.
  IsTraceNode '(sym, arch) nm =>
  TraceNodeType '(sym, arch) nm ->
  TraceNodeLabel nm ->
  EquivM sym arch a ->
  EquivSubTrace sym arch nm a
subTraceLabel v lbl f = EquivSubTrace $ do
  nodeBuilder <- CMR.ask
  (subtree, treeBuilder) <- IO.liftIO $ startTree @'(sym, arch)
  IO.liftIO $ addNodeValue nodeBuilder lbl v subtree
  r <- CMR.lift $
    catchError
      (CMR.local (\env -> env { envTreeBuilder = treeBuilder }) $ (withValid $ f)
        >>= \r -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeStatus True)) >> return r)
      (\e -> (IO.liftIO $ updateTreeStatus treeBuilder (NodeError (show e) True)) >> throwError e)
  return r



emitTrace ::
  forall nm sym arch.
  IsTraceNode '(sym, arch) nm =>
  TraceNodeType '(sym, arch) nm ->
  Default (TraceNodeLabel nm) =>
  EquivM sym arch ()
emitTrace v = emitTraceLabel @nm def v

emitTraceLabel ::
  forall nm sym arch.
  IsTraceNode '(sym, arch) nm =>
  TraceNodeLabel nm ->
  TraceNodeType '(sym, arch) nm ->
  EquivM sym arch ()
emitTraceLabel lbl v = do
  treeBuilder <- CMR.asks envTreeBuilder
  node <- IO.liftIO $ singleNode @'(sym,arch) @nm lbl v
  IO.liftIO $ addNode treeBuilder node

-}

instance IsTraceNode (k :: l) "binary" where
  type TraceNodeType k "binary" = Some PBi.WhichBinaryRepr
  prettyNode () (Some wb) = PP.pretty (show wb)

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "bundle" where
  type TraceNodeType '(sym,arch) "bundle" = Some (SimBundle sym arch)
  prettyNode () (Some bundle) = "<TODO: pretty bundle>"
  nodeTags = [("symbolic", \_ _ -> "<TODO: pretty bundle>")]

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "blocktarget" where
  type TraceNodeType '(sym,arch) "blocktarget" = PPa.PatchPair (PB.BlockTarget arch)
  prettyNode () blkts = PP.pretty blkts

newtype ExprLabel = ExprLabel String
  deriving (Eq, Ord, Show)

instance Default ExprLabel where
  def = ExprLabel ""

instance IsString ExprLabel where
  fromString str = ExprLabel str


instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "expr" where
  type TraceNodeType '(sym,arch) "expr" = Some (W4.SymExpr sym)
  type TraceNodeLabel "expr" = ExprLabel
  
  prettyNode _lbl (Some e) = W4.printSymExpr e
  nodeTags = [(Summary, \(ExprLabel lbl) (Some e) ->
                  let pfx = case lbl of
                        "" -> ""
                        _ -> "(" <> PP.pretty lbl <> ") "
                      ls = lines (show (W4.printSymExpr e))
                  in case ls of
                    [] -> pfx
                    [a] -> pfx <> PP.pretty a
                    (a:as) -> pfx <> PP.pretty a <> ".." <> PP.pretty (last as)
              )]

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
getBinCtx' repr = PPa.getPair' repr <$> CMR.asks (PMC.binCtxs . envCtx)

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
  forall sym arch tp.
  (HasCallStack, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  [T.Text] ->
  MM.ArchReg arch tp ->
  EquivM sym arch (PSR.MacawRegVar sym tp)
unconstrainedRegister argNames reg = do
  let repr = MM.typeRepr reg
  case repr of
    MM.BVTypeRepr n
      | Just Refl <- testEquality n (MM.memWidthNatRepr @(MM.ArchAddrWidth arch)) -> withSymIO $ \sym -> do
          let margName = PA.argumentNameFrom argNames reg
          let name = maybe (showF reg) T.unpack margName
          ptr@(CLM.LLVMPointer region off) <- freshPtr sym name n
          let iRegion = W4.natToIntegerPure region
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
  Scoped f =>
  Scoped g =>
  (forall v. PEM.ExprMappable sym (f v)) =>
  PPa.BlockPair arch ->
  SimSpec sym arch f ->
  (forall v. SimScope sym arch v -> f v -> EquivM sym arch (g v)) ->
  EquivM sym arch (SimSpec sym arch g)
withSimSpec blocks spec f = withSym $ \sym -> do
  spec_fresh <- withFreshVars blocks $ \vars -> liftIO $ bindSpec sym vars spec
  forSpec spec_fresh $ \scope body ->
    withAssumptionSet (scopeAsm scope) (f scope body)

-- | Look up the arguments for this block slice if it is a function entry point
-- (and there are sufficient metadata hints)
lookupArgumentNames
  :: PPa.BlockPair arch
  -> EquivM sym arch [T.Text]
lookupArgumentNames pp = do
  let origEntryAddr = PB.concreteAddress (PPa.pOriginal pp)

  ctx <- CMR.asks envCtx
  let origCtx = PPa.pOriginal (PMC.binCtxs ctx)
  let funcHintIdx = PMC.functionHintIndex origCtx

  case M.lookup origEntryAddr funcHintIdx of
    Nothing -> return []
    Just fd -> return (PH.functionArguments fd)

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

-- | Create a new 'SimSpec' by evaluating the given function under a fresh set
-- of bound variables. The returned 'AssumptionSet' is set as the assumption
-- in the resulting 'SimSpec'.
withFreshVars ::
  forall sym arch f.
  Scoped f =>
  PPa.BlockPair arch ->
  (forall v. PPa.PatchPair (SimVars sym arch v) -> EquivM sym arch (AssumptionSet sym, (f v))) ->
  EquivM sym arch (SimSpec sym arch f)
withFreshVars blocks f = do
  argNames <- lookupArgumentNames blocks
  let
    mkMem :: forall bin. PBi.WhichBinaryRepr bin -> EquivM sym arch (MT.MemTraceImpl sym (MM.ArchAddrWidth arch))
    mkMem bin = do
      binCtx <- getBinCtx' bin
      let baseMem = MBL.memoryImage $ PMC.binary binCtx
      withSymIO $ \sym -> MT.initMemTrace sym baseMem (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))

    mkStackBase :: forall v. EquivM sym arch (StackBase sym arch v)
    mkStackBase = withSymIO $ \sym -> freshStackBase sym (Proxy @arch)

    mkMaxRegion :: forall v. EquivM sym arch (ScopedExpr sym v W4.BaseIntegerType)
    mkMaxRegion = withSymIO $ \sym -> liftScope0 sym $ \sym' ->
      W4.freshConstant sym' (W4.safeSymbol "max_region") W4.BaseIntegerRepr

  freshSimSpec (\_ r -> unconstrainedRegister argNames r) (\x -> mkMem x) (\_ -> mkStackBase) (\_ -> mkMaxRegion) (\v -> f v)
  
-- | Evaluate the given function in an assumption context augmented with the given
-- 'AssumptionSet'.
withAssumptionSet ::
  HasCallStack =>
  AssumptionSet sym ->
  EquivM_ sym arch f ->
  EquivM sym arch f
withAssumptionSet asm f = withSym $ \sym -> do
  curAsm <- currentAsm
  p <- liftIO $ PAS.toPred sym asm
  case PAS.isAssumedPred curAsm p of
    True -> f
    _ -> CMR.local (\env -> env { envCurrentFrame = (asm <> curAsm) }) $ do
      (frame, st) <- withOnlineBackend $ \bak ->  do
        st <- liftIO $ LCB.saveAssumptionState bak
        frame <- liftIO $ LCB.pushAssumptionFrame bak
        safeIO (\_ -> PEE.AssumedFalse curAsm asm) $
          LCB.addAssumption bak (LCB.GenericAssumption initializationLoc "withAssumptionSet" p)
        return (frame, st)
      (f >>= \r -> validateAssumptions curAsm asm >> return r)
        `finally` safePop frame st

-- | try to pop the assumption frame, but restore the solver state
--   if this fails
safePop ::
  LCB.FrameIdentifier ->
  LCB.AssumptionState sym ->
  EquivM sym arch ()
safePop frame st = withOnlineBackend $ \bak -> 
  catchError
    (safeIO (\_ -> PEE.SolverStackMisalignment) (LCB.popAssumptionFrame bak frame >> return ()))
    (\_ -> safeIO (\_ -> PEE.SolverStackMisalignment) (LCBO.restoreSolverState bak st))   

-- | Validates the current set of assumptions by checking that some model exists
-- under the current assumption context.
-- Takes the original assumption set and the recently-pushed assumption set, which
-- is used for reporting in the case that the resulting assumption state is found to
-- be inconsistent.
validateAssumptions ::
  forall sym arch. 
  HasCallStack =>
  AssumptionSet sym {- ^ original assumption set -} ->
  AssumptionSet sym {- ^ recently pushed assumption set -} ->
  EquivM sym arch ()
validateAssumptions oldAsm newAsm = withSym $ \sym -> do
  let
    simp :: forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)
    simp e = resolveConcreteLookups sym (pure . W4.asConstantPred) e  >>= simplifyBVOps sym >>= expandMuxEquality sym

  oldAsm' <- liftIO $ PEM.mapExpr sym simp oldAsm
  newAsm' <- liftIO $ PEM.mapExpr sym simp newAsm  
  goalSat "validateAssumptions" (W4.truePred sym) $ \res -> case res of
    W4R.Unsat _ -> throwHere $ PEE.AssumedFalse oldAsm' newAsm'
    W4R.Unknown -> throwHere $ PEE.AssumedFalse oldAsm' newAsm'
    W4R.Sat{} -> return ()

-- | Evaluate the given function in an assumption context augmented with the given
-- predicate.
withAssumption ::
  HasCallStack =>
  W4.Pred sym ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption asm f = withAssumptionSet (PAS.fromPred asm) f

-- | Rewrite the given 'f' with any bindings in the current 'AssumptionSet'
-- (set when evaluating under 'withAssumptionSet' and 'withAssumption').
applyCurrentAsms ::
  forall sym arch f.
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
applyCurrentAsms f = withSym $ \sym -> do
  asm <- currentAsm
  PAS.apply sym asm f

instance ValidSymArch sym arch => IsTraceNode '(sym,arch) "satAssumption" where
  type TraceNodeType '(sym,arch) "satAssumption" = AssumptionSet sym
  prettyNode () asm = "Satisfiable" PP.<+> PP.pretty asm
  nodeTags = [("solver", \_ -> PP.pretty)]

-- | First check if an assumption is satisfiable before assuming it. If it is not
-- satisfiable, return Nothing.
withSatAssumption ::
  HasCallStack =>
  AssumptionSet sym ->
  EquivM_ sym arch f ->
  EquivM sym arch (Maybe f)
withSatAssumption asm f = withSym $ \sym -> do
  emitTrace @"satAssumption" asm
  p <- liftIO $ PAS.toPred sym asm
  case W4.asConstantPred p of
    Just False -> return Nothing
    Just True -> Just <$> f
    _ -> do
      curAsm <- currentAsm
      CMR.local (\env -> env { envCurrentFrame = (asm <> curAsm) }) $ do
        mst <- withOnlineBackend $ \bak -> do
          st <- liftIO $ LCB.saveAssumptionState bak
          frame <- liftIO $  LCB.pushAssumptionFrame bak
          catchError (safeIO (\_ -> PEE.AssumedFalse curAsm asm)
            (do
                LCB.addAssumption bak (LCB.GenericAssumption initializationLoc "withAssumptionSet" p)
                return $ Just (frame, st)))
            (\_ -> (liftIO $ LCB.popAssumptionFrame bak frame) >> return Nothing)
        case mst of
          Just (frame, st) ->
            (goalSat "check assumptions" (W4.truePred sym) $ \res -> case res of
              W4R.Sat{} -> Just <$> f
              -- on an inconclusive result we can't safely return 'Nothing' since
              -- that may unsoundly exclude viable paths
              W4R.Unknown -> throwHere $ PEE.InconclusiveSAT
              W4R.Unsat{} -> return Nothing)
                `finally` safePop frame st
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
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  checkSatisfiableWithModel heuristicTimeout desc p k >>= \case
    Left _err -> k W4R.Unknown
    Right a -> return a


-- | Concretize a symbolic expression in the current assumption context
concretizeWithSolver ::
  W4.SymExpr sym tp ->
  EquivM sym arch (W4.SymExpr sym tp)
concretizeWithSolver e = withSym $ \sym -> do
  
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  let wsolver = PVC.WrappedSolver sym $ \_desc p k -> do
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
  st <- withOnlineBackend $ \bak -> liftIO $ LCB.saveAssumptionState bak
  mres <- withSolverProcess $ \sp -> liftIO $ do
    WPO.push sp
    W4.assume (WPO.solverConn sp) p
    tryJust filterAsync $ do
      res <- checkSatisfiableWithoutBindings timeout sym desc $ WPO.checkAndGetModel sp "checkSatisfiableWithModel"
      W4R.traverseSatResult (\r' -> pure $ SymGroundEvalFn r') pure res
  case mres of
    Left err -> withOnlineBackend $ \bak -> do
      --FIXME: for some reason the first attempt sometimes fails and we need to try again
      _ <- liftIO $ tryJust filterAsync (LCBO.restoreSolverState bak st)
      withSolverProcess $ \_ -> do
        liftIO $ LCBO.restoreSolverState bak st
        return $ Left err
    Right res -> withOnlineBackend $ \bak -> withSolverProcess $ \sp -> do
      fmap Right $ k res `finally`
        catchError (safeIO (\_ -> PEE.SolverStackMisalignment) (WPO.pop sp))
          (\_ -> safeIO (\_ -> PEE.SolverStackMisalignment) (LCBO.restoreSolverState bak st))

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
isPredSat timeout p = case W4.asConstantPred p of
  Just b -> return b
  Nothing -> either (const False) id <$> checkSatisfiableWithModel timeout "isPredSat" p (\x -> asSat x)

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
        -- Convert exceptions into False because we can't prove that it is true
        res <- checkSatisfiableWithModel timeout "isPredTrue'" notp (\x -> asProve x)
        case res of
          Left _ex -> return False -- TODO!!! This swallows the exception!
          Right x -> return x

concretePred ::
  HasCallStack =>
  PT.Timeout ->
  W4.Pred sym ->
  EquivM sym arch (Maybe Bool)
concretePred timeout p = case W4.asConstantPred p of
  Just b -> return $ Just b
  _ -> do
    
    notp <- withSymIO $ \sym -> W4.notPred sym p
    r <- checkSatisfiableWithModel timeout "concretePred" notp $ \res ->
      case res of
        W4R.Sat{} -> return $ Just False
        W4R.Unsat{} -> return $ Just True
        W4R.Unknown -> return $ Nothing
    case r of
      Left _ex -> return Nothing
      Right (Just True) -> return $ Just True
      Right Nothing -> return Nothing
      -- the predicate is maybe false, but not necessarily false
      Right (Just False) -> do
        r' <- checkSatisfiableWithModel timeout "concretePred" p $ \res ->
          case res of
            -- p can be true or false
            W4R.Sat{} -> return Nothing
            -- p is necessarily false
            W4R.Unsat{} -> return $ Just False
            W4R.Unknown -> return $ Nothing
        case r' of
          Left _ex -> return Nothing
          Right x -> return x

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
    Nothing -> throwHere PEE.InvalidSMTModel

getFootprints ::
  SimBundle sym arch v ->
  EquivM sym arch (Set (MT.MemFootprint sym (MM.ArchAddrWidth arch)))
getFootprints bundle = withSym $ \sym -> do
  footO <- liftIO $ MT.traceFootprint sym (simOutMem $ simOutO bundle)
  footP <- liftIO $ MT.traceFootprint sym (simOutMem $ simOutP bundle)
  return $ S.union footO footP

-- | Update 'envCurrentFunc' if the given pair is a function entry point
withPair :: PPa.BlockPair arch -> EquivM sym arch a -> EquivM sym arch a
withPair pPair f = do
  env <- CMR.ask
  let env' = env { envParentBlocks = pPair:envParentBlocks env }
  let entryPair = fmapF (\b -> PB.functionEntryToConcreteBlock (PB.blockFunctionEntry b)) pPair
  CMR.local (\_ -> env' & PME.envCtxL . PMC.currentFunc .~ entryPair) f

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
  => SimBundle sym arch v
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
    env <- CMR.ask
    catchInIO (f (\x -> runEquivM env x >>= \case
                     Left err -> throwIO err
                     Right r -> return r))

catchInIO ::
  forall sym arch a.
  IO a ->
  EquivM sym arch a
catchInIO f =
  (liftIO $ catch (Right <$> f) (\(e :: PEE.EquivalenceError) -> return $ Left e)) >>= \case
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

runEquivM ::
  forall sym arch a.
  EquivEnv sym arch ->
  EquivM sym arch a ->
  IO (Either PEE.EquivalenceError a)
runEquivM env f = withValidEnv env $ runExceptT $ (CMR.runReaderT (unEQ f) env)

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
