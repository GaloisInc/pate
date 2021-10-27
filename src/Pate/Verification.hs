{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  ) where

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( (&), (.~) )
import           Control.Monad ( void, unless )
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Trans as CMT
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Time as TM
import qualified Data.Traversable as DT
import           GHC.Stack ( HasCallStack )
import qualified Lumberjack as LJ
import           Prelude hiding ( fail )
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Backend.Simple as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Arch as PA
import qualified Pate.Abort as PAb
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import           Pate.Proof.Ground as PFG
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Proof.Operations as PFO
import           Pate.SimState
import qualified Pate.Solver as PS
import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.Simplify as PVSi
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.Validity as PVV
import           What4.ExprHelpers

-- | Run code discovery using macaw
--
-- We run discovery in parallel, since we need to run it two to four times.
--
-- If we have hints for a binary (original or patched), we run discovery twice:
-- with and without hints. We then compare the two and report any discrepancies
-- that indicate that the hints could be wrong.
--
-- We report any errors in the hints:
--
-- * Hints that point to non-code data (bad)
--
-- * Hints not appearing in our discovery (good)
--
-- We use the hinted results (if any)
runDiscovery
  :: (PA.ValidArch arch)
  => LJ.LogAction IO (PE.Event arch)
  -> Maybe FilePath
  -- ^ Directory to save macaw CFGs to
  -> PH.Hinted (PLE.LoadedELF arch)
  -> PH.Hinted (PLE.LoadedELF arch)
  -> CME.ExceptT (PEE.EquivalenceError arch) IO (PPa.PatchPair (PMC.BinaryContext arch))
runDiscovery logAction mCFGDir elf elf' = do
  binCtxO <- discoverCheckingHints PBi.OriginalRepr elf
  binCtxP <- discoverCheckingHints PBi.PatchedRepr elf'
  liftIO $ LJ.writeLog logAction (PE.LoadedBinaries (PH.hinted elf, PMC.parsedFunctionMap binCtxO) (PH.hinted elf', PMC.parsedFunctionMap binCtxP))
  return $ PPa.PatchPair binCtxO binCtxP
  where
    discoverAsync mdir repr e h = liftIO (CCA.async (CME.runExceptT (PD.runDiscovery mdir repr e h)))
    discoverCheckingHints repr e = do
      if | PH.hints e == mempty -> do
             unhintedAnalysis <- discoverAsync mCFGDir repr (PH.hinted e) mempty
             (_, oCtxUnhinted) <- CME.liftEither =<< liftIO (CCA.wait unhintedAnalysis)
             return oCtxUnhinted
         | otherwise -> do
             unhintedAnalysis <- discoverAsync Nothing repr (PH.hinted e) mempty
             hintedAnalysis <- discoverAsync mCFGDir repr (PH.hinted e) (PH.hints e)
             (_, oCtxUnhinted) <- CME.liftEither =<< liftIO (CCA.wait unhintedAnalysis)
             (hintErrors, oCtxHinted) <- CME.liftEither =<< liftIO (CCA.wait hintedAnalysis)

             unless (null hintErrors) $ do
               let invalidSet = S.fromList hintErrors
               let invalidEntries = [ (name, addr)
                                    | (name, fd) <- PH.functionEntries (PH.hints e)
                                    , let addr = PH.functionAddress fd
                                    , S.member addr invalidSet
                                    ]
               liftIO $ LJ.writeLog logAction (PE.FunctionEntryInvalidHints repr invalidEntries)

             let unhintedDiscoveredAddresses = S.fromList (PMC.parsedFunctionEntries (PMC.parsedFunctionMap oCtxUnhinted))
             let hintedDiscoveredAddresses = S.fromList (PMC.parsedFunctionEntries (PMC.parsedFunctionMap oCtxHinted))
             let newAddrs = hintedDiscoveredAddresses `S.difference` unhintedDiscoveredAddresses
             unless (S.null newAddrs) $ do
               liftIO $ LJ.writeLog logAction (PE.FunctionsDiscoveredFromHints repr (F.toList newAddrs))
             return oCtxHinted

-- | Verify equality of the given binaries.
verifyPairs ::
  forall arch.
  PA.ValidArch arch =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PC.VerificationConfig ->
  [PPa.BlockPair arch] ->
  CME.ExceptT (PEE.EquivalenceError arch) IO PEq.EquivalenceStatus
verifyPairs validArch@(PA.SomeValidArch _ _ hdr) logAction elf elf' vcfg pPairs = do
  startTime <- liftIO TM.getCurrentTime
  Some gen <- liftIO N.newIONonceGenerator
  vals <- case MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) of
    Nothing -> CME.throwError $ PEE.equivalenceError PEE.UnsupportedArchitecture
    Just vs -> pure vs
  ha <- liftIO CFH.newHandleAllocator
  contexts <- runDiscovery logAction (PC.cfgMacawDir vcfg) elf elf'

  sym <- liftIO $ CB.newSimpleBackend W4B.FloatRealRepr gen
  adapter <- liftIO $ PS.solverAdapter sym (PC.cfgSolver vcfg)

  eval <- CMT.lift (MS.withArchEval vals sym pure)
  model <- CMT.lift (MT.mkMemTraceVar @arch ha)
  bvar <- CMT.lift (CC.freshGlobalVar ha (T.pack "block_end") W4.knownRepr)
  undefops <- liftIO $ MT.mkUndefinedPtrOps sym

  -- PC values are assumed to be absolute
  pcRegion <- liftIO $ W4.natLit sym 0

  -- we arbitrarily assign disjoint regions for each area of memory
  stackRegion <- liftIO $ W4.natLit sym 1
  globalRegion <- liftIO $ W4.natLit sym 2

  startedAt <- liftIO TM.getCurrentTime
  topNonce <- liftIO $ (PF.ProofNonce <$> N.freshNonce gen)

  -- NOTE: This is using the global nonce generator because it gets sunk down
  -- into contexts where the scope type parameter is quantified out in ways that
  -- are not practical to recover without major refactoring.  This is just as
  -- safe but makes things significantly easier.
  symNonce <- liftIO (N.freshNonce N.globalNonceGenerator)
  prfCache <- liftIO $ freshBlockCache
  ePairCache <- liftIO $ freshBlockCache
  statsVar <- liftIO $ MVar.newMVar mempty
  let
    exts = MT.macawTraceExtensions eval model (trivialGlobalMap @_ @arch) undefops

    ctxt = PMC.EquivalenceContext
      { PMC.handles = ha
      , PMC.binCtxs = contexts
      , PMC.stackRegion = stackRegion
      , PMC.globalRegion = globalRegion
      , PMC._currentFunc = error "No function under analysis at startup"
      }
    env = EquivEnv
      { envWhichBinary = Nothing
      , envValidArch = validArch
      , envCtx = ctxt
      , envArchVals = vals
      , envExtensions = exts
      , envPCRegion = pcRegion
      , envMemTraceVar = model
      , envBlockEndVar = bvar
      , envLogger = logAction
      , envConfig = vcfg
      , envBaseEquiv = stateEquivalence hdr sym stackRegion
      , envFailureMode = PME.ThrowOnAnyFailure
      , envGoalTriples = [] -- populated in runVerificationLoop
      , envValidSym = PS.Sym symNonce sym adapter
      , envStartTime = startedAt
      , envCurrentFrame = mempty
      , envNonceGenerator = gen
      , envParentNonce = Some topNonce
      , envUndefPointerOps = undefops
      , envParentBlocks = mempty
      , envProofCache = prfCache
      , envExitPairsCache = ePairCache
      , envStatistics = statsVar
      }

  liftIO $ do
    (result, stats) <- runVerificationLoop env pPairs
    endTime <- TM.getCurrentTime
    let duration = TM.diffUTCTime endTime startTime
    IO.liftIO $ LJ.writeLog logAction (PE.AnalysisEnd stats duration)
    return $ result

---------------------------------------------
-- Top-level loop

-- | Verify equivalence of the given function pairs.
--
-- The set of "goal" triples (pre-domain, block, and post-domain) is defined by the 'envGoalTriples' field of the underlying
-- 'EquivEnv'. This is initially populated by the given list of function pairs (i.e. function
-- we explicitly want to check the equivalence of), as well as the main entry points for
-- each program (given that 'cfgPairMain' is set on the 'DiscoveryConfig' of the given 'EquivEnv').
--
-- Each "triple" represents an equivalence pre-domain (exact equivalence on the entire machine state,
-- by default, for all the given pairs), a pair of functions,
-- and a post-domain (exact equivalence on global memory, by default).
--
-- Verification proceeds by taking some goal triple an attempting to verify its equivalence.
-- This occurs through a bottom-up analysis of all the intermediate blocks between the start of
-- the function and all possible exits. This traversal is defined by 'checkEquivalence', which
-- either returns normally on success or throws an error if equivalence cannot be proven.
--
-- After a check is completed, the open triple is removed from  and either added to the set
-- of "successful" proofs (i.e. 'stProvenTriples') or "failed" proofs ('stFailedTriples').
-- The next open triple is then popped from 'stOpenTriples' and checked, repeating until
-- no open triples are left.
--
-- Currently the set of open triples is unchanged during 'checkEquivalence':
-- emerging problems are internally solved by a recursive descent rather than this loop.
-- This traversal is therefore more complicated than strictly necessary, however it supports
-- the likely future requirement for equivalence checks to emit deferred equivalence
runVerificationLoop ::
  forall sym arch.
  EquivEnv sym arch ->
  -- | A list of block pairs to test for equivalence. They must be the start of a function.
  [PPa.BlockPair arch] ->
  IO (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
runVerificationLoop env pPairs = do
  result <- CME.runExceptT $ runEquivM env doVerify
  case result of
    Left err -> withValidEnv env $ error (show err)
    Right r -> return r

  where
    doVerify :: EquivM sym arch (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
    doVerify = do
      pPairs' <- ifConfig (not . PC.cfgPairMain) (return pPairs) $ do
        mainO <- CMR.asks $ PMC.binEntry . PPa.pOriginal . PMC.binCtxs . envCtx
        mainP <- CMR.asks $ PMC.binEntry . PPa.pPatched . PMC.binCtxs . envCtx
        let blkO = PB.concreteEntryPoint mainO PBi.OriginalRepr
        let blkP = PB.concreteEntryPoint mainP PBi.PatchedRepr
        let pPair = PPa.PatchPair blkO blkP
        return $ pPair : pPairs
      triples <- DT.forM pPairs' $ topLevelTriple
      result <- CMR.local (\env' -> env' { envGoalTriples = triples } ) $
        CME.foldM (\a b -> (<>) a <$> go b) mempty triples
      statVar <- CMR.asks envStatistics
      stats <- liftIO $ MVar.readMVar statVar
      return (result, stats)

    go ::
      PF.EquivTriple sym arch -> EquivM sym arch PEq.EquivalenceStatus
    go triple = do
      result <- manifestError $ checkEquivalence triple
      emitResult result
      normResult <- return $ case result of
        Right PEq.Equivalent -> PESt.EquivalenceStatistics 1 1 0
        Left _ -> PESt.EquivalenceStatistics 1 0 1
        Right _ -> PESt.EquivalenceStatistics 1 0 0
      statVar <- CMR.asks envStatistics
      liftIO $ MVar.modifyMVar_ statVar (\st -> return (normResult <> st))
      case result of
        Right r -> return r
        Left err -> return (Errored (show err))

emitPreamble :: PPa.BlockPair arch -> EquivM sym arch ()
emitPreamble pPair = emitEvent (\_ -> PE.AnalysisStart pPair)

emitResult :: Either (PEE.EquivalenceError arch) a -> EquivM sym arch ()
emitResult (Left err) = emitEvent (\_ -> PE.ErrorRaised err)
emitResult (Right _) = return ()

-- | Verify that the given triple: that a pair of blocks yield equivalent
-- states on the post-domain, assuming equality on the pre-domain.
-- Returns 'True' if the pairs are proven equivalent, and 'False' if
-- the generated proof contains an inequivalence counterexample.
checkEquivalence ::
  HasCallStack =>
  PF.EquivTriple sym arch ->
  EquivM sym arch PEq.EquivalenceStatus
checkEquivalence triple = startTimer $ withSym $ \sym -> do
  withValid @() $ liftIO $ W4B.startCaching sym
  eqRel <- CMR.asks envBaseEquiv
  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  -- first try proving equivalence by assuming that exact equality
  -- is the only condition we are propagating backwards, so we
  -- don't do any work to try to intelligently narrow this down

  -- TODO: it's unclear how fine-grained to make this, or if it's even
  -- a good idea, but it makes the tests finish in about 1/3 the time
  let doProof = do
        (genPrecond, proof) <- provePostcondition pPair postcondSpec
        proof_final <- PFO.joinLazyProof proof
        return $ (genPrecond, proof_final)

  (genPrecondSpec, proof) <- ifConfig PC.cfgComputeEquivalenceFrames doProof $ do
    (spec, proof) <- doProof
    -- if the previous attempt fails, fall back to intelligent precondition
    -- propagation
    -- FIXME: this should fail early, rather than waiting for the entire proof result
    case PFO.proofResult (PF.unNonceProof proof) of
      PF.VerificationSuccess -> return (spec, proof)
      _ -> 
        CMR.local (\env -> env { envConfig = (envConfig env){PC.cfgComputeEquivalenceFrames = True} }) $
          doProof

  void $ withSimSpec pPair triple $ \stO stP tripleBody -> do
    let
      inO = SimInput stO (PPa.pOriginal pPair)
      inP = SimInput stP (PPa.pPatched pPair)
      precond = PF.eqPreDomain tripleBody
    (_, genPrecond) <- liftIO $ bindSpec sym stO stP genPrecondSpec
    preImpliesGen <- liftIO $ impliesPrecondition sym stackRegion inO inP eqRel precond genPrecond
    -- prove that the generated precondition is implied by the given precondition
    goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
    isPredTrue' goalTimeout preImpliesGen >>= \case
      True -> return ()
      False -> throwHere PEE.ImpossibleEquivalence

    -- prove any generated side conditions
    -- FIXME: this is largely redundant currently, since we aren't propagating these backwards
    -- this fails since the concrete assertions about memory can't be proven at this level
    --isPredTrue asms >>= \case
    -- True -> return ()
    --  False -> throwHere UnsatisfiableAssumptions
  vsym <- CMR.asks envValidSym
  blocks <- PD.getBlocks pPair
  ifConfig (not . PC.cfgEmitProofs) (return ()) $ do
    emitEvent (PE.ProvenGoal blocks (PFI.SomeProofSym vsym proof))
  case PFO.proofResult (PF.unNonceProof proof) of
    PF.VerificationSuccess -> return PEq.Equivalent
    PF.VerificationFail (_, cond) -> case W4.asConstantPred (PFI.condEqPred cond) of
      Just False -> return PEq.Inequivalent
      _ -> return PEq.ConditionallyEquivalent
    _ -> return PEq.Inequivalent
  where
    -- TODO: this breaks the model somewhat, since we're relying on these not containing
    -- the bound terms
    pPair = PF.eqPair $ specBody triple
    postcondSpec = PF.eqPostDomain $ specBody triple
  
--------------------------------------------------------
-- Simulation



-- | Simulate the given block pair, or retrieve a cached result from a previous
-- simulation. Execute the given function in a context where the given 'SimBundle'
-- is valid (i.e. its bound variables are marked free and its preconditions are assumed).
withSimBundle ::
  (HasCallStack, PEM.ExprMappable sym f) =>
  PPa.BlockPair arch ->
  (SimBundle sym arch -> EquivM sym arch f) ->
  EquivM sym arch (SimSpec sym arch f)
withSimBundle pPair f = withEmptyAssumptionFrame $ withSym $ \sym -> do
  withFreshVars pPair $ \stO stP -> do
    let
      simInO_ = SimInput stO (PPa.pOriginal pPair)
      simInP_ = SimInput stP (PPa.pPatched pPair)

    withAssumptionFrame' (PVV.validInitState (Just pPair) stO stP) $ do
      traceBlockPair pPair "Simulating original blocks"
      (asmO, simOutO_) <- PVSy.simulate simInO_
      traceBlockPair pPair "Simulating patched blocks"
      (asmP, simOutP_) <- PVSy.simulate simInP_
      traceBlockPair pPair "Finished simulating blocks"
      (_, simOutO') <- withAssumptionFrame (PVV.validConcreteReads simOutO_) $ return simOutO_
      (_, simOutP') <- withAssumptionFrame (PVV.validConcreteReads simOutP_) $ return simOutP_

      (asm,r) <- withAssumption (liftIO $ allPreds sym [asmO, asmP]) $ do
        let bundle = SimBundle (PPa.PatchPair simInO_ simInP_) (PPa.PatchPair simOutO' simOutP')
        bundle' <- applyCurrentFrame bundle
        f bundle'
      return (frameAssume asm, r)

trivialGlobalMap :: MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap _ _ reg off = pure (CLM.LLVMPointer reg off)

--------------------------------------------------------
-- Proving equivalence

-- | Update 'envCurrentFunc' if the given pair 
withPair :: PPa.BlockPair arch -> EquivM sym arch a -> EquivM sym arch a
withPair pPair f = do
  env <- CMR.ask
  let env' = env { envParentBlocks = pPair:envParentBlocks env }
  case PB.concreteBlockEntry $ PPa.pOriginal pPair of
    PB.BlockEntryInitFunction -> CMR.local (\_ -> env' & PME.envCtxL . PMC.currentFunc .~ pPair) f
    _ -> CMR.local (\_ -> env') f

provePostcondition ::
  HasCallStack =>
  PPa.BlockPair arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
provePostcondition pPair postcondSpec = do
  traceBlockPair pPair "Entering provePostcondition"
  emitPreamble pPair
  catchSimBundle pPair postcondSpec $ \bundle ->
    provePostcondition' bundle postcondSpec

catchSimBundle ::
  forall sym arch ret.
  (HasCallStack, ret ~ (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)) =>
  PPa.BlockPair arch ->
  StatePredSpec sym arch ->
  (SimBundle sym arch -> EquivM sym arch (PES.StatePred sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)  ) ->
  EquivM sym arch ret
catchSimBundle pPair postcondSpec f = do
  pblks <- CMR.asks envParentBlocks
  cached <- concat <$> lookupBlockCache envProofCache pPair
  firstCached cached >>= \case
    Just r -> return r
    Nothing -> withPair pPair $ do
      traceBlockPair pPair ("catchSimBundle parent blocks: " ++ show pblks)
      (precondSpec, prf) <- case elem pPair pblks of
        True -> do
          traceBlockPair pPair "Loop detected"
          errorResult
        False -> (manifestError $ withSimBundle pPair $ f) >>= \case
          Left err -> do
            traceBlockPair pPair ("Caught error: " ++ show err)
            errorResult
          Right r -> return $ unzipProof r
      let triple = fmap (\precond -> PF.EquivTripleBody pPair precond postcondSpec) precondSpec
      future <- PFO.asFutureNonceApp prf
      modifyBlockCache envProofCache pPair (++) [(triple, future)]
      return $ (precondSpec, prf)
  where
    firstCached (x:xs) = getCached x >>= \case
      Just r -> return $ Just r
      Nothing -> firstCached xs
    firstCached [] = return Nothing
    
    getCached ::
      (PF.EquivTriple sym arch, Par.Future (PFI.ProofSymNonceApp sym arch PF.ProofBlockSliceType)) ->
      EquivM sym arch (Maybe ret)
    getCached (triple, futureProof) = do
      traceBlockPair pPair "Checking for cached result"
      impliesPostcond pPair (PF.eqPostDomain $ specBody triple) postcondSpec >>= \case
        True -> do
          traceBlockPair pPair "Cache hit"
          prf' <- PFO.wrapFutureNonceApp futureProof
          return $ Just (fmap PF.eqPreDomain triple, prf')
        False -> do
          traceBlockPair pPair "Cache miss"
          return Nothing

    errorResult :: EquivM sym arch ret
    errorResult = fmap unzipProof $ withSym $ \sym -> withFreshVars pPair $ \stO stP -> do
      let
        simInO_ = SimInput stO (PPa.pOriginal pPair)
        simInP_ = SimInput stP (PPa.pPatched pPair)
      traceBlockPair pPair "Caught an error, so making a trivial block slice"
      PA.SomeValidArch _ externalDomain _ <- CMR.asks envValidArch
      r <- trivialBlockSlice False externalDomain (PPa.PatchPair simInO_ simInP_) postcondSpec
      return $ (W4.truePred sym, r)

impliesPostcond ::
  PPa.BlockPair arch ->
  StatePredSpec sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch Bool
impliesPostcond blocks stPredAsm stPredConcl = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  fmap specBody $ withFreshVars blocks $ \stO stP -> do
    p <- liftIO $ impliesPostcondPred sym (PPa.PatchPair stO stP) stPredAsm stPredConcl
    b <- isPredTrue' heuristicTimeout p
    return $ (W4.truePred sym, b)

data BranchCase sym arch =
  BranchCase
    { -- | predicate that asserts equality on the pre-state, derived
      -- from the 'branchPreStPred' but stored here to avoid re-computing it
      branchPrePred :: W4.Pred sym
      -- | the structured pre-domain for this branch
    , branchPreDomain :: PES.StatePred sym arch
      -- | target for the function call
    , branchBlocks :: PPa.BlockPair arch
      -- | the deferred proof that the pre-domain is sufficient to establish
      -- the target post-domain
    , branchProofTriple :: PFO.LazyProof sym arch PF.ProofTripleType
    }

unzipProof ::
  SimSpec sym arch (f, PFO.LazyProof sym arch tp) ->
  (SimSpec sym arch f, PFO.LazyProof sym arch tp)
unzipProof spec = (fmap fst spec, snd $ specBody spec)

-- | Emits a skipped equivalence proof for a block slice that assumes
-- the post-domain is equivalent if the pre-domain is exactly equivalent.
-- Currently this is used to model syscalls, since we don't have a more precise
-- semantics to decide the conditions under which they are equivalent.
trivialBlockSlice ::
  forall sym arch callk .
  Bool  ->
  PVE.ExternalDomain callk arch ->
  PPa.PatchPair (SimInput sym arch) ->
  StatePredSpec sym arch ->
  EquivM sym arch (PES.StatePred sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
trivialBlockSlice isSkipped (PVE.ExternalDomain externalDomain) in_ postcondSpec = withSym $ \sym -> do
  blkEnd <- liftIO $ MS.initBlockEnd (Proxy @arch) sym
  transition <- PFO.noTransition in_ blkEnd
  preUniv <- externalDomain sym
  prf <- PFO.lazyProofEvent_ pPair $ do
    triple <- PFO.lazyProofEvent_ pPair $ do
      preDomain <- fmap PFO.asLazyProof $ PFO.proofNonceExpr $
         PF.appDomain <$> PFO.statePredToDomain (TF.fmapF simInState in_) preUniv
      postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
      status <- PFO.lazyProofApp $ case isSkipped of
        True -> PF.ProofStatus PF.VerificationSkipped
        False -> PF.ProofStatus PF.Unverified
      return $ PF.ProofTriple pPair preDomain postDomain status
    return $ PF.ProofBlockSlice triple [] Nothing Nothing transition
  return (preUniv, prf)
  where
    pPair :: PPa.BlockPair arch
    pPair = TF.fmapF simInBlock in_

-- | Prove that a postcondition holds for a function pair starting at
-- this address. The return result is the computed pre-domain, tupled with a lazy
-- proof result that, once evaluated, represents the proof tree that verifies
-- the given block slices are equivalent.
provePostcondition' ::
  forall sym arch.
  HasCallStack =>
  SimBundle sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (PES.StatePred sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
provePostcondition' bundle postcondSpec = PFO.lazyProofEvent (simPair bundle) $ withSym $ \sym -> do
  traceBundle bundle "Entering provePostcondition"
  pairs <- PD.discoverPairs bundle
  traceBundle bundle (show (length pairs) ++ " pairs found!")
  -- find all possible exits and propagate the postcondition backwards from them
  funCallProofCases <- DT.forM (zip [0 :: Int ..] pairs) $ \(idx, PPa.PatchPair blktO blktP) ->  do
    traceBundle bundle ("Handling proof case " ++ show idx)
    withAssumption (PD.matchesBlockTarget bundle blktO blktP) $
      PFO.lazyProofEvent (simPair bundle) $ do
      let
        blkO = PB.targetCall blktO
        blkP = PB.targetCall blktP
        pPair = PPa.PatchPair blkO blkP
      traceBundle bundle ("  targetCall: " ++ show blkO)
      case (PB.targetReturn blktO, PB.targetReturn blktP) of
        (Just blkRetO, Just blkRetP) -> do
          traceBundle bundle ("  Return target " ++ show blkRetO)
          isSyscall <- case (PB.concreteBlockEntry blkO, PB.concreteBlockEntry blkP) of
            (PB.BlockEntryPostArch, PB.BlockEntryPostArch) -> return True
            (entryO, entryP) | entryO == entryP -> return False
            _ -> throwHere $ PEE.BlockExitMismatch
          traceBundle bundle ("  Is Syscall? " ++ show isSyscall)
          withNoFrameGuessing isSyscall $ do
            (contPre, contPrf) <- provePostcondition (PPa.PatchPair blkRetO blkRetP) postcondSpec
            traceBundle bundle "finished proving postcondition"
            (funCallPre, funCallSlicePrf) <- catchSimBundle pPair postcondSpec $ \bundleCall -> do
              -- equivalence condition for when this function returns
              case isSyscall of
                -- for arch exits (i.e. syscalls) we assume that equivalence will hold on
                -- any post domain if the pre-domain is exactly equal: i.e. any syscall is
                -- treated as an uninterpreted function that reads the entire machine state
                -- this can be relaxed with more information about the specific call
                True -> do
                  traceBundle bundle ("  Making a trivial block slice because this is a system call")
                  PA.SomeValidArch syscallDomain _ _ <- CMR.asks envValidArch
                  trivialBlockSlice True syscallDomain (simIn bundle) postcondSpec
                False -> do
                  traceBundle bundle "  Not a syscall, emitting preamble pair"
                  emitPreamble pPair
                  -- equivalence condition for calling this function
                  traceBundle bundle "  Recursively proving the postcondition of the call target"
                  provePostcondition' bundleCall contPre

            -- equivalence condition for the function entry
            traceBundle bundle "Proving local postcondition for call return"
            branchCase <- proveLocalPostcondition bundle funCallPre
            traceBundle bundle "Generating a ProofFunctionCall obligation"
            let
              md = PF.ProofFunctionCallMetadata { PF.prfFunctionCallMetadataAddress = PB.concreteAddress blkO
                                                }
              prf = PF.ProofFunctionCall
                      { PF.prfFunctionCallPre = branchProofTriple branchCase
                      , PF.prfFunctionCallBody = funCallSlicePrf
                      , PF.prfFunctionCallContinue = Just contPrf
                      , PF.prfFunctionCallMetadata = md
                      }
            return (branchCase, prf)

        (Nothing, Nothing) -> do
          traceBundle bundle "No return target identified"
          (contPre, contPrf) <- provePostcondition (PPa.PatchPair blkO blkP) postcondSpec
          branchCase <- proveLocalPostcondition bundle contPre
          let
            md = PF.ProofFunctionCallMetadata { PF.prfFunctionCallMetadataAddress = PB.concreteAddress blkO
                                              }
            prf = PF.ProofFunctionCall
                    { PF.prfFunctionCallPre = branchProofTriple branchCase
                    , PF.prfFunctionCallBody = contPrf
                    , PF.prfFunctionCallContinue = Nothing
                    , PF.prfFunctionCallMetadata = md
                    }
          return (branchCase, prf)
        _ -> do
          traceBundle bundle "BlockExitMismatch"
          throwHere $ PEE.BlockExitMismatch
  traceBundle bundle ("Finished proving obligations for all call targets (" ++ show (length funCallProofCases) ++ ")")
  -- if we have a "return" exit, prove that it satisfies the postcondition
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  precondReturn <- withSatAssumption goalTimeout (matchingExits bundle MS.MacawBlockEndReturn) $ do
    traceBundle bundle "Attempting to prove local postconditions"
    proveLocalPostcondition bundle postcondSpec
  let
    -- for simplicitly, we drop the condition on the return case, and assume
    -- it is taken if all other cases are false, which is checked by 'checkCasesTotal'
    returnByDefault = case precondReturn of
      Just (_, br) -> branchPreDomain br
      Nothing -> PES.statePredFalse sym

  traceBundle bundle "Checking exits"
  -- an exit that was not classified
  isUnknown <- do
    isJump <- matchingExits bundle MS.MacawBlockEndJump
    isFail <- matchingExits bundle MS.MacawBlockEndFail
    isBranch <- matchingExits bundle MS.MacawBlockEndBranch
    liftIO $ anyPred sym [isJump, isFail, isBranch]
  traceBundle bundle "Checking unknown"
  precondUnknown <- withSatAssumption goalTimeout (return isUnknown) $ do
    blocks <- PD.getBlocks (simPair bundle)
    emitWarning blocks PEE.BlockEndClassificationFailure
    univDom <- PVD.universalDomainSpec (simPair bundle)
    withNoFrameGuessing True $ proveLocalPostcondition bundle univDom

  --funCallProofCases' <- mapM joinCase funCallProofCases
  let
    funCallCases = map (\(p, (br, _)) -> (p, br)) funCallProofCases
    funCallProofs = map (\(_, (br, prf)) -> (branchBlocks br, prf)) funCallProofCases
    allPreconds = catMaybes [precondReturn,precondUnknown] ++ funCallCases
  
  precond' <- F.foldrM (\(p, br) stPred -> liftIO $ PES.muxStatePred sym p (branchPreDomain br) stPred)  returnByDefault funCallCases

  precond <- withAssumption_ (liftIO $ anyPred sym (map fst allPreconds)) $
    PVSi.simplifySubPreds precond'

  traceBundle bundle "Computing proof triple and ensuring that cases are total"
  -- TODO: this needs to be reorganized to make the domain results actually lazy
  blockSlice <- PFO.simBundleToSlice bundle
  triple <- PFO.lazyProofEvent_ (simPair bundle) $ do
    preDomain <- PFO.asLazyProof <$> PFO.statePredToPreDomain bundle precond
    postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
    status <- checkCasesTotal bundle preDomain allPreconds
    return $ PF.ProofTriple (simPair bundle) preDomain postDomain status
  let
    prf = PF.ProofBlockSlice
            { PF.prfBlockSliceTriple = triple
            , PF.prfBlockSliceCalls = funCallProofs
            , PF.prfBlockSliceReturn = fmap (branchProofTriple . snd) precondReturn
            , PF.prfBlockSliceUnknownExit = fmap (branchProofTriple . snd) precondUnknown
            , PF.prfBlockSliceTrans = blockSlice
            }
  return (precond, prf)

withNoFrameGuessing ::
  Bool -> EquivM_ sym arch f -> EquivM_ sym arch f
withNoFrameGuessing True f =
  CMR.local (\env -> env { envConfig = (envConfig env){PC.cfgComputeEquivalenceFrames = False} }) f
withNoFrameGuessing False f = f


matchingExits ::
  forall sym arch.
  SimBundle sym arch ->
  MS.MacawBlockEndCase ->
  EquivM sym arch (W4.Pred sym)
matchingExits bundle ecase = withSym $ \sym -> do
  case1 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (simOutBlockEnd $ simOutO bundle) ecase
  case2 <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (simOutBlockEnd $ simOutP bundle) ecase
  liftIO $ W4.andPred sym case1 case2  


-- | Prove a local postcondition (i.e. it must hold when the slice exits) for a pair of slices
proveLocalPostcondition ::
  HasCallStack =>
  SimBundle sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (BranchCase sym arch)
proveLocalPostcondition bundle postcondSpec = withSym $ \sym -> do
  traceBundle bundle "proveLocalPostcondition"
  eqRel <- CMR.asks envBaseEquiv
  (asm, postcond) <- liftIO $ bindSpec sym (simOutState $ simOutO bundle) (simOutState $ simOutP bundle) postcondSpec
  (_, postcondPred) <- liftIO $ getPostcondition sym bundle eqRel postcond

  traceBundle bundle "guessing equivalence domain"
  eqInputs <- withAssumption_ (return asm) $ do
    PVD.guessEquivalenceDomain bundle postcondPred postcond
  traceBundle bundle ("Equivalence domain has: " ++ show (M.keys (PES.predRegs eqInputs)))
  
  -- TODO: avoid re-computing this
  blockSlice <- PFO.simBundleToSlice bundle
  let sliceState = PF.slBlockPostState blockSlice
       
  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  eqInputsPred <- liftIO $ getPrecondition sym stackRegion bundle eqRel eqInputs

  notChecks <- liftIO $ W4.notPred sym postcondPred
  blocks <- PD.getBlocks $ simPair bundle

  traceBundle bundle ("Postcondition Predicate:\n" ++ show (W4.printSymExpr postcondPred))

  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  triple <- PFO.lazyProofEvent_ (simPair bundle) $ do
    preDomain <- PFO.asLazyProof <$> PFO.statePredToPreDomain bundle eqInputs
    postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
    result <- PFO.forkProofEvent_ (simPair bundle) $ do
        traceBundle bundle "Starting forked thread in proveLocalPostcondition"
        status <- withAssumption_ (liftIO $ allPreds sym [eqInputsPred, asm]) $ startTimer $ do
          traceBundle bundle "Starting first SAT check"
          r <- checkSatisfiableWithModel goalTimeout "check" notChecks $ \satRes -> do
            case satRes of
              W4R.Unsat _ -> do
                traceBundle bundle "Unsat"
                emitEvent (PE.CheckedEquivalence blocks PE.Equivalent)
                return PF.VerificationSuccess
              W4R.Unknown -> do
                traceBundle bundle "Unknown"
                emitEvent (PE.CheckedEquivalence blocks PE.Inconclusive)
                return PF.Unverified
              W4R.Sat fn -> do
                traceBundle bundle "Sat"
                preDomain' <- PF.unNonceProof <$> PFO.joinLazyProof preDomain
                postDomain' <- PF.unNonceProof <$> PFO.joinLazyProof postDomain
                ir <- PFG.getInequivalenceResult PEE.InvalidPostState preDomain' postDomain' blockSlice fn
                traceBundle bundle "Got inequivalence result"
                emitEvent (PE.CheckedEquivalence blocks (PE.Inequivalent ir))
                return $ PF.VerificationFail ir
          traceBundle bundle "Finished SAT check"
          case r of
            Right r' -> return r'
            Left exn -> do
              traceBundle bundle ("Solver exception: " ++ show exn)
              -- FIXME: Have a more detailed marker, possibly an explanation as to why it is unverified
              return $ PF.Unverified
        let noCond = fmap (\ir -> (ir, PFI.emptyCondEqResult sym)) status
        status' <- case status of
          PF.VerificationFail _ -> do
            traceBundle bundle "The verification failed"
            withAssumptionFrame_ (PVD.equateInitialStates bundle) $ do
              notGoal <- applyCurrentFrame notChecks
              goal <- applyCurrentFrame postcondPred

              traceBundle bundle "Checking goal satisfiability"
              withAssumption_ (return asm) $ do
                isPredSat goalTimeout goal >>= \case
                  True -> do
                    traceBundle bundle "Minimizing condition"
                    postDomain' <- PF.unNonceProof <$> PFO.joinLazyProof postDomain
                    traceBundle bundle "  computeEqCondition"
                    cond <- computeEqCondition bundle sliceState postDomain' notGoal
                    traceBundle bundle "  weakenEqCondition"
                    cond' <- weakenEqCondition bundle cond sliceState postDomain' goal
                    traceBundle bundle "  checkAndMinimizeEqCondition"
                    cond'' <- checkAndMinimizeEqCondition cond' goal
                    traceBundle bundle "Checking for conditional equivalence"
                    er <- checkSatisfiableWithModel goalTimeout "check" notGoal $ \satRes ->
                      case satRes of
                        W4R.Sat fn -> do
                          preUniv <- PVD.universalDomain
                          preUnivDomain <- PF.unNonceProof <$> PFO.statePredToPreDomain bundle preUniv
                          traceBundle bundle "proveLocalPostcondition->getInequivalenceResult"
                          ir <- PFG.getInequivalenceResult PEE.InvalidPostState preUnivDomain postDomain' blockSlice fn
                          traceBundle bundle "proveLocalPostcondition->getEquivalenceResult"
                          cr <- getCondEquivalenceResult bundle cond'' fn
                          traceBundle bundle ("conditionalEquivalenceResult: " ++ show (W4.printSymExpr (PFI.condEqPred cr)))
                          return $ PF.VerificationFail (ir, cr)
                        W4R.Unsat _ -> return $ noCond
                        W4R.Unknown -> return $ noCond
                    case er of
                      Right r -> return r
                      Left exn -> do
                        traceBundle bundle ("Solver failure: " ++ show exn)
                        return noCond
                  False -> return $ noCond
          _ -> return $ noCond
        traceBundle bundle "Generating a status node"
        return $ PF.ProofStatus status'
    return $ PF.ProofTriple (simPair bundle) preDomain postDomain result
  return $ BranchCase eqInputsPred eqInputs (simPair bundle) triple

-- | Summarize the conditional equivalence result, including any bindings it induces to
-- state variables and how it relates to the abort condition on the original program
getCondEquivalenceResult ::
  forall sym arch.
  SimBundle sym arch ->
  -- | computed equivalence condition
  W4.Pred sym ->
  -- | the model representing the counterexample from the solver
  SymGroundEvalFn sym ->
  EquivM sym arch (PFI.CondEquivalenceResult sym arch)
getCondEquivalenceResult bundle eqCond fn = do
  binds <- PFG.getCondEquivalenceBindings eqCond fn
  abortValid <- PAb.proveAbortValid bundle eqCond
  return $ PFI.CondEquivalenceResult binds eqCond abortValid
  

computeEqConditionGas :: Int
computeEqConditionGas = 20

-- | Incrementally build an equivalence condition by negating path conditions which
-- induce inequality on the block slices.
-- For each counter example to equivalence, the negated corresponding path condition is assumed,
-- and then the equivalence check is re-attempted.
--
-- This process terminates when the resulting set of assumptions is sufficient to prove
-- equivalence. Termination is guaranteed, because eventually all possible paths through
-- the given slice will be considered.
-- If no equivalence condition is found, then the resulting path condition from this function will be
-- the negation of all possible path conditions, and therefore inconsistent (i.e. representing
-- the degenerate case that @false@ implies equivalence).
--
-- Notes:
--
-- - The 'W4.Pred' input is the postcondition that, if true, would make the original and patched programs equivalent
--
-- - When we get to this function, we know that the equivalence condition does not hold
--
-- - It looks like, at the beginning of this function, the assumptions in scope are:
--
--   1. The assumptions from 'bindSpec'
--   2. The assumptions generated by 'equateInitialStates'
--
-- - This function attempts to find the conditions that can be assumed to make the postcondition satisfiable
--
-- - It does this by repeatedly:
--
--   1. Asking whether or not the goal is satisfiable
--   2. If it is, using the resulting model to construct a blocking clause (via the 'getPathCondition' function)
--   3. Assuming the negation of that clause
--
-- - The computed path condition is the conjunction of the negations of the
--   blocking clauses (i.e., saying that if we don't take any of the problematic
--   paths, then the goal equivalence state is reached)
--
-- NOTE: The "gas" parameter prevents us from getting stuck in an infinite loop,
-- but if it does cut us off, we are likely to not be able to identify a
-- conditional equivalence condition (and will flag it as an unconditional
-- failure)
computeEqCondition ::
  forall sym arch.
  SimBundle sym arch ->
  -- | block slice post-state
  PF.BlockSliceState (PFI.ProofSym sym arch) ->
  -- | equivalence post-domain
  PFI.SymDomain sym arch ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
computeEqCondition bundle sliceState postDomain notChecks = withSym $ \sym -> do
  cond <- go (W4.truePred sym) computeEqConditionGas
  PVSi.simplifyPred cond
  where
    go :: W4.Pred sym -> Int -> EquivM sym arch (W4.Pred sym)
    go pathCond 0 = return pathCond
    go pathCond gas = withSym $ \sym -> do
      -- can we satisfy equivalence, assuming that none of the given path conditions are taken?  
      goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
      eresult <- checkSatisfiableWithModel goalTimeout "check" notChecks $ \satRes -> case satRes of
          W4R.Unsat _ -> return Nothing
          -- this is safe, because the resulting condition is still checked later
          W4R.Unknown -> return Nothing
          -- counter-example, compute another path condition and continue
          W4R.Sat fn -> Just <$> do
            pathCond' <- PFG.getPathCondition bundle sliceState postDomain fn
            p <- flattenCondPair pathCond'
            traceBundle bundle ("Computing a new path condition:\n" ++ show (W4.printSymExpr p))
            return p
      case either (const Nothing) id eresult of
        -- no result, returning the accumulated path conditions
        Nothing -> return pathCond
      -- indeterminate result, failure
        Just unequalPathCond -> do
          notThis <- liftIO $ W4.notPred sym unequalPathCond
          pathCond' <- liftIO $ W4.andPred sym notThis pathCond
          -- assume this path is not taken and continue
          withAssumption_ (return notThis) $
            go pathCond' (gas - 1)

-- | Weaken a given equality condition with alternative paths which also
-- induce equality.
--
-- Similar to computing a sufficient condition, this process necessarily terminates, as
-- eventually the given predicate will cover all possible paths through the slice.
weakenEqCondition ::
  forall sym arch.
  SimBundle sym arch ->
  -- | path conditions that (should) induce equivalence
  W4.Pred sym ->
  -- | block slice post-state
  PF.BlockSliceState (PFI.ProofSym sym arch) ->
  -- | equivalence post-domain
  PFI.SymDomain sym arch ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
weakenEqCondition bundle pathCond_outer sliceState postDomain goal = withSym $ \sym -> do
  notPathCond_outer <- liftIO $ W4.notPred sym pathCond_outer
  go notPathCond_outer pathCond_outer
  where
    go :: W4.Pred sym -> W4.Pred sym -> EquivM sym arch (W4.Pred sym)
    go notPathCond pathCond = withSym $ \sym -> do
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      -- we use the heuristic timeout here because we're refining the equivalence condition
      -- and failure simply means we fail to refine it further

      result <- withAssumption_ (return notPathCond) $ do
        eres <- checkSatisfiableWithModel heuristicTimeout "check" goal $ \satRes -> case satRes of
          W4R.Unsat _ -> return Nothing
          W4R.Unknown -> return Nothing
          -- counter-example, compute another path condition and continue
          W4R.Sat fn -> Just <$> do
            pathCond' <- PFG.getPathCondition bundle sliceState postDomain fn
            flattenCondPair pathCond'
        return (either (const Nothing) id eres)
      case result of
        Nothing -> return pathCond
        Just unequalPathCond -> do
          isSufficient <- withAssumption_ (return unequalPathCond) $
            isPredTrue' heuristicTimeout goal
          pathCond' <- case isSufficient of
            True -> liftIO $ W4.orPred sym unequalPathCond pathCond
            False -> return pathCond
          notPathCond' <- liftIO $ W4.andPred sym notPathCond =<< W4.notPred sym unequalPathCond
          go notPathCond' pathCond'

flattenCondPair :: PPa.PatchPairC (W4.Pred sym) -> EquivM sym arch (W4.Pred sym)
flattenCondPair (PPa.PatchPairC p1 p2) = withSym $ \sym -> liftIO $ W4.andPred sym p1 p2

-- | Given a pair of path conditions, minimize the predicates and
-- verify that they imply equivalence of the block slice.
-- If no equivalence condition exists, then the given pair of path conditions is
-- inconsistent and the result of this function will simply be @false@.
--
-- The resulting predicate is simplified under the current set of assumptions.
checkAndMinimizeEqCondition ::
  forall sym arch.
  -- | path condition that is assumed to imply equivalence
  W4.Pred sym ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
checkAndMinimizeEqCondition cond goal = withValid $ withSym $ \sym -> do
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  -- this check is not strictly necessary, as the incremental checks should guarantee it
  -- for the moment it's a sanity check on this process as well as the final simplifications
  result <- withSatAssumption goalTimeout (PVSi.simplifyPred_deep cond) $ do
    isPredTrue' goalTimeout goal
  case result of
    Just (p, True) -> return p
    _ -> return $ W4.falsePred sym

--------------------------------------------------------
-- Toplevel preconditions and postconditions

-- | Default toplevel register post-domain: no registers are required to be
-- equivalent
topLevelPostRegisterDomain ::
  forall sym arch.
  EquivM sym arch (M.Map (Some (MM.ArchReg arch)) (W4.Pred sym))
topLevelPostRegisterDomain = return M.empty

-- | Default toplevel post-domain:
--   global (non-stack) memory
topLevelPostDomain ::
  HasCallStack =>
  PPa.BlockPair arch ->
  EquivM sym arch (StatePredSpec sym arch)
topLevelPostDomain pPair = withFreshVars pPair $ \stO stP -> withSym $ \sym -> do
  regDomain <- topLevelPostRegisterDomain
  withAssumptionFrame (PVV.validInitState Nothing stO stP) $
    return $ PES.StatePred
      {
        PES.predRegs = regDomain
      , PES.predStack = PEM.memPredFalse sym
      , PES.predMem = PEM.memPredTrue sym
      }

-- | Top-level equivalence check:
--  predomain:
--   all registers, stack, and memory
--   IPs match given patchpair
-- postdomain:
--   global (non-stack) memory  
topLevelTriple ::
  HasCallStack =>
  PPa.BlockPair arch ->
  EquivM sym arch (PF.EquivTriple sym arch)
topLevelTriple pPair = withPair pPair $ withFreshVars pPair $ \stO stP -> withSym $ \sym -> do
  regDomain <- PVD.allRegistersDomain
  postcond <- topLevelPostDomain pPair
  let
    precond = PES.StatePred
      { PES.predRegs = regDomain
      , PES.predStack = PEM.memPredTrue sym
      , PES.predMem = PEM.memPredTrue sym
      }
  let triple = PF.EquivTripleBody pPair precond postcond
  asm_frame <- PVV.validInitState (Just pPair) stO stP
  asm <- liftIO $ getAssumedPred sym asm_frame
  return (asm, triple)

--------------------------------------------------------
-- Totality check - ensure that the verified exit pairs cover all possible
-- branches

-- | Ensure that the given predicates completely describe all possibilities.
-- We prove that, given that the computed equivalence relation holds on each branch,
-- any exit from this block slice will necessarily fall into one of the provided cases.
checkCasesTotal ::
  HasCallStack =>
  SimBundle sym arch ->
  PFO.LazyProof sym arch PF.ProofDomainType ->
  [(W4.Pred sym, BranchCase sym arch)] ->
  EquivM sym arch (PFO.LazyProof sym arch PF.ProofStatusType)
checkCasesTotal bundle preDomain cases = withSym $ \sym -> do
  blocks <- PD.getBlocks $ simPair bundle
  someCase <- do
    casePreds <- mapM getCase cases
    liftIO $ anyPred sym casePreds

  notCheck <- liftIO $ W4.notPred sym someCase
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  PFO.forkProofEvent_ (simPair bundle) $ do
    estatus <- checkSatisfiableWithModel goalTimeout "checkCasesTotal" notCheck $ \satRes -> do
      let emit r = emitEvent (PE.CheckedBranchCompleteness blocks r)
      case satRes of
        W4R.Sat fn -> do
          -- TODO: avoid re-computing this
          blockSlice <- PFO.simBundleToSlice bundle
          preDomain' <- PF.unNonceProof <$> PFO.joinLazyProof preDomain
          -- TODO: a different counter-example type would be appropriate here, which explicitly
          -- doesn't consider the post-state. At this point we aren't interested in the target
          -- post-domain because we're just making sure that the given cases cover all possible exits,
          -- without considering the equivalence of the state at those exit points.
          noDomain <- PF.unNonceProof <$> PFO.emptyDomain (simPair bundle)

          ir <- PFG.getInequivalenceResult PEE.InvalidCallPair preDomain' noDomain blockSlice fn
          emit $ PE.BranchesIncomplete ir
          -- no conditional equivalence case
          return $ PF.VerificationFail (ir, PFI.emptyCondEqResult sym)
        W4R.Unsat _ -> do
          emit PE.BranchesComplete
          return PF.VerificationSuccess
        W4R.Unknown -> do
          emit PE.InconclusiveBranches
          return PF.Unverified
    let status = either (const PF.Unverified) id estatus
    return $ PF.ProofStatus status
  where
    -- | a branch case is assuming the pre-domain predicate, that the branch condition holds
    getCase :: (W4.Pred sym, BranchCase sym arch) -> EquivM sym arch (W4.Pred sym)
    getCase (cond, br) = withSym $ \sym ->
      liftIO $ W4.impliesPred sym (branchPrePred br) cond
