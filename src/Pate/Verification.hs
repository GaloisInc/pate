{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  ) where

import           Prelude hiding ( fail )

import           GHC.Stack ( HasCallStack, callStack )

import           Control.Applicative ( liftA2 )
import qualified Control.Concurrent.Async as CCA
import           Control.Monad ( void, unless )
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans as CMT
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO )

import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import           Data.Functor.Const ( Const(..) )
import           Data.Maybe ( catMaybes, maybeToList )
import qualified Data.Map as M
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Time as TM
import qualified Data.Traversable as DT
import           GHC.TypeLits
import qualified Lumberjack as LJ
import qualified Data.Word.Indexed as W

import qualified Data.Macaw.BinaryLoader.PPC as TOC (HasTOC(..))
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Symbolic as MS


import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.Backend.Simple as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT

import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.Symbol as WS
import qualified What4.SatResult as W4R

import qualified Pate.Address as PA
import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Equivalence
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import           Pate.Proof.Ground as PFG
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Proof.Operations as PFO
import qualified Pate.Register as PRe
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PS
import           Pate.Types
import qualified Pate.Types as PT
import qualified Pate.Verification.ExternalCall as PVE
import qualified Pate.Verification.SymbolicExecution as PVS
import           What4.ExprHelpers


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

-- | We run discovery in parallel, since we need to run it two or three times
--
-- Currently, we run discovery twice on the original binary: once without
-- hints and again if hints are available.
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
  -> Maybe PH.VerificationHints
  -> PLE.LoadedELF arch
  -> PLE.LoadedELF arch
  -> CME.ExceptT (PEE.EquivalenceError arch) IO (MM.ArchSegmentOff arch, ParsedFunctionMap arch, MM.ArchSegmentOff arch, ParsedFunctionMap arch)
runDiscovery logAction mhints elf elf' = do
  let discoverAsync e h = liftIO (CCA.async (CME.runExceptT (PD.runDiscovery e h)))
  origDiscovery <- discoverAsync elf mempty
  mHintedDiscovery <- DT.traverse (discoverAsync elf) mhints
  patchedDiscovery <- case mhints of
    Just hints -> discoverAsync elf' hints
    Nothing -> discoverAsync elf' mempty
  (_, oMainUnhinted, oPfmUnhinted) <- CME.liftEither =<< liftIO (CCA.wait origDiscovery)
  (_, pMain, pPfm) <- CME.liftEither =<< liftIO (CCA.wait patchedDiscovery)
  (oMain, oPfm) <- case mHintedDiscovery of
    Nothing -> return (oMainUnhinted, oPfmUnhinted)
    Just hintedDiscovery -> do
      (hintErrors, oMain, oPfm) <- CME.liftEither =<< liftIO (CCA.wait hintedDiscovery)
      unless (null hintErrors) $ do
        let invalidSet = S.fromList hintErrors
        let invalidEntries = [ (name, addr)
                             | hints <- maybeToList mhints
                             , (name, addr) <- PH.functionEntries hints
                             , S.member addr invalidSet
                             ]
        liftIO $ LJ.writeLog logAction (PE.FunctionEntryInvalidHints invalidEntries)

      let unhintedDiscoveredAddresses = S.fromList (parsedFunctionEntries oPfmUnhinted)
      let hintedDiscoveredAddresses = S.fromList (parsedFunctionEntries oPfm)
      let newAddrs = hintedDiscoveredAddresses `S.difference` unhintedDiscoveredAddresses
      unless (S.null newAddrs) $ do
        liftIO $ LJ.writeLog logAction (PE.FunctionsDiscoveredFromHints (F.toList newAddrs))

      return (oMain, oPfm)

  liftIO $ LJ.writeLog logAction (PE.LoadedBinaries (elf, oPfm) (elf', pPfm))
  return (oMain, oPfm, pMain, pPfm)


-- | Verify equality of the given binaries.
verifyPairs ::
  forall arch.
  PA.ValidArch arch =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  Maybe PH.VerificationHints ->
  PLE.LoadedELF arch ->
  PLE.LoadedELF arch ->
  BlockMapping arch ->
  PC.VerificationConfig ->
  [PPa.BlockPair arch] ->
  CME.ExceptT (PEE.EquivalenceError arch) IO PT.EquivalenceStatus
verifyPairs validArch logAction mhints elf elf' blockMap vcfg pPairs = do
  startTime <- liftIO TM.getCurrentTime
  Some gen <- liftIO N.newIONonceGenerator
  vals <- case MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) of
    Nothing -> CME.throwError $ PEE.equivalenceError PEE.UnsupportedArchitecture
    Just vs -> pure vs
  ha <- liftIO CFH.newHandleAllocator

  (oMain, oPfm, pMain, pPfm) <- runDiscovery logAction mhints elf elf'

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
  let
    exts = MT.macawTraceExtensions eval model (trivialGlobalMap @_ @arch) undefops

    oCtx = BinaryContext
      { binary = PLE.loadedBinary elf
      , parsedFunctionMap = oPfm
      , binEntry = oMain
      }
    rCtx = BinaryContext
      { binary = PLE.loadedBinary elf'
      , parsedFunctionMap = pPfm
      , binEntry = pMain
      }
    ctxt = EquivalenceContext
      { nonces = gen
      , handles = ha
      , exprBuilder = sym
      , originalCtx = oCtx
      , rewrittenCtx = rCtx

      }
    env = EquivEnv
      { envWhichBinary = Nothing
      , envValidArch = validArch
      , envCtx = ctxt
      , envArchVals = vals
      , envExtensions = exts
      , envStackRegion = stackRegion
      , envGlobalRegion = globalRegion
      , envPCRegion = pcRegion
      , envMemTraceVar = model
      , envBlockEndVar = bvar
      , envBlockMapping = buildBlockMap pPairs blockMap
      , envLogger = logAction
      , envConfig = vcfg
      , envBaseEquiv = stateEquivalence sym stackRegion
      , envFailureMode = ThrowOnAnyFailure
      , envGoalTriples = [] -- populated in runVerificationLoop
      , envValidSym = Sym symNonce sym adapter
      , envStartTime = startedAt
      , envTocs = (TOC.getTOC $ PLE.loadedBinary elf, TOC.getTOC $ PLE.loadedBinary elf')
      -- TODO: restructure EquivEnv to avoid this
      , envCurrentFunc = error "no function under analysis"
      , envCurrentFrame = mempty
      , envNonceGenerator = gen
      , envParentNonce = Some topNonce
      , envUndefPointerOps = undefops
      , envParentBlocks = mempty
      , envProofCache = prfCache
      , envExitPairsCache = ePairCache
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
  IO (PT.EquivalenceStatus, EquivalenceStatistics)
runVerificationLoop env pPairs = do
  let
    st = EquivState
          { stProofs = []
          , stSimResults = M.empty
          , stEqStats = mempty
          }
  result <- CME.runExceptT $ runEquivM env st doVerify
  case result of
    Left err -> withValidEnv env $ error (show err)
    Right r -> return r

  where
    doVerify :: EquivM sym arch (PT.EquivalenceStatus, EquivalenceStatistics)
    doVerify = do
      pPairs' <- ifConfig (not . PC.cfgPairMain) (return pPairs) $ do
        mainO <- CMR.asks $ binEntry . originalCtx . envCtx
        mainP <- CMR.asks $ binEntry . rewrittenCtx . envCtx
        blkO <- PD.mkConcreteBlock PB.BlockEntryInitFunction mainO
        blkP <- PD.mkConcreteBlock PB.BlockEntryInitFunction mainP
        let pPair = PPa.PatchPair blkO blkP
        return $ pPair : pPairs
      triples <- DT.forM pPairs' $ topLevelTriple
      result <- CMR.local (\env' -> env' { envGoalTriples = triples } ) $
        CME.foldM (\a b -> (<>) a <$> go b) mempty triples
      stats <- CMS.gets stEqStats
      return (result, stats)

    go ::
      PF.EquivTriple sym arch -> EquivM sym arch PT.EquivalenceStatus
    go triple = do
      result <- manifestError $ checkEquivalence triple
      emitResult result
      normResult <- return $ case result of
        Right PT.Equivalent -> EquivalenceStatistics 1 1 0
        Left _ -> EquivalenceStatistics 1 0 1
        Right _ -> EquivalenceStatistics 1 0 0
      CMS.modify' $ \st -> st { stEqStats = normResult <> (stEqStats st) }
      case result of
        Right r -> return r
        Left err -> return (Errored (show err))

ifConfig ::
  (PC.VerificationConfig -> Bool) ->
  EquivM sym arch a ->
  EquivM sym arch a ->
  EquivM sym arch a
ifConfig checkCfg ifT ifF = (CMR.asks $ checkCfg . envConfig) >>= \case
  True -> ifT
  False -> ifF

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
  EquivM sym arch PT.EquivalenceStatus
checkEquivalence triple = startTimer $ withSym $ \sym -> do
  withValid @() $ liftIO $ W4B.startCaching sym
  eqRel <- CMR.asks envBaseEquiv
  stackRegion <- CMR.asks envStackRegion
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

  void $ withSimSpec triple $ \stO stP tripleBody -> do
    let
      inO = SimInput stO (PPa.pOriginal pPair)
      inP = SimInput stP (PPa.pPatched pPair)
      precond = PF.eqPreDomain tripleBody
    (_, genPrecond) <- liftIO $ bindSpec sym stO stP genPrecondSpec
    preImpliesGen <- liftIO $ impliesPrecondition sym stackRegion inO inP eqRel precond genPrecond
    -- prove that the generated precondition is implied by the given precondition
    goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
    isPredTrue goalTimeout preImpliesGen >>= \case
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
    PF.VerificationSuccess -> return PT.Equivalent
    PF.VerificationFail (_, cond) -> case W4.asConstantPred (PFI.condEqPred cond) of
      Just False -> return Inequivalent
      _ -> return PT.ConditionallyEquivalent
    _ -> return PT.Inequivalent
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
  withFreshVars $ \stO stP -> do
    let
      simInO_ = SimInput stO (PPa.pOriginal pPair)
      simInP_ = SimInput stP (PPa.pPatched pPair)

    withAssumptionFrame' (validInitState (Just pPair) stO stP) $ do
      traceBlockPair pPair "Simulating original blocks"
      (asmO, simOutO_) <- PVS.simulate simInO_
      traceBlockPair pPair "Simulating patched blocks"
      (asmP, simOutP_) <- PVS.simulate simInP_
      traceBlockPair pPair "Finished simulating blocks"
      (_, simOutO') <- withAssumptionFrame (validConcreteReads simOutO_) $ return simOutO_
      (_, simOutP') <- withAssumptionFrame (validConcreteReads simOutP_) $ return simOutP_

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
    PB.BlockEntryInitFunction -> CMR.local (\_ -> env' { envCurrentFunc = pPair }) f
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
      impliesPostcond (PF.eqPostDomain $ specBody triple) postcondSpec >>= \case
        True -> do
          traceBlockPair pPair "Cache hit"
          prf' <- PFO.wrapFutureNonceApp futureProof
          return $ Just (fmap PF.eqPreDomain triple, prf')
        False -> do
          traceBlockPair pPair "Cache miss"
          return Nothing

    errorResult :: EquivM sym arch ret
    errorResult = fmap unzipProof $ withSym $ \sym -> withFreshVars $ \stO stP -> do
      let
        simInO_ = SimInput stO (PPa.pOriginal pPair)
        simInP_ = SimInput stP (PPa.pPatched pPair)
      traceBlockPair pPair "Caught an error, so making a trivial block slice"
      PA.SomeValidArch _ externalDomain <- CMR.asks envValidArch
      r <- trivialBlockSlice False externalDomain (PPa.PatchPair simInO_ simInP_) postcondSpec
      return $ (W4.truePred sym, r)

impliesPostcond ::
  StatePredSpec sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch Bool
impliesPostcond stPredAsm stPredConcl = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  fmap specBody $ withFreshVars $ \stO stP -> do
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
        blkO = targetCall blktO
        blkP = targetCall blktP
        pPair = PPa.PatchPair blkO blkP
      traceBundle bundle ("  targetCall: " ++ show blkO)
      case (targetReturn blktO, targetReturn blktP) of
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
                  PA.SomeValidArch syscallDomain _ <- CMR.asks envValidArch
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
    univDom <- universalDomainSpec
    withNoFrameGuessing True $ proveLocalPostcondition bundle univDom

  --funCallProofCases' <- mapM joinCase funCallProofCases
  let
    funCallCases = map (\(p, (br, _)) -> (p, br)) funCallProofCases
    funCallProofs = map (\(_, (br, prf)) -> (branchBlocks br, prf)) funCallProofCases
    allPreconds = catMaybes [precondReturn,precondUnknown] ++ funCallCases
  
  precond' <- F.foldrM (\(p, br) stPred -> liftIO $ PES.muxStatePred sym p (branchPreDomain br) stPred)  returnByDefault funCallCases

  precond <- withAssumption_ (liftIO $ anyPred sym (map fst allPreconds)) $
    simplifySubPreds precond'

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

simplifySubPreds ::
  forall sym arch f.
  HasCallStack =>
  PEM.ExprMappable sym f =>
  f ->
  EquivM sym arch f
simplifySubPreds a = withValid $ withSym $ \sym -> do
  (cache :: W4B.IdxCache t (W4B.Expr t)) <- W4B.newIdxCache
  let
    simplifyPred' ::
      W4B.Expr t tp ->
      EquivM sym arch (W4B.Expr t tp)
    simplifyPred' e = case W4.exprType e of
      W4.BaseBoolRepr ->  W4B.idxCacheEval cache e $ simplifyPred e
      _ -> return e
  IO.withRunInIO $ \runInIO -> PEM.mapExpr sym (\e -> runInIO (simplifyPred' e)) a

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
    guessEquivalenceDomain bundle postcondPred postcond
  traceBundle bundle ("Equivalence domain has: " ++ show (M.keys (PES.predRegs eqInputs)))
  
  -- TODO: avoid re-computing this
  blockSlice <- PFO.simBundleToSlice bundle
  let sliceState = PF.slBlockPostState blockSlice
       
  stackRegion <- CMR.asks envStackRegion
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
          return r
        let noCond = fmap (\ir -> (ir, PFI.CondEquivalenceResult MapF.empty (W4.falsePred sym))) status
        status' <- case status of
          PF.VerificationFail _ -> do
            traceBundle bundle "The verification failed"
            withAssumptionFrame_ (equateInitialStates bundle) $ do
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
                    checkSatisfiableWithModel goalTimeout "check" notGoal $ \satRes ->
                      case satRes of
                        W4R.Sat fn -> do
                          preUniv <- universalDomain
                          preUnivDomain <- PF.unNonceProof <$> PFO.statePredToPreDomain bundle preUniv
                          traceBundle bundle "proveLocalPostcondition->getInequivalenceResult"
                          ir <- PFG.getInequivalenceResult PEE.InvalidPostState preUnivDomain postDomain' blockSlice fn
                          traceBundle bundle "proveLocalPostcondition->getEquivalenceResult"
                          cr <- PFG.getCondEquivalenceResult cond'' fn
                          traceBundle bundle ("conditionalEquivalenceResult: " ++ show (W4.printSymExpr (PFI.condEqPred cr)))
                          return $ PF.VerificationFail (ir, cr)
                        W4R.Unsat _ -> return $ noCond
                        W4R.Unknown -> return $ noCond

                  False -> return $ noCond
          _ -> return $ noCond
        traceBundle bundle "Generating a status node"
        return $ PF.ProofStatus status'
    return $ PF.ProofTriple (simPair bundle) preDomain postDomain result
  return $ BranchCase eqInputsPred eqInputs (simPair bundle) triple

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
  simplifyPred cond
  where
    go :: W4.Pred sym -> Int -> EquivM sym arch (W4.Pred sym)
    go pathCond 0 = return pathCond
    go pathCond gas = withSym $ \sym -> do
      -- can we satisfy equivalence, assuming that none of the given path conditions are taken?  
      goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
      result <- checkSatisfiableWithModel goalTimeout "check" notChecks $ \satRes -> case satRes of
          W4R.Unsat _ -> return Nothing
          -- this is safe, because the resulting condition is still checked later
          W4R.Unknown -> return Nothing
          -- counter-example, compute another path condition and continue
          W4R.Sat fn -> Just <$> do
            pathCond' <- PFG.getPathCondition bundle sliceState postDomain fn
            p <- flattenCondPair pathCond'
            traceBundle bundle ("Computing a new path condition:\n" ++ show (W4.printSymExpr p))
            return p
      case result of
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

      result <- withAssumption_ (return notPathCond) $
        checkSatisfiableWithModel heuristicTimeout "check" goal $ \satRes -> case satRes of
          W4R.Unsat _ -> return Nothing
          W4R.Unknown -> return Nothing
          -- counter-example, compute another path condition and continue
          W4R.Sat fn -> Just <$> do
            pathCond' <- PFG.getPathCondition bundle sliceState postDomain fn
            flattenCondPair pathCond'
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
  result <- withSatAssumption goalTimeout (simplifyPred_deep cond) $ do
    isPredTrue' goalTimeout goal
  case result of
    Just (p, True) -> return p
    _ -> return $ W4.falsePred sym

-- | Simplify a predicate by considering the
-- logical necessity of each atomic sub-predicate under the current set of assumptions.
-- Additionally, simplify array lookups across unrelated updates.
simplifyPred_deep ::
  forall sym arch.
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
simplifyPred_deep p = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  cache <- W4B.newIdxCache
  let
    checkPred :: W4.Pred sym -> EquivM sym arch Bool
    checkPred p' = fmap getConst $ W4B.idxCacheEval cache p' $
      Const <$> isPredTrue' heuristicTimeout p'
  -- remove redundant atoms
  p1 <- minimalPredAtoms sym checkPred p
  -- resolve array lookups across unrelated updates
  p2 <- resolveConcreteLookups sym (\e1 e2 -> W4.asConstantPred <$> liftIO (W4.isEq sym e1 e2)) p1
  -- additional bitvector simplifications
  p3 <- liftIO $ simplifyBVOps sym p2
  -- drop any muxes across equality tests
  p4 <- liftIO $ expandMuxEquality sym p3
  -- remove redundant conjuncts
  p_final <- simplifyConjuncts sym checkPred p4
  -- TODO: redundant sanity check that simplification hasn't clobbered anything
  validSimpl <- liftIO $ W4.isEq sym p p_final
  isPredTrue' heuristicTimeout validSimpl >>= \case
    True -> return p_final
    False -> throwHere $ PEE.InconsistentSimplificationResult (CC.showF p) (CC.showF p_final)
  

--------------------------------------------------------
-- Propagating preconditions

-- | Guess a sufficient memory domain that will cause the
-- given postcondition to be satisfied on the given equivalence relations.
--
-- We consider each 'MemCell' present in both the given target post-domain (the given 'MemPred')
-- as well as the trace of memory operations from the 'SimBundle'. For each cell we try to prove
-- that the goal is independent of its initial value - that is, the goal predicate implies
-- the same predicate where the initial value of that cell has been assigned an arbitary value.
-- Each cell is either proven to be irrelevant, and therefore excluded from the guessed pre-domain, or failed
-- to be proven irrelevant, and therefore included.
--
-- This is an imprecise guess for multiple reasons:
-- (1) It does not attempt to determine the exact conditions under which the memory cells may be
-- irrelevant. We assume the branch condition of the cell, and try to prove its irrelevance.
-- If this proof fails, we include it in the domain under the same condition. More precise
-- conditions may allow us to refine this - i.e. a memory cell may be unconditionally read, but
-- only copied to relevant state under some condition.
--
-- (2) If this proof times out, we conservatively include the cell in the domain.

guessMemoryDomain ::
  forall sym arch.
  SimBundle sym arch ->
  -- | the target postcondition that we are trying to satisfy
  W4.Pred sym ->
  -- | the same goal expression, but with its 'patched' memory array rebound to the given
  -- 'MT.MemTraceImpl'
  (MT.MemTraceImpl sym (MM.ArchAddrWidth arch), W4.Pred sym) ->
  -- | the target memory domain used to generate the postcondition
  PEM.MemPred sym arch ->
  -- | filter for whether or not memory cells can possibly belong to
  -- the given domain
  (forall w. PMC.MemCell sym arch w -> EquivM sym arch (W4.Pred sym)) ->
  EquivM sym arch (PEM.MemPred sym arch)
guessMemoryDomain bundle goal (memP', goal') memPred cellFilter = withSym $ \sym -> do
  foots <- getFootprints bundle
  cells <- do
    localPred <- liftIO $ PEM.addFootPrintsToPred sym foots memPred
    PEM.mapMemPred localPred $ \cell p -> do
      isFiltered <- cellFilter cell
      pathCond <- liftIO $ W4.andPred sym p isFiltered
      simplifyPred pathCond

  -- we take the entire reads set of the block and then filter it according
  -- to the polarity of the postcondition predicate
  result <- PEM.mapMemPredPar cells $ \cell p -> maybeEqualAt bundle cell p >>= \case
    True -> ifConfig (not . PC.cfgComputeEquivalenceFrames) (Par.present $ return polarity) $ do
      let repr = MM.BVMemRepr (PMC.cellWidth cell) (PMC.cellEndian cell)
      -- clobber the "patched" memory at exactly this cell
      CLM.LLVMPointer _ freshP <- liftIO $ freshPtrBytes sym "MemCell_guessMemoryDomain" (PMC.cellWidth cell)

      memP'' <- liftIO $ MT.writeMemArr sym memP (PMC.cellPtr cell) repr freshP
      eqMemP <- liftIO $ W4.isEq sym (MT.memArr memP') (MT.memArr memP'')

      -- see if we can prove that the goal is independent of this clobbering
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      withAssumption_ (liftIO $ allPreds sym [p, eqMemP, goal]) $ do
        result <- isPredTruePar' heuristicTimeout goal'
        Par.forFuture result $ \case
          True -> liftIO $ W4.baseTypeIte sym polarity (W4.falsePred sym) p
          False -> liftIO $ W4.baseTypeIte sym polarity p (W4.falsePred sym)
    False -> Par.present $ liftIO $ W4.notPred sym polarity
  Par.joinFuture (result :: Par.Future (PEM.MemPred sym arch))
  where
    polarity = PEM.memPredPolarity memPred
    memP = simInMem $ simInP bundle

-- | True if it is possible for the initial value of this cell to be equivalent,
-- but it is not necessarily the case that they are equivalent. under
-- the current set of assumptions.
maybeEqualAt ::
  SimBundle sym arch ->
  PMC.MemCell sym arch w ->
  W4.Pred sym ->
  EquivM sym arch Bool
maybeEqualAt bundle cell@(PMC.MemCell{}) cond = withSym $ \sym -> do
  valO <- liftIO $ PMC.readMemCell sym memO cell
  valP <- liftIO $ PMC.readMemCell sym memP cell
  ptrsEq <- liftIO $ MT.llvmPtrEq sym valO valP

  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  withAssumption_ (return cond) $
    isPredSat goalTimeout ptrsEq
  where
    memO = simInMem $ simInO bundle
    memP = simInMem $ simInP bundle


-- | Under the current assumptions, attempt to collapse a predicate
-- into either trivially true or false
simplifyPred ::
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
simplifyPred p = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  isPredSat heuristicTimeout p >>= \case
    True -> isPredTrue' heuristicTimeout p >>= \case
      True -> return $ W4.truePred sym
      False -> return p
    False -> return $ W4.falsePred sym


bindMemory ::
  -- | value to rebind
  MT.MemTraceImpl sym ptrW ->
  -- | new value
  MT.MemTraceImpl sym ptrW ->
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')  
bindMemory memVar memVal expr = withSym $ \sym -> do
  liftIO $ rebindExpr sym (Ctx.empty Ctx.:> VarBinding (MT.memArr memVar) (MT.memArr memVal)) expr

-- | Guess a sufficient domain that will cause the
-- given postcondition to be satisfied on the given equivalence relations.
-- This domain includes: the registers, the stack and the global (i.e. non-stack) memory.
--
-- Each register is guessed by attempting to prove that the goal is independent of
-- its initial value.
-- See 'guessMemoryDomain' for an explanation for how the memory domains are guessed.
--
-- This guess is an over-approximation of the state that must be equal in order to
-- prove the given goal. The risk of getting this wrong is incidentally including state
-- that is actually irrelevant, and later cannot be proven equal when used as the post-domain
-- in a preceeding block. In other words, we may assume a precondition that is too strong when
-- it must be later proven as postcondition.
--
-- Importantly, the output of this function is not trusted. Once the guess is made, it is later used to
-- assemble and prove the precise equivalence property that we are interested in. If this guess
-- is incorrect (i.e. we incorrectly exclude some memory location) then that proof will fail.
guessEquivalenceDomain ::
  forall sym arch.
  (HasCallStack) =>
  SimBundle sym arch ->
  W4.Pred sym ->
  PES.StatePred sym arch ->
  EquivM sym arch (PES.StatePred sym arch)
guessEquivalenceDomain bundle goal postcond = startTimer $ withSym $ \sym -> do
  traceBundle bundle "Entering guessEquivalenceDomain"
  ExprFilter isBoundInGoal <- getIsBoundFilter' goal
  eqRel <- CMR.asks envBaseEquiv
  result <- zipRegStatesPar (simRegs inStO) (simRegs inStP) $ \r vO vP -> do
      isInO <- liftFilterMacaw isBoundInGoal vO
      isInP <- liftFilterMacaw isBoundInGoal vP
      let
        include = Par.present $ return $ Just (Some r, W4.truePred sym)
        exclude :: EquivM sym arch (Par.Future (Maybe (Some (MM.ArchReg arch), W4B.Expr t W4.BaseBoolType)))
        exclude = Par.present $ return Nothing
      case PRe.registerCase (PSR.macawRegRepr vO) r of
        -- we have concrete values for the pre-IP and the TOC (if arch-defined), so we don't need
        -- to include them in the pre-domain
        PRe.RegIP -> exclude
        PRe.RegTOC -> exclude
        -- this requires some more careful consideration. We don't want to include
        -- the stack pointer in computed domains, because this unreasonably
        -- restricts preceding blocks from having different numbers of stack allocations.
        -- However our equivalence relation is not strong enough to handle mismatches in
        -- values written to memory that happen to be stack addresses, if those
        -- addresses were computed with different stack bases.
        PRe.RegSP -> ifConfig PC.cfgComputeEquivalenceFrames exclude include
        _ | isInO || isInP ->
          ifConfig (not . PC.cfgComputeEquivalenceFrames) include $ do
            (isFreshValid, freshO) <- freshRegEntry (PPa.pPatched $ simPair bundle) r vO

            goal' <- bindMacawReg vO freshO goal
            goalIgnoresReg <- liftIO $ W4.impliesPred sym goal goal'

            heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
            withAssumption_ (return isFreshValid) $ do
              result <- isPredTruePar' heuristicTimeout goalIgnoresReg
              Par.forFuture result $ \case
                True -> return Nothing
                False -> return $ Just (Some r, W4.truePred sym)
        _ -> exclude
  regsDom <- (M.fromList . catMaybes) <$> Par.joinFuture @_ @Par.Future result
  stackRegion <- CMR.asks envStackRegion
  let
    isStackCell cell = do
      let CLM.LLVMPointer region _ = PMC.cellPtr cell
      liftIO $ W4.natEq sym region stackRegion
    isNotStackCell cell = do
      p <- isStackCell cell
      liftIO $ W4.notPred sym p

  eqRegsFrame <- equateRegisters regsDom bundle
   
  -- rewrite the state elements to explicitly equate registers we have assumed equivalent
  (_, bundle_regsEq) <- applyAssumptionFrame eqRegsFrame bundle
  (_, goal_regsEq) <- applyAssumptionFrame eqRegsFrame goal
  (_, postcond_regsEq) <- applyAssumptionFrame eqRegsFrame postcond
  
  memP' <- liftIO $ MT.initMemTrace sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  goal' <- bindMemory memP memP' goal_regsEq

  stackDom <- guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (PES.predStack postcond_regsEq) isStackCell
  let stackEq = liftIO $ memPredPre sym (memEqAtRegion sym stackRegion) inO inP (eqRelStack eqRel) stackDom
  memDom <- withAssumption_ stackEq $ do
    guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (PES.predMem postcond_regsEq) isNotStackCell

  blocks <- PD.getBlocks $ simPair bundle
  
  emitEvent (PE.ComputedPrecondition blocks)
  return $ PES.StatePred
    { PES.predRegs = regsDom
    , PES.predStack = stackDom
    , PES.predMem = memDom
    }
  where
    memP = simInMem $ simInP bundle
    inO = simInO bundle
    inP = simInP bundle
    inStO = simInState $ simInO bundle
    inStP = simInState $ simInP bundle

freshRegEntry ::
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (W4.Pred sym, PSR.MacawRegEntry sym tp)
freshRegEntry initBlk r entry = withSym $ \sym -> do
  fresh <- case PSR.macawRegRepr entry of
    CLM.LLVMPointerRepr w -> liftIO $ do
      ptr <- freshPtr sym (PC.showF r) w
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) ptr
    CT.BoolRepr -> liftIO $ do
      b <- W4.freshConstant sym (WS.safeSymbol (PC.showF r)) WT.BaseBoolRepr
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) b
    CT.StructRepr Ctx.Empty -> return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) Ctx.Empty
    repr -> throwHere $ PEE.UnsupportedRegisterType $ Some repr
  isValid <- validRegister (Just initBlk) fresh r
  isValid_pred <- liftIO $ getAssumedPred sym isValid
  return (isValid_pred, fresh)

getIsBoundFilter' ::
  W4.SymExpr sym tp ->
  EquivM sym arch (ExprFilter sym)
getIsBoundFilter' e = withValid $ liftIO $ getIsBoundFilter e

liftFilterMacaw ::
  (forall tp'. W4.SymExpr sym tp' -> IO Bool) ->
  PSR.MacawRegEntry sym tp -> EquivM sym arch Bool
liftFilterMacaw f entry = withSym $ \sym -> do
  case PSR.macawRegRepr entry of
    CLM.LLVMPointerRepr{} -> liftIO $ do
      let CLM.LLVMPointer reg off = PSR.macawRegValue entry
      iReg <- W4.natToInteger sym reg
      reg' <- f iReg
      off' <- f off
      return $ reg' || off'
    CT.BoolRepr -> liftIO $ f (PSR.macawRegValue entry)
    CT.StructRepr Ctx.Empty -> return False
    repr -> throwHere $ PEE.UnsupportedRegisterType (Some repr)


equateRegisters ::
  M.Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  SimBundle sym arch ->
  EquivM sym arch (AssumptionFrame sym)
equateRegisters regRel bundle = withValid $ withSym $ \sym -> do
  fmap (mconcat) $ zipRegStates (simRegs inStO) (simRegs inStP) $ \r vO vP -> case PRe.registerCase (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return mempty
    _ -> case M.lookup (Some r) regRel of
      Just cond | Just True <- W4.asConstantPred cond -> liftIO $ macawRegBinding sym vO vP
      _ -> return mempty
  where
    inStO = simInState $ simInO bundle
    inStP = simInState $ simInP bundle

equateInitialMemory :: SimBundle sym arch -> EquivM sym arch (AssumptionFrame sym)
equateInitialMemory bundle =
  return $ exprBinding (MT.memArr (simInMem $ simInO bundle)) (MT.memArr (simInMem $ simInP bundle))

equateInitialStates :: SimBundle sym arch -> EquivM sym arch (AssumptionFrame sym)
equateInitialStates bundle = do
  regDomain <- allRegistersDomain
  eqRegs <- equateRegisters regDomain bundle
  eqMem <- equateInitialMemory bundle
  return $ eqRegs <> eqMem

bindMacawReg ::
  -- | value to rebind
  PSR.MacawRegEntry sym tp ->
  -- | new value
  PSR.MacawRegEntry sym tp ->
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')
bindMacawReg var val expr = withValid $ withSym $ \sym -> do
  bind <- liftIO $ macawRegBinding sym var val
  liftIO $ rebindWithFrame sym bind expr


wLit :: (1 <= w) => W.W w -> EquivM sym arch (W4.SymBV sym w)
wLit w = withSymIO $ \sym -> W4.bvLit sym (W.rep w) (BVS.mkBV (W.rep w) (W.unW w))

functionSegOffs ::
  PPa.BlockPair arch ->
  EquivM sym arch (MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)
functionSegOffs pPair = do
  PPa.PatchPair (PE.Blocks _ (pblkO:_)) (PE.Blocks _ (pblkP:_)) <- PD.getBlocks pPair
  return $ (MD.pblockAddr pblkO, MD.pblockAddr pblkP)

getCurrentTOCs :: PA.HasTOCReg arch => EquivM sym arch (W.W (MM.ArchAddrWidth arch), W.W (MM.ArchAddrWidth arch))
getCurrentTOCs = do
  (tocO, tocP) <- CMR.asks envTocs
  curFuncs <- CMR.asks envCurrentFunc
  (addrO, addrP) <- functionSegOffs curFuncs
  wO <- case TOC.lookupTOC tocO addrO of
    Just w -> return w
    Nothing -> throwHere $ PEE.MissingTOCEntry addrO
  wP <- case TOC.lookupTOC tocP addrP of
    Just w -> return w
    Nothing -> throwHere $ PEE.MissingTOCEntry addrP
  return $ (wO, wP)

--------------------------------------------------------
-- Initial state validity

validRegister ::
  forall bin sym arch tp.
  PB.KnownBinary bin =>
  -- | if this register is an initial state, the corresponding
  -- starting block
  Maybe (PB.ConcreteBlock arch bin) ->
  PSR.MacawRegEntry sym tp ->
  MM.ArchReg arch tp ->
  EquivM sym arch (AssumptionFrame sym)
validRegister mblockStart entry r = withSym $ \sym ->
  case PRe.registerCase (PSR.macawRegRepr entry) r of
    PRe.RegIP -> case mblockStart of
      Just blockStart -> do
        ptrO <- PD.concreteToLLVM blockStart
        liftIO $ macawRegBinding sym entry (PSR.ptrToEntry ptrO)
      Nothing -> return $ mempty
    PRe.RegSP -> do
      stackRegion <- CMR.asks envStackRegion
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      iRegion <- liftIO $ W4.natToInteger sym region
      iStackRegion <- liftIO $ W4.natToInteger sym stackRegion
      return $ exprBinding iRegion iStackRegion
    PRe.RegBV -> liftIO $ do
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      zero <- W4.intLit sym 0
      iRegion <- W4.natToInteger sym region
      return $ exprBinding iRegion zero
    PRe.RegTOC -> do
      globalRegion <- CMR.asks envGlobalRegion
      (tocO, tocP) <- getCurrentTOCs
      tocBV <- case W4.knownRepr :: PB.WhichBinaryRepr bin of
        PB.OriginalRepr -> wLit tocO
        PB.PatchedRepr -> wLit tocP
      let targetToc = CLM.LLVMPointer globalRegion tocBV
      liftIO $ macawRegBinding sym entry (PSR.ptrToEntry targetToc)
    _ -> return $ mempty


validInitState ::
  Maybe (PPa.BlockPair arch) ->
  SimState sym arch PB.Original ->
  SimState sym arch PB.Patched ->
  EquivM sym arch (AssumptionFrame sym)
validInitState mpPair stO stP = do
  fmap mconcat $ zipRegStates (simRegs stO) (simRegs stP) $ \r vO vP -> do
    validO <- validRegister (fmap PPa.pOriginal mpPair) vO r
    validP <- validRegister (fmap PPa.pPatched mpPair) vP r
    return $ validO <> validP

-- | Reads from immutable data have known results.
-- We collect all the reads that occurred during the trace, and then
-- assert that those values are necessarily equivalent to the concrete
-- value from the binary
validConcreteReads ::
  forall bin sym arch.
  PB.KnownBinary bin =>
  SimOutput sym arch bin ->
  EquivM sym arch (AssumptionFrame sym)
validConcreteReads stOut = withSym $ \sym -> do
  binCtx <- getBinCtx @bin
  let
    binmem = MBL.memoryImage $ binary binCtx

    go :: Seq.Seq (MT.MemOp sym (MM.ArchAddrWidth arch)) -> EquivM sym arch (AssumptionFrame sym)
    go mops = do
      flatops <- fmap F.toList $ liftIO $ MT.flatMemOps sym mops
      fmap mconcat $ mapM readConcrete flatops

    readConcrete ::
      MT.MemOp sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (AssumptionFrame sym)
    readConcrete (MT.MemOp (CLM.LLVMPointer reg off) dir _ sz val end) = do
      case (W4.asNat reg, W4.asBV off, dir) of
        (Just 0, Just off', MT.Read) -> do
          let
            addr :: MM.MemAddr (MM.ArchAddrWidth arch) =
              MM.absoluteAddr (MM.memWord (fromIntegral (BVS.asUnsigned off')))
          W4.LeqProof <- return $ W4.leqMulPos (W4.knownNat @8) sz
          let bits = W4.natMultiply (W4.knownNat @8) sz
          case doStaticRead @arch binmem addr bits end of
            Just bv -> liftIO $ do
              let CLM.LLVMPointer _ bvval = val
              lit_val <- W4.bvLit sym bits bv
              -- FIXME: update when memory model has regions
              -- unclear what to assert about the region
              return $ exprBinding bvval lit_val
            Nothing -> return $ mempty
        _ -> return $ mempty
    readConcrete (MT.MergeOps _ seq1 seq2) = liftA2 (<>) (go seq1) (go seq2)
  go (MT.memSeq $ simOutMem $ stOut)

doStaticRead ::
  forall arch w .
  MM.Memory (MM.ArchAddrWidth arch) ->
  MM.MemAddr (MM.ArchAddrWidth arch) ->
  W4.NatRepr w ->
  MM.Endianness ->
  Maybe (BVS.BV w)
doStaticRead mem addr w end = case MM.asSegmentOff mem addr of
  Just segoff | MMP.isReadonly $ MM.segmentFlags $ MM.segoffSegment segoff ->
    fmap (BVS.mkBV w) $
    case (W4.intValue w, end) of
      (8, _) -> liftErr $ MM.readWord8 mem addr
      (16, MM.BigEndian) -> liftErr $ MM.readWord16be mem addr
      (16, MM.LittleEndian) -> liftErr $ MM.readWord16le mem addr
      (32, MM.BigEndian) -> liftErr $ MM.readWord32be mem addr
      (32, MM.LittleEndian) -> liftErr $ MM.readWord32le mem addr
      (64, MM.BigEndian) -> liftErr $ MM.readWord64be mem addr
      (64, MM.LittleEndian) -> liftErr $ MM.readWord64le mem addr
      _ -> Nothing
  _ -> Nothing
  where
    liftErr :: Integral a => Either e a -> Maybe Integer
    liftErr (Left _) = Nothing
    liftErr (Right a) = Just (fromIntegral a)

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
  EquivM sym arch (StatePredSpec sym arch)
topLevelPostDomain = withFreshVars $ \stO stP -> withSym $ \sym -> do
  regDomain <- topLevelPostRegisterDomain
  withAssumptionFrame (validInitState Nothing stO stP) $
    return $ PES.StatePred
      {
        PES.predRegs = regDomain
      , PES.predStack = PEM.memPredFalse sym
      , PES.predMem = PEM.memPredTrue sym
      }

allRegistersDomain ::
  forall sym arch.
  EquivM sym arch (M.Map (Some (MM.ArchReg arch)) (W4.Pred sym))
allRegistersDomain = withSym $ \sym -> do
  return $
    M.fromList $
    map (\(MapF.Pair r (Const p)) -> (Some r, p)) $
    MapF.toList $
    MM.regStateMap $
    MM.mkRegState (\_ -> Const (W4.truePred sym))


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
topLevelTriple pPair = withPair pPair $ withFreshVars $ \stO stP -> withSym $ \sym -> do
  regDomain <- allRegistersDomain
  postcond <- topLevelPostDomain
  let
    precond = PES.StatePred
      { PES.predRegs = regDomain
      , PES.predStack = PEM.memPredTrue sym
      , PES.predMem = PEM.memPredTrue sym
      }
  let triple = PF.EquivTripleBody pPair precond postcond
  asm_frame <- validInitState (Just pPair) stO stP
  asm <- liftIO $ getAssumedPred sym asm_frame
  return (asm, triple)

-- | Domain that includes entire state, except IP and SP registers
universalDomain ::
  forall sym arch.
  EquivM sym arch (PES.StatePred sym arch)
universalDomain =  withSym $ \sym -> do
  regDomain <- allRegistersDomain
  let regDomain' =
        M.delete (Some (MM.sp_reg @(MM.ArchReg arch))) $
        M.delete (Some (MM.ip_reg @(MM.ArchReg arch))) regDomain
  return $ PES.StatePred
    {
      PES.predRegs = regDomain'
    , PES.predStack = PEM.memPredTrue sym
    , PES.predMem = PEM.memPredTrue sym
    }

-- | Domain that includes entire state, except IP and SP registers
universalDomainSpec ::
  HasCallStack =>
  EquivM sym arch (StatePredSpec sym arch)
universalDomainSpec = withFreshVars $ \stO stP ->
  withAssumptionFrame (validInitState Nothing stO stP) $
  universalDomain

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
  PFO.forkProofEvent_ (simPair bundle) $ 
    checkSatisfiableWithModel goalTimeout "checkCasesTotal" notCheck $ \satRes -> do
    let
      emit r = emitEvent (PE.CheckedBranchCompleteness blocks r)
    status <- case satRes of
      W4R.Sat fn -> do
        -- TODO: avoid re-computing this
        blockSlice <- PFO.simBundleToSlice bundle
        preDomain' <- PF.unNonceProof <$> PFO.joinLazyProof preDomain
        -- TODO: a different counter-example type would be appropriate here, which explicitly
        -- doesn't consider the post-state. At this point we aren't interested in the target
        -- post-domain because we're just making sure that the given cases cover all possible exits,
        -- without considering the equivalence of the state at those exit points.
        noDomain <- PF.unNonceProof <$> PFO.emptyDomain
       
        ir <- PFG.getInequivalenceResult PEE.InvalidCallPair preDomain' noDomain blockSlice fn
        emit $ PE.BranchesIncomplete ir
        -- no conditional equivalence case
        return $ PF.VerificationFail (ir, PFI.CondEquivalenceResult MapF.empty (W4.falsePred sym))
      W4R.Unsat _ -> do
        emit PE.BranchesComplete
        return PF.VerificationSuccess
      W4R.Unknown -> do
        emit PE.InconclusiveBranches
        return PF.Unverified
    return $ PF.ProofStatus status
  where
    -- | a branch case is assuming the pre-domain predicate, that the branch condition holds
    getCase :: (W4.Pred sym, BranchCase sym arch) -> EquivM sym arch (W4.Pred sym)
    getCase (cond, br) = withSym $ \sym ->
      liftIO $ W4.impliesPred sym (branchPrePred br) cond

-- | Prefer existing entries
doAddAddr ::
  PA.ConcreteAddress arch ->
  Maybe (PA.ConcreteAddress arch) ->
  Maybe (PA.ConcreteAddress arch)
doAddAddr _ (Just addr) = Just addr
doAddAddr addr Nothing = Just addr

buildBlockMap ::
  [PPa.BlockPair arch] ->
  BlockMapping arch ->
  BlockMapping arch
buildBlockMap pairs bm = foldr go bm pairs
  where
    go :: PPa.BlockPair arch -> BlockMapping arch -> BlockMapping arch
    go (PPa.PatchPair orig patched) (BlockMapping m) =
      BlockMapping $ M.alter (doAddAddr (PB.concreteAddress patched)) (PB.concreteAddress orig) m
