{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
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
{-# LANGUAGE ViewPatterns #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  ) where

import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.MVar as MVar
import           Control.Lens ( (&), (.~), view )
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
import           GHC.Stack ( HasCallStack, callStack )
import qualified Lumberjack as LJ
import           Prelude hiding ( fail )
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as W4B
import qualified What4.FunctionName as WF
import qualified What4.Interface as W4
import qualified What4.SatResult as W4R

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Abort as PAb
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemoryDomain as PEM
import qualified Pate.Equivalence.RegisterDomain as PER
import qualified Pate.Equivalence.EquivalenceDomain as PED
import qualified Pate.Equivalence.Statistics as PESt
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Memory as PM
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Proof.CounterExample as PFC
import qualified Pate.Proof.Operations as PFO
import           Pate.SimState
import qualified Pate.Solver as PS
import qualified Pate.SymbolTable as PSym
import qualified Pate.Verification.Domain as PVD
import qualified Pate.Verification.ExternalCall as PVE
import           Pate.Verification.InlineCallee ( inlineCallee )
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Override.Library as PVOL
import qualified Pate.Verification.Simplify as PVSi
import qualified Pate.Verification.SymbolicExecution as PVSy
import qualified Pate.Verification.Validity as PVV
import qualified Pate.Verification.PairGraph as PPG
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
  -> PA.SomeValidArch arch
  -> PH.Hinted (PLE.LoadedELF arch)
  -> PH.Hinted (PLE.LoadedELF arch)
  -> CME.ExceptT (PEE.EquivalenceError arch) IO (PPa.PatchPair (PMC.BinaryContext arch))
runDiscovery logAction mCFGDir (PA.SomeValidArch archData) elf elf' = do
  binCtxO <- discoverCheckingHints PBi.OriginalRepr (PA.validArchOrigExtraSymbols archData) elf
  binCtxP <- discoverCheckingHints PBi.PatchedRepr (PA.validArchPatchedExtraSymbols archData) elf'
  liftIO $ LJ.writeLog logAction (PE.LoadedBinaries (PH.hinted elf) (PH.hinted elf'))
  return $ PPa.PatchPair binCtxO binCtxP
  where
    discoverAsync mdir repr extra e h = liftIO (CCA.async (CME.runExceptT (PD.runDiscovery mdir repr extra e h)))
    discoverCheckingHints repr extra e = do
      if | PH.hints e == mempty -> do
             unhintedAnalysis <- discoverAsync mCFGDir repr extra (PH.hinted e) mempty
             (_, oCtxUnhinted) <- CME.liftEither =<< liftIO (CCA.wait unhintedAnalysis)
             return oCtxUnhinted
         | otherwise -> do
             hintedAnalysis <- discoverAsync mCFGDir repr extra (PH.hinted e) (PH.hints e)
             (hintErrors, oCtxHinted) <- CME.liftEither =<< liftIO (CCA.wait hintedAnalysis)

             unless (null hintErrors) $ do
               let invalidSet = S.fromList hintErrors
               let invalidEntries = [ (name, addr)
                                    | (name, fd) <- PH.functionEntries (PH.hints e)
                                    , let addr = PH.functionAddress fd
                                    , S.member addr invalidSet
                                    ]
               liftIO $ LJ.writeLog logAction (PE.FunctionEntryInvalidHints repr invalidEntries)
             return oCtxHinted

verifyPairs ::
  forall arch.
  PA.ValidArch arch =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PC.VerificationConfig ->
  PC.PatchData ->
  CME.ExceptT (PEE.EquivalenceError arch) IO PEq.EquivalenceStatus
verifyPairs validArch logAction elf elf' vcfg pd = do
  Some gen <- liftIO N.newIONonceGenerator
  sym <- liftIO $ WE.newExprBuilder WE.FloatRealRepr WE.EmptyExprBuilderState gen 
  doVerifyPairs validArch logAction elf elf' vcfg pd gen sym

-- | Verify equality of the given binaries.
doVerifyPairs ::
  forall arch sym scope st fs.
  ( PA.ValidArch arch
  , sym ~ WE.ExprBuilder scope st fs
  , CB.IsSymInterface sym
  ) =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PC.VerificationConfig ->
  PC.PatchData ->
  N.NonceGenerator IO scope ->
  sym ->
  CME.ExceptT (PEE.EquivalenceError arch) IO PEq.EquivalenceStatus
doVerifyPairs validArch@(PA.SomeValidArch (PA.validArchDedicatedRegisters -> hdr)) logAction elf elf' vcfg pd gen sym = do
  startTime <- liftIO TM.getCurrentTime
  (traceVals, llvmVals) <- case ( MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) Nothing
                                , MS.genArchVals (Proxy @MS.LLVMMemory) (Proxy @arch) Nothing) of
    (Just vs1, Just vs2) -> pure (vs1, vs2)
    _ -> CME.throwError $ PEE.equivalenceError PEE.UnsupportedArchitecture
  ha <- liftIO CFH.newHandleAllocator
  contexts <- runDiscovery logAction (PC.cfgMacawDir vcfg) validArch elf elf'

  adapter <- liftIO $ PS.solverAdapter sym (PC.cfgSolver vcfg)


  -- Implicit parameters for the LLVM memory model
  let ?memOpts = CLM.laxPointerMemOptions

  eval <- CMT.lift (MS.withArchEval traceVals sym pure)
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

  -- compute function entry pairs from the input PatchData
  upData <- unpackPatchData contexts pd
  -- include the process entry point, if configured to do so
  pPairs' <- if PC.cfgPairMain vcfg then
               do let mainO = PMC.binEntry . PPa.pOriginal $ contexts
                  let mainP = PMC.binEntry . PPa.pPatched $ contexts
                  return (PPa.PatchPair mainO mainP : unpackedPairs upData)
              else
                return (unpackedPairs upData)

  let
    exts = MT.macawTraceExtensions eval model (trivialGlobalMap @_ @arch) undefops

    ctxt = PMC.EquivalenceContext
      { PMC.handles = ha
      , PMC.binCtxs = contexts
      , PMC.stackRegion = stackRegion
      , PMC.globalRegion = globalRegion
      , PMC._currentFunc = error "No function under analysis at startup"
      , PMC.originalIgnorePtrs = unpackedOrigIgnore upData
      , PMC.patchedIgnorePtrs = unpackedPatchIgnore upData
      , PMC.equatedFunctions = unpackedEquatedFuncs upData
      }
    env = EquivEnv
      { envWhichBinary = Nothing
      , envValidArch = validArch
      , envCtx = ctxt
      , envArchVals = traceVals
      , envLLVMArchVals = llvmVals
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
      , envOverrides = \ovCfg -> M.fromList [ (n, ov)
                                            | ov@(PVO.SomeOverride o) <- PVOL.overrides ovCfg
                                            , let txtName = WF.functionName (PVO.functionName o)
                                            , n <- [PSym.LocalSymbol txtName, PSym.PLTSymbol txtName]
                                            ]
      }
  -- Note from above: we are installing overrides for each override that cover
  -- both local symbol definitions and the corresponding PLT stubs for each
  -- override so that they cover both statically linked and dynamically-linked
  -- function calls.
  liftIO $ do
    (result, stats) <-
      case PC.cfgVerificationMethod vcfg of
        PC.HoareTripleVerification   -> runVerificationLoop env pPairs'
        PC.StrongestPostVerification -> PPG.runVerificationLoop env pPairs'
    endTime <- TM.getCurrentTime
    let duration = TM.diffUTCTime endTime startTime
    IO.liftIO $ LJ.writeLog logAction (PE.AnalysisEnd stats duration)
    return $ result


unpackBlockData ::
  HasCallStack =>
  PBi.KnownBinary bin =>
  PA.ValidArch arch =>
  PMC.BinaryContext arch bin ->
  PC.BlockData ->
  CME.ExceptT (PEE.EquivalenceError arch) IO (PB.FunctionEntry arch bin)
unpackBlockData ctxt (PC.Hex w) =
  case PM.resolveAbsoluteAddress mem (fromIntegral w) of
    Just segAddr ->
      -- We don't include a symbol for this entry point because we don't really
      -- have one conveniently available.  That name is never actually
      -- referenced, so it doesn't seem too problematic.
      return PB.FunctionEntry { PB.functionSegAddr = segAddr
                              , PB.functionSymbol = Nothing
                              , PB.functionBinRepr = W4.knownRepr
                              }
    Nothing -> CME.throwError (PEE.equivalenceError (PEE.LookupNotAtFunctionStart callStack caddr))
  where
    mem = MBL.memoryImage (PMC.binary ctxt)
    caddr = PAd.memAddrToAddr (MM.absoluteAddr (MM.memWord w))

data UnpackedPatchData arch =
  UnpackedPatchData { unpackedPairs :: [PPa.FunPair arch]
                    , unpackedOrigIgnore :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
                    , unpackedPatchIgnore :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
                    , unpackedEquatedFuncs :: [(PAd.ConcreteAddress arch, PAd.ConcreteAddress arch)]
                    }

unpackPatchData ::
  HasCallStack =>
  PA.ValidArch arch =>
  PPa.PatchPair (PMC.BinaryContext arch) ->
  PC.PatchData ->
  CME.ExceptT (PEE.EquivalenceError arch) IO (UnpackedPatchData arch)
unpackPatchData contexts (PC.PatchData pairs (oIgn,pIgn) eqFuncs) =
   do pairs' <-
         DT.forM pairs $ \(bd, bd') ->
            PPa.PatchPair
              <$> unpackBlockData (PPa.pOriginal contexts) bd
              <*> unpackBlockData (PPa.pPatched contexts) bd'

      let f (PC.Hex w) = PAd.memAddrToAddr . MM.absoluteAddr . MM.memWord $ w
      let g (PC.Hex loc, PC.Hex len) = (MM.memWord loc, toInteger len)

      let oIgn' = map g oIgn
      let pIgn' = map g pIgn

      let eqFuncs' = [ (f o, f p)
                     | (o, p) <- eqFuncs
                     ]

      return UnpackedPatchData { unpackedPairs = pairs'
                               , unpackedOrigIgnore = oIgn'
                               , unpackedPatchIgnore = pIgn'
                               , unpackedEquatedFuncs = eqFuncs'
                               }

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
  PA.ValidArch arch =>
  EquivEnv sym arch ->
  -- | A list of block pairs to test for equivalence. They must be the entry points of a functions.
  [PPa.FunPair arch] ->
  IO (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
runVerificationLoop env pPairs = do
  result <- CME.runExceptT $ runEquivM env doVerify
  case result of
    Left err -> withValidEnv env $ error (show err)
    Right r -> return r

  where
    doVerify :: EquivM sym arch (PEq.EquivalenceStatus, PESt.EquivalenceStatistics)
    doVerify = do
      triples <- DT.forM pPairs $ \p -> topLevelTriple p
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

  void $ withSimSpec pPair (PF.eqPreDomain triple) $ \stO stP precond -> do
    let
      inO = SimInput stO (PPa.pOriginal pPair)
      inP = SimInput stP (PPa.pPatched pPair)
    (_, genPrecond) <- liftIO $ bindSpec sym stO stP genPrecondSpec
    preImpliesGen <- liftIO $ impliesPredomain sym stackRegion inO inP eqRel precond genPrecond
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
    emitEvent (PE.ProvenGoal blocks (PFI.SomeProofNonceExpr vsym proof))
  case PFO.proofResult (PF.unNonceProof proof) of
    PF.VerificationSuccess -> return PEq.Equivalent
    PF.VerificationFail _ cond -> case W4.asConstantPred (PF.condEqPred cond) of
      Just False -> return PEq.Inequivalent
      _ -> return PEq.ConditionallyEquivalent
    _ -> return PEq.Inequivalent
  where
    pPair = PF.eqPair triple
    postcondSpec = PF.eqPostDomain triple

--------------------------------------------------------
-- Simulation



-- | Simulate the given block pair, or retrieve a cached result from a previous
-- simulation. Execute the given function in a context where the given 'SimBundle'
-- is valid (i.e. its bound variables are marked free and its preconditions are assumed).
-- In this resulting 'f' these free variables are then bound in the 'SimSpec', resulting
-- in a closed "term".
-- The resulting 'prf' is used for returning additional information (i.e. a proof node) that
-- is not necessarily traversable according to 'PEM.ExprMappable', and therefore is not
-- closed under the resulting 'SimSpec'.
withSimBundle ::
  (HasCallStack, PEM.ExprMappable sym f) =>
  PPa.BlockPair arch ->
  (SimBundle sym arch -> EquivM sym arch (f, prf)) ->
  EquivM sym arch (SimSpec sym arch f, prf)
withSimBundle pPair f = fmap unzipSkipTransformation $ withEmptyAssumptionFrame $ withSym $ \sym -> do
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

      (asm,(r, prf)) <- withAssumption (liftIO $ allPreds sym [asmO, asmP]) $ do
        let bundle = SimBundle (PPa.PatchPair simInO_ simInP_) (PPa.PatchPair simOutO' simOutP')
        bundle' <- applyCurrentFrame bundle
        f bundle'
      return (frameAssume asm, (r, PEM.SkipTransformation prf))

trivialGlobalMap :: MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap = MS.GlobalMap $ \_ _ reg off -> pure (CLM.LLVMPointer reg off)

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

-- | Prove that the given equivalence domain holds when starting execution from the given
-- block pair. Returns a computed pre-domain that must be initially equivalent, in order
-- for the given post-domain to hold.
provePostcondition ::
  HasCallStack =>
  PPa.BlockPair arch ->
  DomainSpec sym arch ->
  EquivM sym arch (DomainSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
provePostcondition pPair postcondSpec = do
  traceBlockPair pPair "Entering provePostcondition"
  emitPreamble pPair
  catchSimBundle pPair postcondSpec $ \bundle ->
    provePostcondition' bundle postcondSpec

catchSimBundle ::
  forall sym arch ret.
  (HasCallStack, ret ~ (DomainSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)) =>
  PPa.BlockPair arch ->
  DomainSpec sym arch ->
  (SimBundle sym arch -> EquivM sym arch (PED.EquivalenceDomain sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)  ) ->
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
          Right r -> return r
      let triple = PF.EquivTriple pPair precondSpec postcondSpec
      future <- PFO.asFutureNonceApp prf
      modifyBlockCache envProofCache pPair (++) [(triple, future)]
      return $ (precondSpec, prf)
  where
    firstCached (x:xs) = getCached x >>= \case
      Just r -> return $ Just r
      Nothing -> firstCached xs
    firstCached [] = return Nothing

    getCached ::
      (PF.EquivTriple sym arch, Par.Future (PF.ProofNonceApp sym arch PF.ProofBlockSliceType)) ->
      EquivM sym arch (Maybe ret)
    getCached (triple, futureProof) = do
      traceBlockPair pPair "Checking for cached result"
      impliesPostcond pPair (PF.eqPostDomain triple) postcondSpec >>= \case
        True -> do
          traceBlockPair pPair "Cache hit"
          prf' <- PFO.wrapFutureNonceApp futureProof
          return $ Just (PF.eqPreDomain triple, prf')
        False -> do
          traceBlockPair pPair "Cache miss"
          return Nothing

    errorResult :: EquivM sym arch ret
    errorResult = fmap unzipProof $ withSym $ \sym -> withFreshVars pPair $ \stO stP -> do
      let
        simInO_ = SimInput stO (PPa.pOriginal pPair)
        simInP_ = SimInput stP (PPa.pPatched pPair)
      traceBlockPair pPair "Caught an error, so making a trivial block slice"
      PA.SomeValidArch (PA.validArchFunctionDomain -> externalDomain) <- CMR.asks envValidArch
      r <- trivialBlockSlice False externalDomain (PPa.PatchPair simInO_ simInP_) postcondSpec
      return $ (W4.truePred sym, r)


impliesPostcond ::
  PPa.BlockPair arch ->
  DomainSpec sym arch ->
  DomainSpec sym arch ->
  EquivM sym arch Bool
impliesPostcond blocks stPredAsm stPredConcl = withSym $ \sym -> do
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  fmap specBody $ withFreshVars blocks $ \stO stP -> do
    p <- liftIO $ impliesPostdomainPred sym (PPa.PatchPair stO stP) stPredAsm stPredConcl
    b <- isPredTrue' heuristicTimeout p
    return $ (W4.truePred sym, b)

data BranchCase sym arch =
  BranchCase
    { -- | predicate that asserts equality on the pre-state, derived
      -- from the 'branchPreStPred' but stored here to avoid re-computing it
      branchPrePred :: W4.Pred sym
      -- | the structured pre-domain for this branch
    , branchPreDomain :: PED.EquivalenceDomain sym arch
      -- | target for the function call
    , branchBlocks :: PPa.BlockPair arch
      -- | the deferred proof that the pre-domain is sufficient to establish
      -- the target post-domain
    , branchProofTriple :: PFO.LazyProof sym arch PF.ProofTripleType
    }

unzipSkipTransformation ::
  SimSpec sym arch (a, PEM.SkipTransformation b) ->
  (SimSpec sym arch a, b)
unzipSkipTransformation spec = (fmap fst spec, PEM.unSkip $ snd $ specBody spec)

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
  DomainSpec sym arch ->
  EquivM sym arch (PED.EquivalenceDomain sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
trivialBlockSlice isSkipped (PVE.ExternalDomain externalDomain) in_ postcondSpec = withSym $ \sym -> do
  blkEnd <- liftIO $ MS.initBlockEnd (Proxy @arch) sym
  transition <- PFO.noTransition in_ blkEnd
  preUniv <- externalDomain sym
  prf <- PFO.lazyProofEvent_ pPair $ do
    triple <- PFO.lazyProofEvent_ pPair $ do
      preDomain <- PFO.domainToProof preUniv
      postDomain <- PFO.domainSpecToProof postcondSpec
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
  DomainSpec sym arch ->
  EquivM sym arch (PED.EquivalenceDomain sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
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
            (PB.BlockEntryPreArch, PB.BlockEntryPreArch) -> return True
            (entryO, entryP) | entryO == entryP -> return False
            _ -> throwHere $ PEE.BlockExitMismatch
          traceBundle bundle ("  Is Syscall? " ++ show isSyscall)
          withNoFrameGuessing isSyscall $ do
            -- These are the preconditions that must hold *when the callee returns*
            (contPre, contPrf) <- provePostcondition (PPa.PatchPair blkRetO blkRetP) postcondSpec
            traceBundle bundle "finished proving postcondition"

            -- Now figure out how to handle the callee
            ctx <- view PME.envCtxL
            let isEquatedCallSite = any (PPa.matchEquatedAddress pPair) (PMC.equatedFunctions ctx)

            (funCallPre, funCallSlicePrf) <-
              if | isSyscall -> fmap unzipProof $ withFreshVars pPair $ \_stO _stP -> do
                   -- For arch exits (i.e. syscalls) we assume that equivalence will hold on
                   -- any post domain if the pre-domain is exactly equal: i.e. any syscall is
                   -- treated as an uninterpreted function that reads the entire machine state
                   -- this can be relaxed with more information about the specific call
                   traceBundle bundle ("  Making a trivial block slice because this is a system call")
                   PA.SomeValidArch (PA.validArchSyscallDomain -> syscallDomain) <- CMR.asks envValidArch
                   r <- trivialBlockSlice True syscallDomain (simIn bundle) postcondSpec
                   return $ (W4.truePred sym, r)
                 | isEquatedCallSite -> do
                     -- If the call is to our distinguished function (provided
                     -- as an input), do not call provePostcondition'. Instead,
                     -- symbolically execute the function (with whatever setup
                     -- is required to enable us to summarize the memory
                     -- effects) using more traditional macaw-symbolic setups.
                     traceBundle bundle ("  Inlining equated callees " ++ show pPair)
                     inlineCallee contPre pPair
                 | otherwise -> catchSimBundle pPair postcondSpec $ \bundleCall -> do
                     -- Otherwise, just recursively traverse the callee
                     traceBundle bundle ("  Recursively proving the postcondition of the call target " ++ show pPair)
                     provePostcondition' bundleCall contPre

            -- equivalence condition for the function entry
            traceBundle bundle "Proving local postcondition for call return"
            branchCase <- proveLocalPostcondition bundle funCallPre
            traceBundle bundle "Generating a ProofFunctionCall obligation"
            let
              prf = PF.ProofFunctionCall
                      { PF.prfFunctionCallPre = branchProofTriple branchCase
                      , PF.prfFunctionCallBody = funCallSlicePrf
                      , PF.prfFunctionCallContinue = Just contPrf
                      , PF.prfFunctionCallMetadata = PB.concreteAddress blkO
                      }
            return (branchCase, prf)

        (Nothing, Nothing) -> do
          traceBundle bundle "No return target identified"
          (contPre, contPrf) <- provePostcondition (PPa.PatchPair blkO blkP) postcondSpec
          branchCase <- proveLocalPostcondition bundle contPre
          let
            prf = PF.ProofFunctionCall
                    { PF.prfFunctionCallPre = branchProofTriple branchCase
                    , PF.prfFunctionCallBody = contPrf
                    , PF.prfFunctionCallContinue = Nothing
                    , PF.prfFunctionCallMetadata = PB.concreteAddress blkO
                    }
          return (branchCase, prf)
        _ -> do
          traceBundle bundle "BlockExitMismatch"
          throwHere $ PEE.BlockExitMismatch
  traceBundle bundle ("Finished proving obligations for all call targets (" ++ show (length funCallProofCases) ++ ")")
  -- if we have a "return" exit, prove that it satisfies the postcondition
  -- as a special case, if the original binary is determined to abort,
  -- we consider that to be equivalent to a return
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  isReturn <- do
    bothReturn <- PD.matchingExits bundle MS.MacawBlockEndReturn
    abortO <- PAb.isAbortedStatePred (PPa.getPair @PBi.Original (simOut bundle))
    returnP <- liftIO $ MS.isBlockEndCase (Proxy @arch) sym (simOutBlockEnd $ simOutP bundle) MS.MacawBlockEndReturn
    abortCase <- liftIO $ W4.andPred sym abortO returnP
    liftIO $ W4.orPred sym bothReturn abortCase

  precondReturn <- withSatAssumption goalTimeout (return isReturn) $ do
    traceBundle bundle "Attempting to prove local postconditions"
    proveLocalPostcondition bundle postcondSpec
  let
    -- for simplicitly, we drop the condition on the return case, and assume
    -- it is taken if all other cases are false, which is checked by 'checkCasesTotal'
    returnByDefault = case precondReturn of
      Just (_, br) -> branchPreDomain br
      Nothing -> PED.empty sym

  traceBundle bundle "Checking exits"
  -- an exit that was not classified
  isUnknown <- do
    isJump <- PD.matchingExits bundle MS.MacawBlockEndJump
    isFail <- PD.matchingExits bundle MS.MacawBlockEndFail
    isBranch <- PD.matchingExits bundle MS.MacawBlockEndBranch
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

  blockSlice <- PFO.simBundleToSlice bundle
  postDomain <- PFO.domainSpecToProof postcondSpec

  traceBundle bundle "Generating triple"
  (precond, triple) <- case allPreconds of
    -- In the case where no exits are found, but both programs call the same unknown function,
    -- we treat this slice as an uninterpreted function call (propagating an external domain)
    [] -> PD.isMatchingCall bundle >>= \case
      True -> do
        traceBundle bundle "No block exits found, treating slice as uninterpeted"
        PA.SomeValidArch (PA.validArchFunctionDomain -> PVE.ExternalDomain externalDomain) <- CMR.asks envValidArch
        preUniv <- externalDomain sym
        PFO.lazyProofEvent (simPair bundle) $ do
          preDomain <- PFO.domainToProof preUniv
          status <- PFO.lazyProofApp $ PF.ProofStatus PF.Unverified
          return $ (preUniv, PF.ProofTriple (simPair bundle) preDomain postDomain status)
        -- at this point we have no recourse - no matching block exits have been found and we can't
        -- prove that the slices call the same unknown function, and so this is undefined
      False -> throwHere PEE.BlockEndClassificationFailure
    -- Otherise, mux the preconditions of the branches to compute the final precondition
    _ -> do
      precond' <- F.foldrM (\(p, br) stPred -> liftIO $ PED.mux sym p (branchPreDomain br) stPred)  returnByDefault funCallCases

      precond <- withAssumption_ (liftIO $ anyPred sym (map fst allPreconds)) $
        PVSi.simplifySubPreds precond'

      traceBundle bundle "Computing proof triple and ensuring that cases are total"
      -- TODO: this needs to be reorganized to make the domain results actually lazy

      PFO.lazyProofEvent (simPair bundle) $ do
        preDomain <- PFO.domainToProof precond
        status <- checkCasesTotal bundle preDomain allPreconds
        return $ (precond, PF.ProofTriple (simPair bundle) preDomain postDomain status)
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


-- | Prove a local postcondition (i.e. it must hold when the slice exits) for a pair of slices
proveLocalPostcondition ::
  HasCallStack =>
  SimBundle sym arch ->
  DomainSpec sym arch ->
  EquivM sym arch (BranchCase sym arch)
proveLocalPostcondition bundle postcondSpec = withSym $ \sym -> do
  traceBundle bundle "proveLocalPostcondition"
  eqRel <- CMR.asks envBaseEquiv
  (asm, postcond) <- liftIO $ bindSpec sym (simOutState $ simOutO bundle) (simOutState $ simOutP bundle) postcondSpec
  (_, postcondPred) <- liftIO $ getPostdomain sym bundle eqRel postcond

  traceBundle bundle "guessing equivalence domain"
  eqInputs <- withAssumption_ (return asm) $ do
    PVD.guessEquivalenceDomain bundle postcondPred postcond
  traceBundle bundle ("Equivalence domain has: " ++ show (PER.toList $ PED.eqDomainRegisters eqInputs))

  -- TODO: avoid re-computing this
  blockSlice <- PFO.simBundleToSlice bundle
  let sliceState = PF.slBlockPostState blockSlice

  stackRegion <- CMR.asks (PMC.stackRegion . PME.envCtx)
  eqInputsPred <- liftIO $ getPredomain sym stackRegion bundle eqRel eqInputs

  notChecks <- liftIO $ W4.notPred sym postcondPred
  blocks <- PD.getBlocks $ simPair bundle

  traceBundle bundle ("Postcondition Predicate:\n" ++ show (W4.printSymExpr postcondPred))

  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  triple <- PFO.lazyProofEvent_ (simPair bundle) $ do
    preDomain <- PFO.domainToProof eqInputs
    postDomain <- PFO.domainSpecToProof postcondSpec
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
                PF.ProofDomain preDomain' <- PFO.lazyProofAtom preDomain
                PF.ProofDomain postDomain' <- PFO.lazyProofAtom postDomain
                ir <- PFC.getInequivalenceResult PEE.InvalidPostState preDomain' postDomain' blockSlice fn
                traceBundle bundle "Got inequivalence result"
                emitEvent (PE.CheckedEquivalence blocks (PE.Inequivalent ir))
                return $ PF.VerificationFail ir (PF.emptyCondEqResult sym)
          traceBundle bundle "Finished SAT check"
          case r of
            Right r' -> return r'
            Left exn -> do
              traceBundle bundle ("Solver exception: " ++ show exn)
              -- FIXME: Have a more detailed marker, possibly an explanation as to why it is unverified
              return $ PF.Unverified
        status' <- case status of
          PF.VerificationFail _ _ -> do
            traceBundle bundle "The verification failed"
            withAssumptionFrame_ (PVD.equateInitialStates bundle) $ do
              notGoal <- applyCurrentFrame notChecks
              goal <- applyCurrentFrame postcondPred

              traceBundle bundle "Checking goal satisfiability"
              withAssumption_ (return asm) $ do
                isPredSat goalTimeout goal >>= \case
                  True -> do
                    traceBundle bundle "Minimizing condition"
                    PF.ProofDomain postDomain' <- PFO.lazyProofAtom postDomain
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
                          traceBundle bundle "proveLocalPostcondition->getInequivalenceResult"
                          ir <- PFC.getInequivalenceResult PEE.InvalidPostState (PVD.universalDomain sym) postDomain' blockSlice fn
                          traceBundle bundle "proveLocalPostcondition->getEquivalenceResult"
                          cr' <- getCondEquivalenceResult bundle cond'' fn
                          cr <- applyCurrentFrame cr'
                          traceBundle bundle ("conditionalEquivalenceResult: " ++ show (W4.printSymExpr (PF.condEqPred cr)))
                          return $ PF.VerificationFail ir cr
                        W4R.Unsat _ -> return $ status
                        W4R.Unknown -> return $ status
                    case er of
                      Right r -> return r
                      Left exn -> do
                        traceBundle bundle ("Solver failure: " ++ show exn)
                        return status
                  False -> return $ status
          _ -> return $ status
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
  EquivM sym arch (PF.CondEquivalenceResult sym arch)
getCondEquivalenceResult bundle eqCond fn = do
  binds <- PFC.getCondEquivalenceBindings eqCond fn
  abortValid <- PAb.proveAbortValid bundle eqCond
  return $ PF.CondEquivalenceResult binds eqCond abortValid


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
  PF.BlockSliceState sym arch ->
  -- | equivalence post-domain
  PED.EquivalenceDomain sym arch ->
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
            pathCond' <- PFC.getPathCondition bundle sliceState postDomain fn
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
  PF.BlockSliceState sym arch ->
  -- | equivalence post-domain
  PED.EquivalenceDomain sym arch ->
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
            pathCond' <- PFC.getPathCondition bundle sliceState postDomain fn
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
  EquivM sym arch (PER.RegisterDomain sym arch)
topLevelPostRegisterDomain = return $ PER.empty

-- | Default toplevel post-domain:
--   global (non-stack) memory
topLevelPostDomain ::
  HasCallStack =>
  PPa.BlockPair arch ->
  EquivM sym arch (DomainSpec sym arch)
topLevelPostDomain pPair = withFreshVars pPair $ \stO stP -> withSym $ \sym -> do
  regDomain <- topLevelPostRegisterDomain
  withAssumptionFrame (PVV.validInitState Nothing stO stP) $
    return $ PED.EquivalenceDomain
      {
        PED.eqDomainRegisters = regDomain
      , PED.eqDomainStackMemory = PEM.empty sym
      , PED.eqDomainGlobalMemory = PEM.universal sym
      }

-- | Top-level equivalence check:
--  predomain:
--   all registers, stack, and memory
--   IPs match given patchpair
-- postdomain:
--   global (non-stack) memory
topLevelTriple ::
  HasCallStack =>
  PPa.FunPair arch ->
  EquivM sym arch (PF.EquivTriple sym arch)
topLevelTriple fnPair =
  let pPair = TF.fmapF PB.functionEntryToConcreteBlock fnPair in
  withPair pPair $
  withSym $ \sym -> do
    let regDomain = PER.universal sym
    postcond <- topLevelPostDomain pPair
    precond <- withFreshVars pPair $ \stO stP -> do
      withAssumptionFrame (PVV.validInitState (Just pPair) stO stP) $
        return $ PED.EquivalenceDomain
          { PED.eqDomainRegisters = regDomain
          , PED.eqDomainStackMemory = PEM.universal sym
          , PED.eqDomainGlobalMemory = PEM.universal sym
          }
    return $ PF.EquivTriple pPair precond postcond

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
    casePreds <- mapM (\c -> getCase c) cases
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
          PF.ProofDomain preDomain' <- PFO.lazyProofAtom preDomain
          -- TODO: a different counter-example type would be appropriate here, which explicitly
          -- doesn't consider the post-state. At this point we aren't interested in the target
          -- post-domain because we're just making sure that the given cases cover all possible exits,
          -- without considering the equivalence of the state at those exit points.
          ir <- PFC.getInequivalenceResult PEE.InvalidCallPair preDomain' (PED.empty sym) blockSlice fn
          emit $ PE.BranchesIncomplete ir
          -- no conditional equivalence case
          return $ PF.VerificationFail ir (PF.emptyCondEqResult sym)
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
