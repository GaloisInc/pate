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

import           GHC.Stack ( HasCallStack )
import qualified Control.Concurrent.Async as CCA
import           Control.Monad ( void, unless )
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans as CMT

import           Control.Applicative
import           Control.Lens hiding ( op, pre )
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO )

import qualified Prettyprinter as PP

import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Functor.Compose as DFC
import qualified Data.List as DL
import           Data.Maybe ( catMaybes, maybeToList )
import qualified Data.Map as M
import           Data.Proxy ( Proxy(..) )
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import           Data.String ( fromString )
import qualified Data.Text as T
import qualified Data.Time as TM
import qualified Data.Traversable as DT
import           GHC.TypeLits
import qualified Lumberjack as LJ
import qualified System.IO as IO
import qualified Data.Word.Indexed as W

import qualified Data.Macaw.BinaryLoader.PPC as TOC (HasTOC(..))
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Symbolic as MS


import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.Map as MapF

import qualified Lang.Crucible.Backend.Simple as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS
import qualified Lang.Crucible.Types as CT

import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4L
import qualified What4.Symbol as WS
import qualified What4.SatResult as W4R

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import           Pate.Equivalence
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.Hints as PH
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Proof as PF
import           Pate.Proof.Ground as PFG
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Proof.Operations as PFO
import qualified Pate.Parallel as Par
import           Pate.SimState
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PS
import           Pate.Types
import           What4.ExprHelpers

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
  -> PB.LoadedELF arch
  -> PB.LoadedELF arch
  -> CME.ExceptT (EquivalenceError arch) IO (MM.ArchSegmentOff arch, ParsedFunctionMap arch, MM.ArchSegmentOff arch, ParsedFunctionMap arch)
runDiscovery logAction mhints elf elf' = do
  let discoverAsync e h = liftIO (CCA.async (CME.runExceptT (PD.runDiscovery e h)))
  origDiscovery <- discoverAsync elf mempty
  mHintedDiscovery <- DT.traverse (discoverAsync elf) mhints
  patchedDiscovery <- discoverAsync elf' mempty
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
  LJ.LogAction IO (PE.Event arch) ->
  Maybe PH.VerificationHints ->
  PB.LoadedELF arch ->
  PB.LoadedELF arch ->
  BlockMapping arch ->
  PC.VerificationConfig ->
  [BlockPair arch] ->
  CME.ExceptT (EquivalenceError arch) IO Bool
verifyPairs logAction mhints elf elf' blockMap vcfg pPairs = do
  Some gen <- liftIO N.newIONonceGenerator
  vals <- case MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) of
    Nothing -> CME.throwError $ equivalenceError UnsupportedArchitecture
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
  let
    exts = MT.macawTraceExtensions eval model (trivialGlobalMap @_ @arch) undefops

    oCtx = BinaryContext
      { binary = PB.loadedBinary elf
      , parsedFunctionMap = oPfm
      , binEntry = oMain
      }
    rCtx = BinaryContext
      { binary = PB.loadedBinary elf'
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
      , envValidSym = Sym sym adapter
      , envStartTime = startedAt
      , envTocs = (TOC.getTOC $ PB.loadedBinary elf, TOC.getTOC $ PB.loadedBinary elf')
      -- TODO: restructure EquivEnv to avoid this
      , envCurrentFunc = error "no function under analysis"
      , envCurrentFrame = mempty
      , envNonceGenerator = gen
      , envParentNonce = Some topNonce
      }

  liftIO $ do
    stats <- runVerificationLoop env pPairs
    IO.liftIO $ LJ.writeLog logAction (PE.AnalysisEnd stats)
    return $ equivSuccess stats

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
  [BlockPair arch] ->
  IO EquivalenceStatistics
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
    doVerify :: EquivM sym arch EquivalenceStatistics
    doVerify = do
      pPairs' <- ifConfig (not . PC.cfgPairMain) (return pPairs) $ do
        mainO <- CMR.asks $ binEntry . originalCtx . envCtx
        mainP <- CMR.asks $ binEntry . rewrittenCtx . envCtx
        blkO <- PD.mkConcreteBlock BlockEntryInitFunction mainO
        blkP <- PD.mkConcreteBlock BlockEntryInitFunction mainP
        let pPair = PatchPair blkO blkP
        return $ pPair : pPairs
      triples <- DT.forM pPairs' $ topLevelTriple
      CMR.local (\env' -> env' { envGoalTriples = triples } ) $
        F.forM_ triples go
      CMS.gets stEqStats

    go ::
      PF.EquivTriple sym arch -> EquivM sym arch ()
    go triple = do
      result <- manifestError $ checkEquivalence triple
      emitResult result
      normResult <- return $ case result of 
        Left _ -> EquivalenceStatistics 1 0 1
        Right False -> EquivalenceStatistics 1 0 0
        Right True -> EquivalenceStatistics 1 1 0
      CMS.modify' $ \st -> st { stEqStats = normResult <> (stEqStats st) }

ifConfig ::
  (PC.VerificationConfig -> Bool) ->
  EquivM sym arch a ->
  EquivM sym arch a ->
  EquivM sym arch a
ifConfig checkCfg ifT ifF = (CMR.asks $ checkCfg . envConfig) >>= \case
  True -> ifT
  False -> ifF

emitPreamble :: BlockPair arch -> EquivM sym arch ()
emitPreamble pPair = emitEvent (\_ -> PE.AnalysisStart pPair)

emitResult :: Either (EquivalenceError arch) a -> EquivM sym arch ()
emitResult (Left err) = emitEvent (\_ -> PE.ErrorRaised err)
emitResult (Right _) = return ()

-- | Verify that the given triple: that a pair of blocks yield equivalent
-- states on the post-domain, assuming equality on the pre-domain.
-- Returns 'True' if the pairs are proven equivalent, and 'False' if
-- the generated proof contains an inequivalence counterexample.
checkEquivalence ::
  HasCallStack =>
  PF.EquivTriple sym arch ->
  EquivM sym arch Bool
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
      inO = SimInput stO (pOriginal pPair)
      inP = SimInput stP (pPatched pPair)
      precond = PF.eqPreDomain tripleBody
    (_, genPrecond) <- liftIO $ bindSpec sym stO stP genPrecondSpec
    preImpliesGen <- liftIO $ impliesPrecondition sym stackRegion inO inP eqRel precond genPrecond
    -- prove that the generated precondition is implied by the given precondition
    goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
    isPredTrue goalTimeout preImpliesGen >>= \case
      True -> return ()
      False -> throwHere ImpossibleEquivalence

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
    PF.VerificationSuccess -> return True
    _ -> return False
  where
    -- TODO: this breaks the model somewhat, since we're relying on these not containing
    -- the bound terms
    pPair = PF.eqPair $ specBody triple
    postcondSpec = PF.eqPostDomain $ specBody triple
  
--------------------------------------------------------
-- Simulation

simulate ::
  forall sym arch bin.
  KnownBinary bin =>
  SimInput sym arch bin ->
  EquivM sym arch (W4.Pred sym, SimOutput sym arch bin)
simulate simInput = withBinary @bin $ do
  -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
  CC.SomeCFG cfg <- do
    CC.Some (DFC.Compose pbs_) <- PD.lookupBlocks (simInBlock simInput)
    let pb:pbs = DL.sortOn MD.pblockAddr pbs_
        -- There's a slight hack here.
        --
        -- The core problem we're dealing with here is that renovate blocks
        -- can have multiple basic blocks; and almost always do in the
        -- rewritten binary. We want to stitch them together in the right
        -- way, and part of that means deciding whether basic block
        -- terminators are things we should "follow" to their target to
        -- continue symbolically executing or not. Normally any block
        -- terminator that goes to another basic block in the same renovate
        -- block is one we want to keep symbolically executing through.
        --
        -- BUT if there is an actual self-contained loop within a single
        -- renovate block, we want to avoid trying to symbolically execute
        -- that forever, so we'd like to pick some of the edges in the
        -- "block X can jump to block Y" graph that break all the cycles,
        -- and mark all of those as terminal for the purposes of CFG
        -- creation.
        --
        -- Instead of doing a careful analysis of that graph, we adopt the
        -- following heuristic: kill any edges that point to the entry
        -- point of the renovate block, and symbolically execute through
        -- all the others. This catches at the very least any
        -- single-basic-block loops in the original binary and in most
        -- cases even their transformed version in the rewritten binary. If
        -- we ever kill such an edge, we have certainly broken a cycle; but
        -- cycles could appear in other ways that we don't catch.
        --
        -- This heuristic is reflected in the code like this: when deciding
        -- if a jump should be killed, we compare jump targets to a
        -- collection of "internal" addresses, and kill it if the target
        -- isn't in that collection. Then we omit the entry point's address
        -- from that collection, so that jumps to it are considered terminal.

        -- Multiple ParsedBlocks may have the same address, so the delete
        -- is really needed.
        internalAddrs = S.delete (MD.pblockAddr pb) $ S.fromList [MD.pblockAddr b | b <- pbs]
        (terminal_, nonTerminal) = DL.partition isTerminalBlock pbs
        terminal = [pb | isTerminalBlock pb] ++ terminal_
        killEdges =
          concatMap (backJumps internalAddrs) (pb : pbs) ++
          concatMap (externalTransitions internalAddrs) (pb:pbs)
    fns <- archFuns
    ha <- CMR.asks $ handles . envCtx
    be <- CMR.asks envBlockEndVar
    liftIO $ MS.mkBlockSliceCFG fns ha (W4L.OtherPos . fromString . show) pb nonTerminal terminal killEdges (Just be)
  let preRegs = simInRegs simInput
  preRegsAsn <- regStateToAsn preRegs
  archRepr <- archStructRepr
  let regs = CS.assignReg archRepr preRegsAsn CS.emptyRegMap
  globals <- getGlobals simInput
  cres <- evalCFG globals regs cfg
  (asm, postRegs, memTrace, exitClass) <- getGPValueAndTrace cres

  return $ (asm, SimOutput (SimState memTrace postRegs) exitClass)

archStructRepr :: forall sym arch. EquivM sym arch (CC.TypeRepr (MS.ArchRegStruct arch))
archStructRepr = do
  archFs <- archFuns
  return $ CC.StructRepr $ MS.crucArchRegTypes archFs

isTerminalBlock :: MD.ParsedBlock arch ids -> Bool
isTerminalBlock pb = case MD.pblockTermStmt pb of
  MD.ParsedCall{} -> True
  MD.PLTStub{} -> True
  MD.ParsedJump{} -> False
  MD.ParsedBranch{} -> False
  MD.ParsedLookupTable{} -> False
  MD.ParsedReturn{} -> False
  MD.ParsedArchTermStmt{} -> True -- TODO: think harder about this
  MD.ParsedTranslateError{} -> True
  MD.ClassifyFailure{} -> True

-- FIXME: this is hardly rigorous
-- | Kill back jumps within the function
backJumps ::
  Set (MM.ArchSegmentOff arch) ->
  MD.ParsedBlock arch ids ->
  [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
backJumps internalAddrs pb =
  [ (MD.pblockAddr pb, tgt)
  | tgt <- case MD.pblockTermStmt pb of
     MD.ParsedJump _ tgt -> [tgt]
     MD.ParsedBranch _ _ tgt tgt' -> [tgt, tgt']
     MD.ParsedLookupTable _jt _ _ tgts -> F.toList tgts
     _ -> []
  , tgt < MD.pblockAddr pb
  , tgt `S.member` internalAddrs
  ]


externalTransitions ::
  Set (MM.ArchSegmentOff arch) ->
  MD.ParsedBlock arch ids ->
  [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
externalTransitions internalAddrs pb =
  [ (MD.pblockAddr pb, tgt)
  | tgt <- case MD.pblockTermStmt pb of
      MD.ParsedCall{} -> []
      MD.PLTStub{} -> []
      MD.ParsedJump _ tgt -> [tgt]
      MD.ParsedBranch _ _ tgt tgt' -> [tgt, tgt']
      MD.ParsedLookupTable _jt _ _ tgts -> F.toList tgts
      MD.ParsedReturn{} -> []
      MD.ParsedArchTermStmt{} -> [] -- TODO: think harder about this
      MD.ParsedTranslateError{} -> []
      MD.ClassifyFailure{} -> []
  , tgt `S.notMember` internalAddrs
  ]

-- | Simulate the given block pair, or retrieve a cached result from a previous
-- simulation. Execute the given function in a context where the given 'SimBundle'
-- is valid (i.e. its bound variables are marked free and its preconditions are assumed).
withSimBundle ::
  PEM.ExprMappable sym f =>
  BlockPair arch ->
  (SimBundle sym arch -> EquivM sym arch f) ->
  EquivM sym arch (SimSpec sym arch f)
withSimBundle pPair f = withSym $ \sym -> do
  results <- CMS.gets stSimResults
  bundleSpec <- case M.lookup pPair results of
    Just bundleSpec -> return bundleSpec    
    Nothing -> do
      bundleSpec <- withFreshVars $ \stO stP -> do
        let
          simInO_ = SimInput stO (pOriginal pPair)
          simInP_ = SimInput stP (pPatched pPair)
        withAssumptionFrame' (validInitState (Just pPair) stO stP) $ do
          (asmO, simOutO_) <- simulate simInO_
          (asmP, simOutP_) <- simulate simInP_
          (asmO', simOutO') <- withAssumptionFrame (validConcreteReads simOutO_) $ return simOutO_
          (asmP', simOutP') <- withAssumptionFrame (validConcreteReads simOutP_) $ return simOutP_

          asm <- liftIO $ allPreds sym [asmO, asmP, asmO', asmP']
          return $ (frameAssume asm, SimBundle (PatchPair simInO_ simInP_) (PatchPair simOutO' simOutP'))
      CMS.modify' $ \st -> st { stSimResults = M.insert pPair bundleSpec (stSimResults st) }
      return bundleSpec
  withSimSpec bundleSpec $ \_ _ bundle -> f bundle

trivialGlobalMap :: MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap _ _ reg off = pure (CLM.LLVMPointer reg off)

-- TODO: What should happen if the Pred sym in a PartialRes in pres or pres' is false?
getGPValueAndTrace ::
  forall sym arch p ext.
  CS.ExecResult p sym ext (CS.RegEntry sym (MS.ArchRegStruct arch)) ->
  EquivM sym arch
    ( W4.Pred sym
    , MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym)
    , MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    , CS.RegValue sym (MS.MacawBlockEndType arch)
    )
getGPValueAndTrace (CS.FinishedResult _ pres) = withSym $ \sym -> do
  mem <- CMR.asks envMemTraceVar
  eclass <- CMR.asks envBlockEndVar
  asm <- case pres of
    CS.TotalRes _ -> return $ W4.truePred sym
    CS.PartialRes _ p _ _ -> return p

  case pres ^. CS.partialValue of
    CS.GlobalPair val globs
      | Just mt <- CGS.lookupGlobal mem globs
      , Just ec <- CGS.lookupGlobal eclass globs -> withValid $ do
        val' <- structToRegState @sym @arch val
        return $ (asm, val', mt, ec)
    _ -> throwHere MissingCrucibleGlobals
getGPValueAndTrace (CS.AbortedResult _ ar) = throwHere . SymbolicExecutionFailed . ppAbortedResult $ ar
getGPValueAndTrace (CS.TimeoutResult _) = throwHere (SymbolicExecutionFailed "timeout")

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"

structToRegState :: forall sym arch.
  CS.RegEntry sym (MS.ArchRegStruct arch) ->
  EquivM sym arch (MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym))
structToRegState e = do
  archVs <- CMR.asks $ envArchVals
  return $ MM.mkRegState (PSR.macawRegEntry . MS.lookupReg archVs e)

regStateToAsn :: forall sym arch.
  HasCallStack =>
  MM.RegState (MM.ArchReg arch) (PSR.MacawRegEntry sym) ->
  EquivM sym arch (Ctx.Assignment (CS.RegValue' sym)  (MS.MacawCrucibleRegTypes arch))
regStateToAsn regs = do
  archFs <- archFuns
  let allRegsAsn = MS.crucGenRegAssignment archFs
  return $ MS.macawAssignToCruc (\(PSR.MacawRegEntry _ v) -> CS.RV @sym v) $
    TFC.fmapFC (\r -> regs ^. MM.boundValue r) allRegsAsn

getGlobals ::
  forall sym arch bin.
  SimInput sym arch bin ->
  EquivM sym arch (CS.SymGlobalState sym)
getGlobals simInput = withValid $ withSym $ \sym -> do
  env <- CMR.ask
  blkend <- liftIO $ MS.initBlockEnd (Proxy @arch) sym
  return $
      CGS.insertGlobal (envMemTraceVar env) (simInMem simInput)
    $ CGS.insertGlobal (envBlockEndVar env) blkend
    $ CGS.emptyGlobals

evalCFG ::
  CS.SymGlobalState sym ->
  CS.RegMap sym tp ->
  CC.CFG (MS.MacawExt arch) blocks tp (MS.ArchRegStruct arch) ->
  EquivM sym arch (CS.ExecResult (MS.MacawSimulatorState sym) sym (MS.MacawExt arch) (CS.RegEntry sym (MS.ArchRegStruct arch)))
evalCFG globals regs cfg = do
  archRepr <- archStructRepr
  initCtx <- initSimContext
  liftIO $ id
    . CS.executeCrucible []
    . CS.InitialState initCtx globals CS.defaultAbortHandler archRepr
    . CS.runOverrideSim archRepr
    $ CS.regValue <$> CS.callCFG cfg regs

initSimContext ::
  EquivM sym arch (CS.SimContext (MS.MacawSimulatorState sym) sym (MS.MacawExt arch))
initSimContext = withValid $ withSym $ \sym -> do
  exts <- CMR.asks envExtensions
  ha <- CMR.asks $ handles . envCtx
  return $
    CS.initSimContext
    sym
    MT.memTraceIntrinsicTypes
    ha
    IO.stderr
    (CS.FnBindings CFH.emptyHandleMap)
    exts
    MS.MacawSimulatorState

--------------------------------------------------------
-- Proving equivalence

-- | Update 'envCurrentFunc' if the given pair 
withPair :: BlockPair arch -> EquivM sym arch a -> EquivM sym arch a
withPair pPair f = case concreteBlockEntry $ pOriginal pPair of
  BlockEntryInitFunction -> CMR.local (\env -> env { envCurrentFunc = pPair}) $ f
  _ -> f

provePostcondition ::
  HasCallStack =>
  BlockPair arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
provePostcondition pPair postcondSpec = startTimer $ withPair pPair $ do
  emitPreamble pPair
  fmap unzipProof $ withSimBundle pPair $ \bundle ->
    provePostcondition' bundle postcondSpec

data BranchCase sym arch =
  BranchCase
    { -- | predicate that asserts equality on the pre-state, derived
      -- from the 'branchPreStPred' but stored here to avoid re-computing it
      branchPrePred :: W4.Pred sym
      -- | the structured pre-domain for this branch
    , branchPreDomain :: StatePred sym arch
      -- | target for the function call
    , branchBlocks :: BlockPair arch
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
  SimBundle sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePred sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
trivialBlockSlice bundle postcondSpec = withSym $ \sym -> do
  transition <- PFO.noTransition (simIn bundle) (simOutBlockEnd $ simOutO bundle)
  PFO.lazyProofEvent (simPair bundle) $ do
    preUniv <- universalDomain
    preDomain <- PFO.asLazyProof <$> PFO.statePredToPreDomain bundle preUniv
    postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
    status <- PFO.lazyProofApp $ PF.ProofStatus PF.VerificationSkipped (W4.truePred sym)
    triple <- PFO.lazyProofApp $ PF.ProofTriple (simPair bundle) preDomain postDomain status
    let prf = PF.ProofBlockSlice triple [] Nothing Nothing transition
    return (preUniv, prf)

-- | Prove that a postcondition holds for a function pair starting at
-- this address. The return result is the computed pre-domain, tupled with a lazy
-- proof result that, once evaluated, represents the proof tree that verifies
-- the given block slices are equivalent.
provePostcondition' ::
  forall sym arch.
  HasCallStack =>
  SimBundle sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePred sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
provePostcondition' bundle postcondSpec = PFO.lazyProofEvent (simPair bundle) $ withSym $ \sym -> do
  pairs <- PD.discoverPairs bundle
  -- find all possible exits and propagate the postcondition backwards from them
  funCallProofCases <- DT.forM pairs $ \(blktO, blktP) ->  do
    withAssumption (PD.matchesBlockTarget bundle blktO blktP) $
      PFO.lazyProofEvent (simPair bundle) $ do
      let
        blkO = targetCall blktO
        blkP = targetCall blktP
        pPair = PatchPair blkO blkP
      case (targetReturn blktO, targetReturn blktP) of
        (Just blkRetO, Just blkRetP) -> do
          isSyscall <- case (concreteBlockEntry blkO, concreteBlockEntry blkP) of
            (BlockEntryPostArch, BlockEntryPostArch) -> return True
            (entryO, entryP) | entryO == entryP -> return False
            _ -> throwHere $ BlockExitMismatch
          withNoFrameGuessing isSyscall $ do
            (contPre, contPrf) <- provePostcondition (PatchPair blkRetO blkRetP) postcondSpec
            (funCallPre, funCallSlicePrf) <- fmap unzipProof $ withSimBundle pPair $ \bundleCall -> do
              -- equivalence condition for when this function returns
              case isSyscall of
                -- for arch exits (i.e. syscalls) we assume that equivalence will hold on
                -- any post domain if the pre-domain is exactly equal: i.e. any syscall is
                -- treated as an uninterpreted function that reads the entire machine state
                -- this can be relaxed with more information about the specific call
                True -> trivialBlockSlice bundleCall postcondSpec
                False -> do
                  emitPreamble pPair
                  -- equivalence condition for calling this function
                  provePostcondition' bundleCall contPre

            -- equivalence condition for the function entry
            branchCase <- proveLocalPostcondition bundle funCallPre
            let
              prf = PF.ProofFunctionCall
                      { PF.prfFunctionCallPre = branchProofTriple branchCase
                      , PF.prfFunctionCallBody = funCallSlicePrf
                      , PF.prfFunctionCallContinue = Just contPrf
                      }
            return (branchCase, prf)

        (Nothing, Nothing) -> do
          (contPre, contPrf) <- provePostcondition (PatchPair blkO blkP) postcondSpec
          branchCase <- proveLocalPostcondition bundle contPre
          let
            prf = PF.ProofFunctionCall
                    { PF.prfFunctionCallPre = branchProofTriple branchCase
                    , PF.prfFunctionCallBody = contPrf
                    , PF.prfFunctionCallContinue = Nothing
                    }
          return (branchCase, prf)
        _ -> throwHere $ BlockExitMismatch

  -- if we have a "return" exit, prove that it satisfies the postcondition
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  precondReturn <- withSatAssumption goalTimeout (matchingExits bundle MS.MacawBlockEndReturn) $ do
    proveLocalPostcondition bundle postcondSpec
  let
    -- for simplicitly, we drop the condition on the return case, and assume
    -- it is taken if all other cases are false, which is checked by 'checkCasesTotal'
    returnByDefault = case precondReturn of
      Just (_, br) -> branchPreDomain br
      Nothing -> statePredFalse sym

  -- an exit that was not classified
  isUnknown <- do
    isJump <- matchingExits bundle MS.MacawBlockEndJump
    isFail <- matchingExits bundle MS.MacawBlockEndFail
    isBranch <- matchingExits bundle MS.MacawBlockEndBranch
    liftIO $ anyPred sym [isJump, isFail, isBranch]
  precondUnknown <- withSatAssumption goalTimeout (return isUnknown) $ do
    blocks <- PD.getBlocks (simPair bundle)
    emitWarning blocks BlockEndClassificationFailure
    univDom <- universalDomainSpec
    withNoFrameGuessing True $ proveLocalPostcondition bundle univDom

  let
    funCallCases = map (\(p, (br, _)) -> (p, br)) funCallProofCases
    funCallProofs = map (\(_, (br, prf)) -> (branchBlocks br, prf)) funCallProofCases
    allPreconds = catMaybes [precondReturn,precondUnknown] ++ funCallCases
  
  precond' <- F.foldrM (\(p, br) stPred -> liftIO $ muxStatePred sym p (branchPreDomain br) stPred)  returnByDefault funCallCases

  precond <- withAssumption_ (liftIO $ anyPred sym (map fst allPreconds)) $
    simplifySubPreds precond'

  -- TODO: this needs to be reorganized to make the domain results actually lazy
  preDomain <- PFO.asLazyProof <$> PFO.statePredToPreDomain bundle precond
  postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
  status <- checkCasesTotal bundle preDomain allPreconds
  blockSlice <- PFO.simBundleToSlice bundle
  triple <- PFO.lazyProofEvent_ (simPair bundle) $ return $
    PF.ProofTriple (simPair bundle) preDomain postDomain status
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
  eqRel <- CMR.asks envBaseEquiv
  (asm, postcond) <- liftIO $ bindSpec sym (simOutState $ simOutO bundle) (simOutState $ simOutP bundle) postcondSpec
  (_, postcondPred) <- liftIO $ getPostcondition sym bundle eqRel postcond

  eqInputs <- withAssumption_ (return asm) $ do
    guessEquivalenceDomain bundle postcondPred postcond

  -- TODO: avoid re-computing this
  blockSlice <- PFO.simBundleToSlice bundle
  let sliceState = PF.slBlockPostState blockSlice
       
  stackRegion <- CMR.asks envStackRegion
  eqInputsPred <- liftIO $ getPrecondition sym stackRegion bundle eqRel eqInputs

  notChecks <- liftIO $ W4.notPred sym postcondPred
  blocks <- PD.getBlocks $ simPair bundle
  preDomain <- PFO.asLazyProof <$> PFO.statePredToPreDomain bundle eqInputs
  postDomain <- PFO.asLazyProof <$> PFO.statePredToPostDomain postcondSpec
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)

  liftIO $ putStrLn "Starting inequivalence proof"
  result <- PFO.lazyProofEvent_ (simPair bundle) $
     withAssumption_ (liftIO $ allPreds sym [eqInputsPred, asm]) $ startTimer $ do
       status <- checkSatisfiableWithModel goalTimeout "check" notChecks $ \satRes -> do        
         case satRes of
           W4R.Unsat _ -> do
             emitEvent (PE.CheckedEquivalence blocks PE.Equivalent)
             return PF.VerificationSuccess
           W4R.Unknown -> do
             emitEvent (PE.CheckedEquivalence blocks PE.Inconclusive)
             return PF.Unverified
           W4R.Sat fn -> do
             preDomain' <- PF.unNonceProof <$> PFO.joinLazyProof preDomain
             postDomain' <- PF.unNonceProof <$> PFO.joinLazyProof postDomain
             liftIO $ putStrLn "Getting inequivalence result"
             
             ir <- PFG.getInequivalenceResult InvalidPostState preDomain' postDomain' blockSlice fn
             emitEvent (PE.CheckedEquivalence blocks (PE.Inequivalent ir))
             return $ PF.VerificationFail ir
       cond <- case status of
         PF.VerificationFail _ -> do
           postDomain' <- PF.unNonceProof <$> PFO.joinLazyProof postDomain
           -- no paths are known to be equivalent at this point
           noPathCond <- falsePathCond
           cond <- conditionalEquivalenceCheck bundle noPathCond
                      sliceState postDomain' notChecks
           minimalPathCondition cond postcondPred
         _ -> return $ W4.truePred sym
       return $ PF.ProofStatus status cond
           
  triple <- PFO.lazyProofEvent_ (simPair bundle) $
    return $ PF.ProofTriple (simPair bundle) preDomain postDomain result
  return $ BranchCase eqInputsPred eqInputs (simPair bundle) triple

-- | Compute an equivalence condition without strengthening the pre-domain.
-- The condition is negated, then assumed, and the equivalence check is re-attempted.
-- This process eventually terminates by either resulting in a "false" equivalence condition
-- representing the fact that no such condition could be found, or by finding a structured
-- equivalence condition which induces equality on the given slice under the given additional
-- assumption.
conditionalEquivalenceCheck ::
  SimBundle sym arch ->
  -- | path conditions that (should) induce equivalence
  PatchPairC (W4.Pred sym) ->
  -- | block slice post-state
  PF.BlockSliceState (PFI.ProofSym sym arch) ->
  -- | equivalence post-domain
  PFI.SymDomain sym arch ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (PatchPairC (W4.Pred sym))
conditionalEquivalenceCheck bundle pathCond sliceState postDomain notChecks = withSym $ \sym -> do
  liftIO $ putStrLn "Checking for conditional equivalence.."

  -- can we satisfy equivalence, assuming that none of the given path conditions are taken?  
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)

  result <- checkSatisfiableWithModel goalTimeout "check" notChecks $ \satRes -> case satRes of
      W4R.Unsat _ -> return Nothing
      W4R.Unknown -> return Nothing
      -- counter-example, compute another path condition and continue
      W4R.Sat fn -> Just <$> PFG.getUnequalPathCondition bundle sliceState postDomain fn
  case result of
    Nothing -> do
      liftIO $ putStrLn "Got result, giving up."
      return pathCond
  -- indeterminate result, failure
    Just unequalPathCond -> do
      liftIO $ putStrLn "No result, recursing."
      pathCond' <- liftIO $ zipMPatchPairC unequalPathCond pathCond (W4.orPred sym)
      liftIO $ putStrLn (show $ ppPatchPairC (PP.pretty . CC.showF) unequalPathCond)
      -- assume this path is not taken and continue
      unequalPathCond_flat <- flattenCondPair unequalPathCond
      withAssumption_ (liftIO $ W4.notPred sym unequalPathCond_flat) $
        conditionalEquivalenceCheck bundle pathCond' sliceState postDomain notChecks

falsePathCond :: EquivM sym arch (PatchPairC (W4.Pred sym))
falsePathCond = withSym $ \sym -> return (PatchPairC (W4.falsePred sym) (W4.falsePred sym))

flattenCondPair :: PatchPairC (W4.Pred sym) -> EquivM sym arch (W4.Pred sym)
flattenCondPair (PatchPairC p1 p2) = withSym $ \sym -> liftIO $ W4.andPred sym p1 p2

-- | Given a path condition representing the set of paths that are inequivalent,
-- compute a minimal positive condition for equivalence.
minimalPathCondition ::
  forall sym arch.
  -- | path condition that is assumed to imply equivalence
  PatchPairC (W4.Pred sym) ->
  -- | goal equivalence predicate
  W4.Pred sym ->
  EquivM sym arch (W4.Pred sym)
minimalPathCondition pathCond goal = withValid $ withSym $ \sym -> do
  liftIO $ putStrLn "Conditional equivalence found!"
  goalTimeout <- CMR.asks (PC.cfgGoalTimeout . envConfig)
  heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
  let
    checkCond :: W4.Pred sym -> EquivM sym arch (Maybe (W4.Pred sym, Bool))
    checkCond cond = withSatAssumption goalTimeout (liftIO $ W4.notPred sym cond) $ do
        isPredTrue' goalTimeout goal

  liftIO $ putStrLn (show $ ppPatchPairC (PP.pretty . CC.showF) pathCond)
  -- check if either path condition alone is sufficient to imply equivalence
  p <- mapM checkCond pathCond >>= \case
    PatchPairC _ (Just (condP, True)) -> return condP
    PatchPairC (Just (condO, True)) _ -> return condO
    PatchPairC (Just (condO, False)) (Just (condP, False)) -> do
      result <- withSatAssumption goalTimeout (liftIO $ W4.andPred sym condO condP) $ do
        isPredTrue' goalTimeout goal
      case result of
        Just (p, True) -> return p
        _ -> return $ W4.falsePred sym
    _ -> return $ W4.falsePred sym
  atoms <- exprSetToList @sym <$> (liftIO $ getPredAtoms sym p)
  let
    applyAtom :: W4.Pred sym -> W4.Pred sym -> EquivM sym arch (W4.Pred sym)
    applyAtom p' atom = do
      isIndep <- liftIO $ independentOf sym atom p'
      isPredTrue' heuristicTimeout isIndep >>= \case
        True -> liftIO $ rebindWithFrame sym (frameAssume atom) p' 
        False -> return p'
    
  p' <- CME.foldM applyAtom p atoms
  liftIO $ putStrLn "Minimal path condition:"
  liftIO $ putStrLn (CC.showF p')
  return p


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
  MemPred sym arch ->
  -- | filter for whether or not memory cells can possibly belong to
  -- the given domain
  (forall w. PMC.MemCell sym arch w -> EquivM sym arch (W4.Pred sym)) ->
  EquivM sym arch (MemPred sym arch)
guessMemoryDomain bundle goal (memP', goal') memPred cellFilter = withSym $ \sym -> do
  foots <- getFootprints bundle
  cells <- do
    localPred <- liftIO $ addFootPrintsToPred sym foots memPred
    mapMemPred localPred $ \cell p -> do
      isFiltered <- cellFilter cell
      pathCond <- liftIO $ W4.andPred sym p isFiltered
      simplifyPred pathCond

  -- we take the entire reads set of the block and then filter it according
  -- to the polarity of the postcondition predicate
  result <- mapMemPredPar cells $ \cell p -> maybeEqualAt bundle cell p >>= \case
    True -> ifConfig (not . PC.cfgComputeEquivalenceFrames) (Par.present $ return polarity) $ do
      let repr = MM.BVMemRepr (PMC.cellWidth cell) (PMC.cellEndian cell)
      p' <- bindMemory memP memP' p
      -- clobber the "patched" memory at exactly this cell
      CLM.LLVMPointer _ freshP <- liftIO $ freshPtrBytes sym (PMC.cellWidth cell)
      cell' <- mapExpr' (bindMemory memP memP') cell

      memP'' <- liftIO $ MT.writeMemArr sym memP (PMC.cellPtr cell') repr freshP
      eqMemP <- liftIO $ W4.isEq sym (MT.memArr memP') (MT.memArr memP'')

      -- see if we can prove that the goal is independent of this clobbering
      asm <- liftIO $ allPreds sym [p, p', eqMemP, goal]
      check <- liftIO $ W4.impliesPred sym asm goal'
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      result <- isPredTruePar' heuristicTimeout check
      Par.forFuture result $ \case
        True -> liftIO $ W4.baseTypeIte sym polarity (W4.falsePred sym) p
        False -> liftIO $ W4.baseTypeIte sym polarity p (W4.falsePred sym)
    False -> Par.present $ liftIO $ W4.notPred sym polarity
  Par.joinFuture (result :: Par.Future (MemPred sym arch))
  where
    polarity = memPredPolarity memPred
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

mapExpr' ::
  PEM.ExprMappable sym f =>
  (forall tp. W4.SymExpr sym tp -> EquivM sym arch (W4.SymExpr sym tp)) ->
  f ->
  EquivM sym arch f
mapExpr' f e = withSym $ \sym ->
  IO.withRunInIO $ \runInIO -> PEM.mapExpr sym (\a -> runInIO (f a)) e

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
  SimBundle sym arch ->
  W4.Pred sym ->
  StatePred sym arch ->
  EquivM sym arch (StatePred sym arch)
guessEquivalenceDomain bundle goal postcond = startTimer $ withSym $ \sym -> do
  ExprFilter isBoundInGoal <- getIsBoundFilter' goal
  eqRel <- CMR.asks envBaseEquiv
  result <- zipRegStatesPar (simRegs inStO) (simRegs inStP) $ \r vO vP -> do
      isInO <- liftFilterMacaw isBoundInGoal vO
      isInP <- liftFilterMacaw isBoundInGoal vP
      let
        include = Par.present $ return $ Just (Some r, W4.truePred sym)
        exclude = Par.present $ return Nothing
      case registerCase (PSR.macawRegRepr vO) r of
        -- we have concrete values for the pre-IP and the TOC (if arch-defined), so we don't need
        -- to include them in the pre-domain
        RegIP -> exclude
        RegTOC -> exclude
        -- this requires some more careful consideration. We don't want to include
        -- the stack pointer in computed domains, because this unreasonably
        -- restricts preceding blocks from having different numbers of stack allocations.
        -- However our equivalence relation is not strong enough to handle mismatches in
        -- values written to memory that happen to be stack addresses, if those
        -- addresses were computed with different stack bases.
        RegSP -> ifConfig PC.cfgComputeEquivalenceFrames exclude include
        _ | isInO || isInP ->
          ifConfig (not . PC.cfgComputeEquivalenceFrames) include $ do
            (isFreshValid, freshO) <- freshRegEntry (pPatched $ simPair bundle) r vO

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

  ExprMapper doEquate <- equateRegisters regsDom bundle
   
  -- rewrite the state elements to explicitly equate registers we have assumed equivalent
  bundle_regsEq <- liftIO $ PEM.mapExpr sym doEquate bundle
  goal_regsEq <- liftIO $ doEquate goal
  postcond_regsEq <- liftIO $ PEM.mapExpr sym doEquate postcond
  
  memP' <- liftIO $ MT.initMemTrace sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  goal' <- bindMemory memP memP' goal_regsEq

  stackDom <- guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (predStack postcond_regsEq) isStackCell
  let stackEq = liftIO $ memPredPre sym (memEqAtRegion sym stackRegion) inO inP (eqRelStack eqRel) stackDom
  memDom <- withAssumption_ stackEq $ do
    guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (predMem postcond_regsEq) isNotStackCell

  blocks <- PD.getBlocks $ simPair bundle
  
  emitEvent (PE.ComputedPrecondition blocks)
  return $ StatePred
    { predRegs = regsDom
    , predStack = stackDom
    , predMem = memDom
    }
  where
    memP = simInMem $ simInP bundle
    inO = simInO bundle
    inP = simInP bundle
    inStO = simInState $ simInO bundle
    inStP = simInState $ simInP bundle

freshRegEntry ::
  KnownBinary bin =>
  ConcreteBlock arch bin ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (W4.Pred sym, PSR.MacawRegEntry sym tp)
freshRegEntry initBlk r entry = withSym $ \sym -> do
  fresh <- case PSR.macawRegRepr entry of
    CLM.LLVMPointerRepr w -> liftIO $ do
      ptr <- freshPtr sym w
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) ptr
    CT.BoolRepr -> liftIO $ do
      b <- W4.freshConstant sym (WS.safeSymbol "freshBoolRegister") WT.BaseBoolRepr
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) b
    CT.StructRepr Ctx.Empty -> return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) Ctx.Empty
    repr -> throwHere $ UnsupportedRegisterType $ Some repr
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
    repr -> throwHere $ UnsupportedRegisterType (Some repr)

newtype ExprMapper sym = ExprMapper (forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp'))

equateRegisters ::
  M.Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  SimBundle sym arch ->
  EquivM sym arch (ExprMapper sym)
equateRegisters regRel bundle = withValid $ withSym $ \sym -> do
  binds <- fmap (mconcat) $ zipRegStates (simRegs inStO) (simRegs inStP) $ \r vO vP -> case registerCase (PSR.macawRegRepr vO) r of
    RegIP -> return mempty
    _ -> case M.lookup (Some r) regRel of
      Just cond | Just True <- W4.asConstantPred cond -> liftIO $ macawRegBinding sym vO vP
      _ -> return mempty
  cache <- W4B.newIdxCache
  return $ ExprMapper $ rebindWithFrame' sym cache binds
  where
    inStO = simInState $ simInO bundle
    inStP = simInState $ simInP bundle


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
  BlockPair arch ->
  EquivM sym arch (MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)
functionSegOffs pPair = do
  PatchPair (PE.Blocks _ (pblkO:_)) (PE.Blocks _ (pblkP:_)) <- PD.getBlocks pPair
  return $ (MD.pblockAddr pblkO, MD.pblockAddr pblkP)

getCurrentTOCs :: PA.HasTOCReg arch => EquivM sym arch (W.W (MM.ArchAddrWidth arch), W.W (MM.ArchAddrWidth arch))
getCurrentTOCs = do
  (tocO, tocP) <- CMR.asks envTocs
  curFuncs <- CMR.asks envCurrentFunc
  (addrO, addrP) <- functionSegOffs curFuncs
  wO <- case TOC.lookupTOC tocO addrO of
    Just w -> return w
    Nothing -> throwHere $ MissingTOCEntry addrO
  wP <- case TOC.lookupTOC tocP addrP of
    Just w -> return w
    Nothing -> throwHere $ MissingTOCEntry addrP
  return $ (wO, wP)

--------------------------------------------------------
-- Initial state validity

validRegister ::
  forall bin sym arch tp.
  KnownBinary bin =>
  -- | if this register is an initial state, the corresponding
  -- starting block
  Maybe (ConcreteBlock arch bin) ->
  PSR.MacawRegEntry sym tp ->
  MM.ArchReg arch tp ->
  EquivM sym arch (AssumptionFrame sym)
validRegister mblockStart entry r = withSym $ \sym ->
  case registerCase (PSR.macawRegRepr entry) r of
    RegIP -> case mblockStart of
      Just blockStart -> do
        ptrO <- PD.concreteToLLVM blockStart
        liftIO $ macawRegBinding sym entry (PSR.ptrToEntry ptrO)
      Nothing -> return $ mempty
    RegSP -> do
      stackRegion <- CMR.asks envStackRegion
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      iRegion <- liftIO $ W4.natToInteger sym region
      iStackRegion <- liftIO $ W4.natToInteger sym stackRegion
      return $ exprBinding iRegion iStackRegion
    RegBV -> liftIO $ do
      let
        CLM.LLVMPointer region _ = PSR.macawRegValue entry
      zero <- W4.intLit sym 0
      iRegion <- W4.natToInteger sym region
      return $ exprBinding iRegion zero
    RegTOC -> do
      globalRegion <- CMR.asks envGlobalRegion
      (tocO, tocP) <- getCurrentTOCs
      tocBV <- case W4.knownRepr :: WhichBinaryRepr bin of
        OriginalRepr -> wLit tocO
        PatchedRepr -> wLit tocP
      let targetToc = CLM.LLVMPointer globalRegion tocBV
      liftIO $ macawRegBinding sym entry (PSR.ptrToEntry targetToc)
    _ -> return $ mempty


validInitState ::
  Maybe (BlockPair arch) ->
  SimState sym arch Original ->
  SimState sym arch Patched ->
  EquivM sym arch (AssumptionFrame sym)
validInitState mpPair stO stP = do
  fmap mconcat $ zipRegStates (simRegs stO) (simRegs stP) $ \r vO vP -> do
    validO <- validRegister (fmap pOriginal mpPair) vO r
    validP <- validRegister (fmap pPatched mpPair) vP r
    return $ validO <> validP

-- | Reads from immutable data have known results.
-- We collect all the reads that occurred during the trace, and then
-- assert that those values are necessarily equivalent to the concrete
-- value from the binary
validConcreteReads ::
  forall bin sym arch.
  KnownBinary bin =>
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
    return $ StatePred
      {
        predRegs = regDomain
      , predStack = memPredFalse sym
      , predMem = memPredTrue sym
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
  BlockPair arch ->
  EquivM sym arch (PF.EquivTriple sym arch)
topLevelTriple pPair = withPair pPair $ withFreshVars $ \stO stP -> withSym $ \sym -> do
  regDomain <- allRegistersDomain
  postcond <- topLevelPostDomain
  let
    precond = StatePred
      { predRegs = regDomain
      , predStack = memPredTrue sym
      , predMem = memPredTrue sym
      }
  let triple = PF.EquivTripleBody pPair precond postcond
  asm_frame <- validInitState (Just pPair) stO stP
  asm <- liftIO $ getAssumedPred sym asm_frame
  return (asm, triple)

-- | Domain that includes entire state, except IP and SP registers
universalDomain ::
  forall sym arch.
  EquivM sym arch (StatePred sym arch)
universalDomain =  withSym $ \sym -> do
  regDomain <- allRegistersDomain
  let regDomain' =
        M.delete (Some (MM.sp_reg @(MM.ArchReg arch))) $
        M.delete (Some (MM.ip_reg @(MM.ArchReg arch))) regDomain
  return $ StatePred
    {
      predRegs = regDomain'
    , predStack = memPredTrue sym
    , predMem = memPredTrue sym
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
  PFO.forkProofEvent (simPair bundle) $ 
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
       
        ir <- PFG.getInequivalenceResult InvalidCallPair preDomain' noDomain blockSlice fn
        emit $ PE.BranchesIncomplete ir
        return $ PF.VerificationFail ir
      W4R.Unsat _ -> do
        emit PE.BranchesComplete
        return PF.VerificationSuccess
      W4R.Unknown -> do
        emit PE.InconclusiveBranches
        return PF.Unverified
    return $ PF.ProofStatus status (W4.truePred sym)
  where
    -- | a branch case is assuming the pre-domain predicate, that the branch condition holds
    getCase :: (W4.Pred sym, BranchCase sym arch) -> EquivM sym arch (W4.Pred sym)
    getCase (cond, br) = withSym $ \sym ->
      liftIO $ W4.impliesPred sym (branchPrePred br) cond

-- | Prefer existing entries
doAddAddr ::
  ConcreteAddress arch ->
  Maybe (ConcreteAddress arch) ->
  Maybe (ConcreteAddress arch)
doAddAddr _ (Just addr) = Just addr
doAddAddr addr Nothing = Just addr

buildBlockMap ::
  [BlockPair arch] ->
  BlockMapping arch ->
  BlockMapping arch
buildBlockMap pairs bm = foldr go bm pairs
  where
    go :: BlockPair arch -> BlockMapping arch -> BlockMapping arch
    go (PatchPair orig patched) (BlockMapping m) =
      BlockMapping $ M.alter (doAddAddr (concreteAddress patched)) (concreteAddress orig) m
