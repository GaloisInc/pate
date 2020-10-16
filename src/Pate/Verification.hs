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

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  , checkRenEquivalence
  , mkIPEquivalence
  ) where

import           Prelude hiding ( fail )

import           Data.Typeable
import           Data.Bits
import           Control.Monad.Trans.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Control.Applicative
import           Control.Lens hiding ( op, pre )
import           Control.Monad.Except
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.ST

import qualified Data.BitVector.Sized as BVS
import           Data.Foldable
import           Data.Functor.Compose
import qualified Data.IntervalMap as IM
import           Data.List
import           Data.Maybe (catMaybes)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.String
import qualified Data.Time as TM
import           Data.Type.Equality (testEquality)
import           GHC.TypeLits
import qualified Lumberjack as LJ
import           System.IO

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MD

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MM


import qualified Data.Parameterized.Context.Unsafe as Ctx
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.Map as MapF


import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.ProblemFeatures as W4PF
import qualified What4.ProgramLoc as W4L
import qualified What4.Protocol.Online as W4O
import qualified What4.SatResult as W4R

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import           Pate.Types
import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT

verifyPairs ::
  forall arch.
  ValidArch arch =>
  LJ.LogAction IO (PE.Event arch) ->
  PB.LoadedELF arch ->
  PB.LoadedELF arch ->
  BlockMapping arch ->
  DiscoveryConfig ->
  [PatchPair arch] ->
  ExceptT (EquivalenceError arch) IO Bool
verifyPairs logAction elf elf' blockMap dcfg pPairs = do
  Some gen <- liftIO . stToIO $ N.newSTNonceGenerator
  vals <- case MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) of
    Nothing -> throwError $ equivalenceError UnsupportedArchitecture
    Just vs -> pure vs
  ha <- liftIO CFH.newHandleAllocator
  (mainO, pfmO)  <- runDiscovery elf
  (mainP, pfmP) <- runDiscovery elf'

  Some gen' <- liftIO N.newIONonceGenerator
  let pfeats = W4PF.useBitvectors .|. W4PF.useSymbolicArrays
  CBO.withYicesOnlineBackend W4B.FloatRealRepr gen' CBO.NoUnsatFeatures pfeats $ \sym -> do
    eval <- lift (MS.withArchEval vals sym pure)
    model <- lift (MT.mkMemTraceVar @arch ha)
    evar <- lift (MT.mkExitClassVar @arch ha)
    initMem <- liftIO $ MT.initMemTrace sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
    initEClass <- liftIO $ MT.initExitClass sym
    proc <- liftIO $ CBO.withSolverProcess sym return

    stackRegion <- liftIO $ W4.natLit sym 0
    let
      exts = MT.macawTraceExtensions eval model evar (trivialGlobalMap @_ @arch)

      oCtx = BinaryContext
        { binary = PB.loadedBinary elf
        , parsedFunctionMap = pfmO
        , binEntry = mainO
        }
      rCtx = BinaryContext
        { binary = PB.loadedBinary elf'
        , parsedFunctionMap = pfmP
        , binEntry = mainP
        }
      ctxt = EquivalenceContext
        { nonces = gen
        , handles = ha
        , exprBuilder = sym
        , originalCtx = oCtx
        , rewrittenCtx = rCtx
        
        }
      globs =
        CGS.insertGlobal evar initEClass
        $ CGS.insertGlobal model initMem CGS.emptyGlobals
      env = EquivEnv
        { envSym = sym
        , envProc = proc
        , envWhichBinary = Nothing
        , envCtx = ctxt
        , envArchVals = vals
        , envExtensions = exts
        , envGlobalMap = globs
        , envStackRegion = stackRegion
        , envMemTraceVar = model
        , envExitClassVar = evar
        , envBlockMapping = buildBlockMap pPairs blockMap
        , envLogger = logAction
        , envDiscoveryCfg = dcfg
        }

    liftIO $ do
      putStr "\n"
      stats <- runVerificationLoop env pPairs
      liftIO . putStr $ ppEquivalenceStatistics stats
      return $ equivSuccess stats

-- | Verify equivalence of the given pairs, as well as any
-- resulting pairs that emerge
runVerificationLoop ::
  EquivEnv sym arch ->
  [PatchPair arch] ->
  IO EquivalenceStatistics
runVerificationLoop env pPairs = do
  let
    st = EquivState
          { stOpenPairs = S.fromList pPairs
          , stVerifiedPairs = S.empty
          , stFailedPairs = S.empty
          }
  result <- runExceptT $ runEquivM env st doVerify
  case result of
    Left err -> withValidEnv env $ error (show err)
    Right r -> return r

  where
    doVerify :: EquivM sym arch EquivalenceStatistics
    doVerify = do
      whenM (asks $ cfgPairMain . envDiscoveryCfg) $ do
        mainO <- asks $ binEntry . originalCtx . envCtx
        mainP <- asks $ binEntry . rewrittenCtx . envCtx
        blkO <- mkConcreteBlock BlockEntryInitFunction <$> segOffToAddr mainO
        blkP <- mkConcreteBlock BlockEntryInitFunction <$> segOffToAddr mainP
        addOpenPairs $ S.singleton (PatchPair blkO blkP)
      go mempty

    go :: EquivalenceStatistics -> EquivM sym arch EquivalenceStatistics
    go stats = gets (S.toList . S.take 1 . stOpenPairs) >>= \case
      [pPair] -> do
        printPreamble pPair
        result <- manifestError $ checkRenEquivalence pPair
        case result of
          Left _ -> markPairFailed pPair
          Right _ -> return ()
        printResult result
        normResult <- return $ case result of
          Left err | InequivalentError _ <- errEquivError err -> EquivalenceStatistics 1 0 0
          Left _ -> EquivalenceStatistics 1 0 1
          Right _ -> EquivalenceStatistics 1 1 0
        go (stats <> normResult)

      _ -> return stats

whenM :: Monad m => m Bool -> m () -> m ()
whenM p f = p >>= \case
  True -> f
  False -> return ()

printPreamble :: PatchPair arch -> EquivM sym arch ()
printPreamble pPair = liftIO $ putStr $ ""
    ++ "Checking equivalence of "
    ++ ppBlock (pOrig pPair)
    ++ " and "
    ++ ppBlock (pPatched pPair)
    ++ " (" ++ ppBlockEntry (concreteBlockEntry (pOrig pPair)) ++ ") "
    ++ ": "

ppBlockEntry :: BlockEntryKind arch -> String
ppBlockEntry be = case be of
  BlockEntryInitFunction -> "function entry point"
  BlockEntryPostFunction -> "intermediate function point"
  BlockEntryPostArch -> "intermediate function point (after syscall)"
  BlockEntryJump -> "unknown program point"

printResult :: Either (EquivalenceError arch) () -> EquivM sym arch ()
printResult (Left err) = liftIO $ putStr . ppEquivalenceError $ err
printResult (Right ()) = liftIO $ putStr "✓\n"


checkRenEquivalence ::
  forall sym arch.
  PatchPair arch ->
  EquivM sym arch ()
checkRenEquivalence pPair@(PatchPair { pOrig = rBlock, pPatched =  rBlock' }) = do
  initRegStateO <- MM.mkRegStateM (unconstrainedRegister rBlock)
  initRegStateP <- MM.mkRegStateM (initialRegisterState rBlock' initRegStateO)

  oCtx <- asks $ originalCtx . envCtx
  rCtx <- asks $ rewrittenCtx . envCtx

  CC.Some (Compose opbs) <- lookupBlocks (parsedFunctionMap oCtx) rBlock
  let oBlocks = PE.Blocks (concreteAddress rBlock) opbs
  CC.Some (Compose ppbs) <- lookupBlocks (parsedFunctionMap rCtx) rBlock'
  let pBlocks = PE.Blocks (concreteAddress rBlock') ppbs
   
  simResult <- withBinary Original $ simulate oCtx rBlock initRegStateO
  simResult' <- withBinary Rewritten $ simulate rCtx rBlock' initRegStateP
  let
    regs = resultRegs simResult
    regs' = resultRegs simResult'

  regEq@(RegEquivCheck eqPred) <- mkRegEquivCheck simResult simResult'
  registersEquivalent <- withSymIO $ \sym -> MT.exitCases sym (resultExit simResult) $ \ecase -> do
    preds <- MM.traverseRegsWith (\r v -> Const <$> eqPred ecase r v (regs' ^. MM.boundValue r)) regs
    TF.foldrMF (\(Const p1) p2 -> W4.andPred sym p1 p2) (W4.truePred sym) preds

  withSymIO $ \sym -> CB.resetAssumptionState sym

  assertPrecondition simResult simResult'
  matchTraces pPair registersEquivalent regEq (oBlocks, simResult) (pBlocks, simResult')



isIPAligned ::
  forall sym arch.
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (W4.Pred sym)
isIPAligned (CLM.LLVMPointer _blk offset)
  | bits <- MM.memWidthNatRepr @(MM.ArchAddrWidth arch) = withSymIO $ \sym -> do
    lowbits <- W4.bvSelect sym (W4.knownNat :: W4.NatRepr 0) bits offset
    W4.bvEq sym lowbits =<< W4.bvLit sym bits (BVS.zero bits)

-- | Assert additional conditions relating the initial program states
assertPrecondition :: forall sym arch.
  SimulationResult sym arch ->
  SimulationResult sym arch ->
  EquivM sym arch ()
assertPrecondition resultO resultP = do
  ipEq <- mkIPEquivalence
  MM.traverseRegsWith_ (\r preO -> do
    let preP = (resultPreRegs resultP) ^. MM.boundValue r
    case funCallIP r of
      Just Refl -> do
        alignedO <- isIPAligned (macawRegValue preO)
        alignedP <- isIPAligned (macawRegValue preP)
        withSymIO $ \sym -> do
          here <- W4.getCurrentProgramLoc sym
          eqIPs <- ipEq (macawRegValue preO) (macawRegValue preP)

          CB.addAssumption sym (CB.LabeledPred alignedO (CB.AssumptionReason here "IPs Aligned - Original"))
          CB.addAssumption sym (CB.LabeledPred alignedP (CB.AssumptionReason here "IPs Aligned - Patched"))
          CB.addAssumption sym (CB.LabeledPred eqIPs (CB.AssumptionReason here "IPs Equivalent"))
      _ -> return ()
    ) (resultPreRegs resultO)

throwInequivalenceResult ::
  forall sym arch a.
  InequivalenceReason ->
  RegEquivCheck sym arch ->
  SimulationResult sym arch ->
  SimulationResult sym arch ->
  SymGroundEvalFn sym ->
  (InequivalenceResult arch -> EquivM sym arch ()) ->
  EquivM sym arch a
throwInequivalenceResult defaultReason regEq simResult simResult' fn@(SymGroundEvalFn fn') emit = do
  let
    RegEquivCheck eqPred = regEq
    regsO = resultRegs simResult
    regsP = resultRegs simResult'

  ecaseO <- liftIO $ MT.groundExitCase fn' (resultExit simResult)
  ecaseP <- liftIO $ MT.groundExitCase fn' (resultExit simResult')
  memdiff <- groundTraceDiff fn (resultMem simResult) (resultMem simResult')
  regdiff <- MM.traverseRegsWith
    (\r preO -> do
        let
          preP = (resultPreRegs simResult') ^. MM.boundValue r
          postO = regsO ^. MM.boundValue r
          postP = regsP ^. MM.boundValue r
        equivE <- liftIO $ eqPred ecaseP r postO postP
        mkRegisterDiff fn r preO preP postO postP equivE
    )
    (resultPreRegs simResult)
  let reason =
        if isMemoryDifferent memdiff then InequivalentMemory
        else if areRegistersDifferent regdiff then InequivalentRegisters
        else defaultReason
  let ir = InequivalentResults memdiff (ecaseO, ecaseP) regdiff reason
  emit ir
  throwHere $ InequivalentError ir

isMemoryDifferent :: forall arch. MemTraceDiff arch -> Bool
isMemoryDifferent diffs = any go diffs
  where
    go :: MemOpDiff arch -> Bool
    go diff = mOpOriginal diff /= mOpRewritten diff

areRegistersDifferent :: forall arch. MM.RegState (MM.ArchReg arch) (RegisterDiff arch) -> Bool
areRegistersDifferent regs = case MM.traverseRegsWith_ go regs of
  Just () -> False
  Nothing -> True
  where
    go :: forall tp. MM.ArchReg arch tp -> RegisterDiff arch tp -> Maybe ()
    go _ diff = if rPostEquivalent diff then Just () else Nothing

matchTraces :: forall sym arch.
  PatchPair arch ->
  W4.Pred sym ->
  RegEquivCheck sym arch ->
  (PE.Blocks arch, SimulationResult sym arch) ->
  (PE.Blocks arch, SimulationResult sym arch) ->
  EquivM sym arch ()
matchTraces pPair prevChecks regEq (oBlocks, simResult) (pBlocks, simResult') = do
  eqWrites <- withSymIO $ \sym -> do
    let
      eqRel :: forall w. CLM.LLVMPtr sym w -> CLM.LLVMPtr sym w -> IO (W4.Pred sym)
      eqRel = llvmPtrEq sym
    MT.equivWrites sym eqRel (resultMem simResult) (resultMem simResult')

  validExits <- withSymIO $ \sym -> do
    let
      MT.ExitClassifyImpl exitO = resultExit simResult
      MT.ExitClassifyImpl exitP = resultExit simResult'
    MT.exitCases sym (resultExit simResult) $ \case
      MT.ExitUnknown -> return $ W4.falsePred sym
      _ -> W4.isEq sym exitO exitP

  checks <- withSymIO $ \sym -> do
    eqState <- W4.andPred sym eqWrites validExits
    W4.andPred sym eqState prevChecks
  notChecks <- withSymIO $ \sym -> W4.notPred sym checks

  startedAt <- liftIO TM.getCurrentTime
  checkSatisfiableWithModel satResultDescription notChecks $ \satRes -> do
    finishedBy <- liftIO TM.getCurrentTime
    let duration = TM.diffUTCTime finishedBy startedAt
    case satRes of
      W4R.Unsat _ -> do
        emitEvent (PE.CheckedEquivalence oBlocks pBlocks PE.Equivalent duration)
        return ()
      W4R.Unknown -> do
        emitEvent (PE.CheckedEquivalence oBlocks pBlocks PE.Inconclusive duration)
        throwHere InconclusiveSAT
      W4R.Sat fn@(SymGroundEvalFn fn') -> do
        let emit ir = emitEvent (PE.CheckedEquivalence oBlocks pBlocks (PE.Inequivalent ir) duration)
        throwInequivalenceResult InvalidPostState regEq simResult simResult' fn emit

  -- compute possible call targets and add them to the set of open pairs
  withSymIO $ \sym -> do
    here <- W4.getCurrentProgramLoc sym
    CB.addAssumption sym (CB.LabeledPred checks (CB.AssumptionReason here "Passing equivalence checks."))

  pfmO <- asks $ parsedFunctionMap . originalCtx . envCtx
  blksO <- getSubBlocks pfmO (pOrig pPair)

  pfmP <- asks $ parsedFunctionMap . rewrittenCtx . envCtx
  blksP <- getSubBlocks pfmP (pPatched pPair)

  let
    allCalls = [ (blkO, blkP)
               | blkO <- blksO
               , blkP <- blksP
               , compatibleTargets blkO blkP]

  validTargets <- fmap catMaybes $
    forM allCalls $ \(blktO, blktP) -> do
      ptrsEq <- withSymIO $ \sym -> matchesBlockTarget sym (targetCall blktO) (targetCall blktP)
      checkSatisfiableWithModel "check" ptrsEq $ \case
          W4R.Sat _ -> return $ Just $ (blktO, blktP)
          W4R.Unsat _ -> return Nothing
          W4R.Unknown -> throwHere InconclusiveSAT

  addOpenPairs $ S.fromList $ concat $ map allTargets validTargets

  notValidCall <- withSymIO $ \sym -> do
    let addTarget e p (blktO, blktP) = do
          case validExit e (concreteBlockEntry (targetCall blktO)) of
            True -> do
              matches <- matchesBlockTarget sym (targetCall blktO) (targetCall blktP)
              W4.orPred sym matches p
            False -> return p
    validCall <- MT.exitCases sym (resultExit simResult) $ \ecase -> do
      case ecase of
        -- TODO: we need to assert that the stored return address in the stack
        -- initially satisfies the IP equivalence relation in order to prove
        -- that this return satisfies it
        MT.ExitReturn -> return $ W4.truePred sym
        _ -> foldM (addTarget ecase) (W4.falsePred sym) validTargets

    W4.notPred sym validCall

  -- FIXME: Stream results out from this SAT check
  checkSatisfiableWithModel "check" notValidCall $ \case
    W4R.Unsat _ -> return ()
    W4R.Sat fn -> throwInequivalenceResult InvalidCallPair regEq simResult simResult' fn (\_ -> return ())
    W4R.Unknown -> throwHere InconclusiveSAT

  markPairVerified pPair
  where
    regsO = resultRegs simResult
    regsP = resultRegs simResult'
    ipO = regsO ^. MM.curIP
    ipP = regsP ^. MM.curIP

    rBlock = resultBlock simResult
    rBlock' = resultBlock simResult'
    satResultDescription = ""
      ++ "equivalence of the blocks at " ++ show (concreteAddress rBlock) ++ " in the original binary "
      ++ "and at " ++ show (concreteAddress rBlock') ++ " in the rewritten binary"

    matchesBlockTarget ::
      sym ->
      ConcreteBlock arch ->
      ConcreteBlock arch ->
      IO (W4.Pred sym)
    matchesBlockTarget sym blkO blkP = do
      ptrO <- concreteToLLVM sym (concreteAddress blkO)
      ptrP <- concreteToLLVM sym (concreteAddress blkP)

      eqO <- llvmPtrEq sym ptrO (macawRegValue ipO)
      eqP <- llvmPtrEq sym ptrP (macawRegValue ipP)
      W4.andPred sym eqO eqP


validExit :: MT.ExitCase -> BlockEntryKind arch -> Bool
validExit ecase blkK = case (ecase, blkK) of
  (MT.ExitCall, BlockEntryInitFunction) -> True
  (MT.ExitArch, BlockEntryPostArch) -> True
  _ -> False

allTargets ::
  (BlockTarget arch, BlockTarget arch) -> [PatchPair arch]
allTargets (BlockTarget blkO mrblkO, BlockTarget blkP mrblkP) =
  [PatchPair blkO blkP] ++
    case (mrblkO, mrblkP) of
      (Just rblkO, Just rblkP) -> [PatchPair rblkO rblkP]
      _ -> []

-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  BlockTarget arch ->
  BlockTarget arch ->
  Bool
compatibleTargets blkt1 blkt2 =
  concreteBlockEntry (targetCall blkt1) == concreteBlockEntry (targetCall blkt2) &&
  case (targetReturn blkt1, targetReturn blkt2) of
    (Just blk1, Just blk2) -> concreteBlockEntry blk1 == concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

-- | Mark a PatchPair as having unsuccessfully attempted verification
markPairFailed ::
  PatchPair arch ->
  EquivM sym arch ()
markPairFailed pPair = modify $
  \(EquivState open closed failed) -> EquivState (S.delete pPair open) closed (S.insert pPair failed)


-- | Mark a PatchPair as having completed verification
markPairVerified ::
  PatchPair arch ->
  EquivM sym arch ()
markPairVerified pPair = modify $
  \(EquivState open closed failed) -> EquivState (S.delete pPair open) (S.insert pPair closed) failed


addOpenPairs ::
  Set (PatchPair arch) ->
  EquivM sym arch ()
addOpenPairs pPairs = modify $ \(EquivState open closed failed) ->
    let
      newopen = (S.union pPairs open) S.\\ closed S.\\ failed
    in
      EquivState newopen closed failed

evalCFG ::
  CS.RegMap sym tp ->
  CC.CFG (MS.MacawExt arch) blocks tp (MS.ArchRegStruct arch) ->
  EquivM sym arch (CS.ExecResult (MS.MacawSimulatorState sym) sym (MS.MacawExt arch) (CS.RegEntry sym (MS.ArchRegStruct arch)))
evalCFG regs cfg = do
  archRepr <- archStructRepr
  globals <- asks envGlobalMap
  initCtx <- initSimContext
  liftIO $ id
    . CS.executeCrucible []
    . CS.InitialState initCtx globals CS.defaultAbortHandler archRepr
    . CS.runOverrideSim archRepr
    $ CS.regValue <$> CS.callCFG cfg regs

initSimContext ::
  EquivM sym arch (CS.SimContext (MS.MacawSimulatorState sym) sym (MS.MacawExt arch))
initSimContext = withValid $ withSym $ \sym -> do
  exts <- asks envExtensions
  ha <- asks $ handles . envCtx
  return $
    CS.initSimContext
    sym
    MT.memTraceIntrinsicTypes
    ha
    stderr
    CFH.emptyHandleMap
    exts
    MS.MacawSimulatorState

data SimulationResult sym arch where
  SimulationResult ::
    { resultPreRegs :: MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
    , resultRegs :: MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
    , resultMem :: MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    , resultExit :: MT.ExitClassifyImpl sym
    , resultBlock :: ConcreteBlock arch
    } -> SimulationResult sym arch

simulate ::
  BinaryContext sym arch ->
  ConcreteBlock arch ->
  MM.RegState (MM.ArchReg arch) (MacawRegEntry sym) ->
  EquivM sym arch (SimulationResult sym arch)
simulate binCtx rb preRegs = errorFrame $ do
  -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
  CC.SomeCFG cfg <- do
    CC.Some (Compose pbs_) <- lookupBlocks (parsedFunctionMap binCtx) rb
    let pb:pbs = sortOn MD.pblockAddr pbs_
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
        (terminal_, nonTerminal) = partition isTerminalBlock pbs
        terminal = [pb | isTerminalBlock pb] ++ terminal_
        killEdges = concatMap (externalTransitions internalAddrs) (pb:pbs)
    fns <- archFuns
    ha <- asks $ handles . envCtx
    liftIO $ MS.mkBlockSliceCFG fns ha (W4L.OtherPos . fromString . show) pb nonTerminal terminal killEdges
  preRegsAsn <- regStateToAsn preRegs
  archRepr <- archStructRepr
  let regs = CS.assignReg archRepr preRegsAsn CS.emptyRegMap
  cres <- evalCFG regs cfg
  (postRegs, memTrace, jumpClass) <- getGPValueAndTrace cres
  return $ SimulationResult preRegs postRegs memTrace jumpClass rb

execGroundFn ::
  SymGroundEvalFn sym  -> 
  W4.SymExpr sym tp -> 
  EquivM sym arch (W4G.GroundValue tp)  
execGroundFn gfn e = liftIO (execGroundFnIO gfn e)

archStructRepr :: forall sym arch. EquivM sym arch (CC.TypeRepr (MS.ArchRegStruct arch))
archStructRepr = do
  archFs <- archFuns
  return $ CC.StructRepr $ MS.crucArchRegTypes archFs

memOpCondition :: MT.MemOpCondition sym -> EquivM sym arch (W4.Pred sym)
memOpCondition = \case
  MT.Unconditional -> withSymIO $ \sym -> return $ W4.truePred sym
  MT.Conditional p -> return p

checkSatisfiableWithModel ::
  String ->
  W4.Pred sym ->
  (W4R.SatResult (SymGroundEvalFn sym) () -> EquivM sym arch a) ->
  EquivM sym arch a
checkSatisfiableWithModel desc p k = withProc $ \proc -> do
  let mkResult r = W4R.traverseSatResult (pure . SymGroundEvalFn) pure r
  runInIO1 (mkResult >=> k) $ W4O.checkSatisfiableWithModel proc desc p

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
      MD.ParsedLookupTable _ _ tgts -> toList tgts
      MD.ParsedReturn{} -> []
      MD.ParsedArchTermStmt{} -> [] -- TODO: think harder about this
      MD.ParsedTranslateError{} -> []
      MD.ClassifyFailure{} -> []
  , tgt `S.notMember` internalAddrs
  ]

-- | True if this register can be assumed equivalent at the start of
-- a block
-- FIXME: Stack pointers need not be equal in general
preStableReg ::
  forall arch tp.
  ValidArch arch =>
  ConcreteBlock arch ->
  MM.ArchReg arch tp ->
  Bool
preStableReg _ reg | Just _ <- testEquality reg (MM.sp_reg @(MM.ArchReg arch)) = True
preStableReg blk reg = case concreteBlockEntry blk of
  BlockEntryInitFunction -> funCallArg reg || funCallStable reg
  BlockEntryPostFunction -> funCallRet reg || funCallStable reg
  -- FIXME: not entirely true, needs proper dependency analysis
  BlockEntryPostArch -> funCallStable reg
  _ -> False


mkRegisterDiff ::
  SymGroundEvalFn sym ->
  MM.ArchReg arch tp ->
  MacawRegEntry sym tp ->
  -- ^ original prestate
  MacawRegEntry sym tp ->
  -- ^ patched prestate
  MacawRegEntry sym tp ->
  -- ^ original post state
  MacawRegEntry sym tp ->
  -- ^ patched post state
  W4.Pred sym ->
  EquivM sym arch (RegisterDiff arch tp)
mkRegisterDiff fn reg preO preP postO postP equivE = do
  pre <- concreteValue fn preO
  pre' <- concreteValue fn preP
  post <- concreteValue fn postO
  post' <- concreteValue fn postP
  equiv <- execGroundFn fn equivE
  desc <- liftIO $ ppRegDiff fn postO postP
  pure RegisterDiff
    { rReg = reg
    , rTypeRepr = macawRegRepr preP
    , rPreOriginal = pre
    , rPrePatched = pre'
    , rPostOriginal = post
    , rPostPatched = post'
    , rPostEquivalent = equiv
    , rDiffDescription = desc
    }

concreteValue ::
  SymGroundEvalFn sym ->
  MacawRegEntry sym tp ->
  EquivM sym arch (ConcreteValue (MS.ToCrucibleType tp))
concreteValue fn e
  | CLM.LLVMPointerRepr _ <- macawRegRepr e
  , ptr <- macawRegValue e = do
    groundBV fn ptr
concreteValue _ e = throwHere (UnsupportedRegisterType (Some (macawRegRepr e)))

groundTraceDiff :: forall sym arch.
  SymGroundEvalFn sym ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (MemTraceDiff arch)
groundTraceDiff fn mem1 mem2 = do
  foot1 <- withSymIO $ \sym -> MT.traceFootprint sym (MT.memSeq mem1)
  foot2 <- withSymIO $ \sym -> MT.traceFootprint sym (MT.memSeq mem2)
  let foot = S.union foot1 foot2
  (S.toList . S.fromList) <$> mapM checkFootprint (S.toList foot)
  where
    checkFootprint ::
      MT.MemFootprint sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (MemOpDiff arch)
    checkFootprint (MT.MemFootprint ptr w dir cond) = do
      let repr = MM.BVMemRepr w MM.BigEndian
      val1 <- withSymIO $ \sym -> MT.readMemArr sym (MT.memArr mem1) ptr repr
      val2 <- withSymIO $ \sym -> MT.readMemArr sym (MT.memArr mem2) ptr repr
      cond' <- memOpCondition cond
      op1  <- groundMemOp fn ptr cond' val1
      op2  <- groundMemOp fn ptr cond' val2
      return $ MemOpDiff { mDirection = dir
                         , mOpOriginal = op1
                         , mOpRewritten = op2
                         }


groundMemOp ::
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  W4.Pred sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (GroundMemOp arch)
groundMemOp fn addr cond val = liftA3 GroundMemOp
  (groundLLVMPointer fn addr)
  (execGroundFn fn cond)
  (groundBV fn val)

groundBV ::
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (GroundBV w)
groundBV fn (CLM.LLVMPointer reg off) = do
  W4.BaseBVRepr w <- return $ W4.exprType off
  greg <- execGroundFn fn reg
  goff <- execGroundFn fn off
  let gbv = mkGroundBV w greg goff
  return gbv



groundLLVMPointer :: forall sym arch.
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (GroundLLVMPointer (MM.ArchAddrWidth arch))
groundLLVMPointer fn ptr = groundBVAsPointer <$> groundBV fn ptr


trivialGlobalMap :: MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap _ _ reg off = pure (CLM.LLVMPointer reg off)

-- TODO: What should happen if the Pred sym in a PartialRes in pres or pres' is false?
getGPValueAndTrace ::
  forall sym arch p ext.
  CS.ExecResult p sym ext (CS.RegEntry sym (MS.ArchRegStruct arch)) ->
  EquivM sym arch
    ( MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
    , MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    , MT.ExitClassifyImpl sym
    )
getGPValueAndTrace (CS.FinishedResult _ pres) = do
  mem <- asks envMemTraceVar
  eclass <- asks envExitClassVar
  case pres ^. CS.partialValue of
    CS.GlobalPair val globs
      | Just mt <- CGS.lookupGlobal mem globs
      , Just jc <- CGS.lookupGlobal eclass globs -> withValid $ do
        val' <- structToRegState @sym @arch val
        return $ (val', mt, jc)
    _ -> throwError undefined
getGPValueAndTrace (CS.AbortedResult _ ar) = throwHere . SymbolicExecutionFailed . ppAbortedResult $ ar
getGPValueAndTrace (CS.TimeoutResult _) = throwHere (SymbolicExecutionFailed "timeout")


structToRegState :: forall sym arch.
  CS.RegEntry sym (MS.ArchRegStruct arch) ->
  EquivM sym arch (MM.RegState (MM.ArchReg arch) (MacawRegEntry sym))
structToRegState e = do
  archVs <- asks $ envArchVals
  return $ MM.mkRegState (macawRegEntry . MS.lookupReg archVs e)


regStateToAsn :: forall sym arch.
  MM.RegState (MM.ArchReg arch) (MacawRegEntry sym) ->
  EquivM sym arch (Ctx.Assignment (CS.RegValue' sym)  (MS.MacawCrucibleRegTypes arch))
regStateToAsn regs = do
  archFs <- archFuns
  let allRegsAsn = MS.crucGenRegAssignment archFs
  return $ MS.macawAssignToCruc (\(MacawRegEntry _ v) -> CS.RV @sym v) $
    TFC.fmapFC (\r -> regs ^. MM.boundValue r) allRegsAsn



unconstrainedRegister ::
  forall sym arch tp.
  ConcreteBlock arch ->
  MM.ArchReg arch tp ->
  EquivM sym arch (MacawRegEntry sym tp)
unconstrainedRegister blk reg = do
  archFs <- archFuns
  let
    symbol = MS.crucGenArchRegName archFs reg
    repr = MM.typeRepr reg
  case repr of
    -- | Instruction pointers are exactly the start of the block
    _ | Just Refl <- testEquality reg (MM.ip_reg @(MM.ArchReg arch)) ->
      withSymIO $ \sym -> do
        ptr <- concreteToLLVM sym $ concreteAddress blk
        return $ MacawRegEntry (MS.typeToCrucible repr) ptr
    -- | Stack pointer is in a unique region
    _ | Just Refl <- testEquality reg (MM.sp_reg @(MM.ArchReg arch)) -> do
        stackRegion <- asks envStackRegion
        withSymIO $ \sym -> do
          bv <- W4.freshConstant sym symbol W4.knownRepr
          let ptr = CLM.LLVMPointer stackRegion bv
          return $ MacawRegEntry (MS.typeToCrucible repr) ptr
    MM.BVTypeRepr n -> withSymIO $ \sym -> do
      bv <- W4.freshConstant sym symbol (W4.BaseBVRepr n)
      -- TODO: This fixes the region to 0. Is that okay?
      ptr <- CLM.llvmPointer_bv sym bv
      return $ MacawRegEntry (MS.typeToCrucible repr) ptr
    _ -> throwHere (UnsupportedRegisterType (Some (MS.typeToCrucible repr)))

initialRegisterState ::
  ConcreteBlock arch ->
  MM.RegState (MM.ArchReg arch) (MacawRegEntry sym) ->
  MM.ArchReg arch tp ->
  EquivM sym arch (MacawRegEntry sym tp)
initialRegisterState blk regs reg = case preStableReg blk reg of
  True -> return $ regs ^. MM.boundValue reg
  False -> unconstrainedRegister blk reg

lookupBlocks ::
  ParsedFunctionMap arch ->
  ConcreteBlock arch ->
  EquivM sym arch (CC.Some (Compose [] (MD.ParsedBlock arch)))
lookupBlocks pfm b = case M.assocs $ M.unions $ fmap snd $ IM.lookupLE i pfm of
  [(start', CC.Some (ParsedBlockMap pbm))] -> do
    case concreteBlockEntry b of
      BlockEntryInitFunction -> do
        funAddr <- segOffToAddr start'
        when (funAddr /= start) $
          throwHere $ LookupNotAtFunctionStart start
      _ -> return ()
    let result = concat $ IM.elems $ IM.intersecting pbm i
    return $ CC.Some (Compose result)
  blks -> throwHere $ NoUniqueFunctionOwner i (fst <$> blks)
  where
  start@(ConcreteAddress addr) = concreteAddress b
  end = ConcreteAddress (MM.MemAddr (MM.addrBase addr) maxBound)
  i = IM.OpenInterval start end

data BlockTarget arch =
  BlockTarget
    { targetCall :: ConcreteBlock arch
    , targetReturn :: Maybe (ConcreteBlock arch)
    }

instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (BlockTarget arch) where
  show (BlockTarget a b) = "BlockTarget (" ++ show a ++ ") " ++ "(" ++ show b ++ ")"

-- | From the given starting point, find all of the accessible
-- blocks
getSubBlocks ::
  forall sym arch.
  ParsedFunctionMap arch ->
  ConcreteBlock arch ->
  EquivM sym arch [BlockTarget arch]
getSubBlocks pfm b = case M.assocs $ M.unions $ fmap snd $ IM.lookupLE i pfm of
  [(_, CC.Some (ParsedBlockMap pbm))] -> do
    let pbs = concat $ IM.elems $ IM.intersecting pbm i
    concat <$> mapM (concreteExternalJumpTargets pbs) pbs
  blks -> throwHere $ NoUniqueFunctionOwner i (fst <$> blks)
  where
  start@(ConcreteAddress saddr) = concreteAddress b
  end = ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
  i = IM.OpenInterval start end

concreteExternalJumpTargets ::
  forall sym arch ids.
  ValidArch arch =>
  [MD.ParsedBlock arch ids] ->
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch]
concreteExternalJumpTargets allPbs pb = do
  targets <- concreteJumpTargets pb
  addrs <- mapM (segOffToAddr . MD.pblockAddr) allPbs
  let
    isTargetExternal btgt = not ((concreteAddress (targetCall btgt)) `elem` addrs)
  return $ filter isTargetExternal targets

mkConcreteBlock ::
  BlockEntryKind arch ->
  ConcreteAddress arch ->
  ConcreteBlock arch
mkConcreteBlock k a = ConcreteBlock a k

concreteNextIPs ::
  ValidArch arch =>
  MM.RegState (MM.ArchReg arch) (MM.Value arch ids) ->
  [ConcreteAddress arch]
concreteNextIPs st = concreteValueAddress $ st ^. MM.curIP

concreteValueAddress ::
  MM.Value arch ids (MM.BVType (MM.ArchAddrWidth arch)) ->
  [ConcreteAddress arch]
concreteValueAddress = \case
  MM.RelocatableValue _ addr -> [ConcreteAddress addr]
  MM.AssignedValue (MM.Assignment _ rhs) -> case rhs of
    MM.EvalApp (MM.Mux _ _ b1 b2) -> concreteValueAddress b1 ++ concreteValueAddress b2
    _ -> []
  _ -> []

concreteJumpTargets ::
  forall sym arch ids.
  ValidArch arch =>
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch]
concreteJumpTargets pb = case MD.pblockTermStmt pb of
  MD.ParsedCall st ret -> go (concreteNextIPs st) ret

  MD.PLTStub st _ _ -> case MapF.lookup (MM.ip_reg @(MM.ArchReg arch)) st of
    Just addr -> go (concreteValueAddress addr) Nothing
    _ -> return $ []
  MD.ParsedJump _ tgt -> do
    blk <- mkConcreteBlock BlockEntryJump <$> segOffToAddr tgt
    return $ [ BlockTarget blk Nothing ]
  MD.ParsedBranch _ _ t f -> do
    blk_t <- mkConcreteBlock BlockEntryJump <$> segOffToAddr t
    blk_f <- mkConcreteBlock BlockEntryJump <$> segOffToAddr f
    return $ [ BlockTarget blk_t Nothing, BlockTarget blk_f Nothing ]
  MD.ParsedLookupTable st _ _ -> go (concreteNextIPs st) Nothing
  MD.ParsedArchTermStmt _ st _ -> do
    return $ [ BlockTarget (mkConcreteBlock BlockEntryPostArch next) Nothing
             | next <- (concreteNextIPs st) ]
  _ -> return []
  where
    go ::
      [ConcreteAddress arch] ->
      Maybe (MM.ArchSegmentOff arch) ->
      EquivM sym arch [BlockTarget arch]
    go next_ips ret = do
      ret_blk <- fmap (mkConcreteBlock BlockEntryPostFunction) <$> mapM segOffToAddr ret
      return $ [ BlockTarget (mkConcreteBlock BlockEntryInitFunction next) ret_blk | next <- next_ips ]


segOffToAddr ::
  MM.ArchSegmentOff arch ->
  EquivM sym arch (ConcreteAddress arch)
segOffToAddr off = concreteFromAbsolute <$>
  liftMaybe (MM.segoffAsAbsoluteAddr off) (NonConcreteParsedBlockAddress off)

liftMaybe :: Maybe a -> InnerEquivalenceError arch -> EquivM sym arch a
liftMaybe Nothing e = throwHere e
liftMaybe (Just a) _ = pure a

runDiscovery ::
  ValidArch arch =>
  PB.LoadedELF arch ->
  ExceptT (EquivalenceError arch) IO (MM.MemSegmentOff (MM.ArchAddrWidth arch), ParsedFunctionMap arch)
runDiscovery elf = do
  let
    bin = PB.loadedBinary elf
    archInfo = PB.archInfo elf
  entries <- toList <$> MBL.entryPoints bin
  pfm <- goDiscoveryState $
    MD.cfgFromAddrs archInfo (MBL.memoryImage bin) M.empty entries []
  return (head entries, pfm)
  where
  goDiscoveryState ds = id
    . fmap (IM.unionsWith M.union)
    . mapM goSomeDiscoveryFunInfo
    . M.assocs
    $ ds ^. MD.funInfo
  goSomeDiscoveryFunInfo (entrySegOff, CC.Some dfi) = markEntryPoint entrySegOff <$> goDiscoveryFunInfo dfi
  goDiscoveryFunInfo dfi = fmap (ParsedBlockMap . IM.fromListWith (++)) . sequence $
    [ (\addrs -> (addrs, [pb])) <$> archSegmentOffToInterval blockSegOff (MD.blockSize pb)
    | (blockSegOff, pb) <- M.assocs (dfi ^. MD.parsedBlocks)
    ]

archSegmentOffToInterval ::
  (MonadError (EquivalenceError arch) m, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  MM.ArchSegmentOff arch ->
  Int ->
  m (IM.Interval (ConcreteAddress arch))
archSegmentOffToInterval segOff size = case MM.segoffAsAbsoluteAddr segOff of
  Just w -> pure (IM.IntervalCO start (start `addressAddOffset` fromIntegral size))
    where start = concreteFromAbsolute w
  Nothing -> throwError $ equivalenceError $ StrangeBlockAddress segOff

buildBlockMap ::
  [PatchPair arch] ->
  BlockMapping arch ->
  BlockMapping arch
buildBlockMap pairs bm = foldr go bm pairs
  where
    go :: PatchPair arch -> BlockMapping arch -> BlockMapping arch
    go (PatchPair orig patched) (BlockMapping m) =
      BlockMapping $ M.alter (doAddAddr (concreteAddress patched)) (concreteAddress orig) m

-- | Prefer existing entries
doAddAddr ::
  ConcreteAddress arch ->
  Maybe (ConcreteAddress arch) ->
  Maybe (ConcreteAddress arch)
doAddAddr _ (Just addr) = Just addr
doAddAddr addr Nothing = Just addr


getAllPairs :: EquivM sym arch [PatchPair arch]
getAllPairs = do
  EquivState open closed failed <- get
  return $ S.toList $ S.union (S.union open closed) failed

getBlockMap :: EquivM sym arch (BlockMapping arch)
getBlockMap = do
  BlockMapping m <- asks envBlockMapping
  pairs <- getAllPairs
  let m' =
        foldr (\(PatchPair o p) ->
                 M.alter (doAddAddr (concreteAddress p)) (concreteAddress o)) m pairs
  return $ BlockMapping m'


mkIPEquivalence ::
  EquivM sym arch (
    CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
    CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
    IO (W4.Pred sym)
    )
mkIPEquivalence = do
  BlockMapping blockMap <- getBlockMap
  let assocs = filter (\(blkO, blkP) -> blkO /= blkP) $ M.assocs blockMap
  withSymIO $ \sym -> do
    ips <- traverse (concreteToLLVM sym . fst) assocs
    ips' <- traverse (concreteToLLVM sym . snd) assocs
    let [regSS, offSS, regSS', offSS', ipEqSS] = map userSymbol $
          ["orig_reg", "orig_off", "rewrite_reg", "rewrite_off", "related_ips"]
    regionVar  <- W4.freshBoundVar sym regSS  W4.knownRepr
    offsetVar  <- W4.freshBoundVar sym offSS  W4.knownRepr
    regionVar' <- W4.freshBoundVar sym regSS' W4.knownRepr
    offsetVar' <- W4.freshBoundVar sym offSS' W4.knownRepr

    let ipArg  = CLM.LLVMPointer (W4.varExpr sym regionVar ) (W4.varExpr sym offsetVar )
        ipArg' = CLM.LLVMPointer (W4.varExpr sym regionVar') (W4.varExpr sym offsetVar')
        iop <&&> iop' = do
          p  <- iop
          p' <- iop'
          W4.andPred sym p p'
    alternatives <- flipZipWithM ips ips' $ \ip ip' -> llvmPtrEq sym ipArg ip <&&> llvmPtrEq sym ipArg' ip'
    anyAlternative <- foldM (W4.orPred sym) (W4.falsePred sym) alternatives

    tableEntries <- forM ips $ \ip -> llvmPtrEq sym ipArg ip
    isInTable <- foldM (W4.orPred sym) (W4.falsePred sym) tableEntries

    plainEq <- llvmPtrEq sym ipArg ipArg'
    -- only if the first entry is in this table do we consult this table, otherwise
    -- we require actual pointer equality
    body <- W4.baseTypeIte sym isInTable anyAlternative plainEq

    ipEqSymFn <- W4.definedFn sym
      ipEqSS
      (Ctx.empty `Ctx.extend` regionVar `Ctx.extend` offsetVar `Ctx.extend` regionVar' `Ctx.extend` offsetVar')
      body
      W4.AlwaysUnfold

    pure $ \(CLM.LLVMPointer region offset) (CLM.LLVMPointer region' offset') -> W4.applySymFn sym ipEqSymFn
      (Ctx.empty `Ctx.extend` region `Ctx.extend` offset `Ctx.extend` region' `Ctx.extend` offset')


data RegEquivCheck sym arch where
  RegEquivCheck ::
    (forall tp.
      MT.ExitCase ->
      MM.ArchReg arch tp ->
      MacawRegEntry sym tp ->
      MacawRegEntry sym tp ->
      IO (W4.Pred sym)) ->
    RegEquivCheck sym arch


mkRegEquivCheck ::
  forall sym arch.
  SimulationResult sym arch ->
  SimulationResult sym arch ->
  EquivM sym arch (RegEquivCheck sym arch)
mkRegEquivCheck _simResultO _simResultP = do

  withSymIO $ \sym -> return $ RegEquivCheck $ \ecase reg (MacawRegEntry repr bvO) (MacawRegEntry _ bvP) -> do
    case repr of
        CLM.LLVMPointerRepr _ -> case testEquality reg ipReg of
          Just Refl ->
            -- IP equivalence is checked in the post-state through function discovery

            return $ W4.truePred sym
            -- TODO: What to do with the link register (index 1 in the current
            -- register struct for PPC64)? Is ipEq good enough? Things to worry
            -- about with that choice:
            -- 1. We should probably initialize the link register somehow for both
            -- blocks so that the register starts out equivalent. Would be sort of
            -- a shame to declare blocks inequivalent because they both started
            -- with 0 in their LR and didn't change that.
            -- 2. ipEq declares the starts of blocks equivalent. blr tends to come
            -- at the end of blocks, not the start.

            -- TODO: Stack pointer need not be equivalent in general, but we need to treat stack-allocated
            -- variables specially to reason about how they may be offset

          -- | For registers used for function arguments, we assert equivalence when
          -- the jump target is known to be a function call
          _ | funCallArg reg -> case ecase of
                MT.ExitCall -> llvmPtrEq sym bvO bvP
                _ -> return $ W4.truePred sym
          _ | funCallRet reg -> case ecase of
                MT.ExitReturn -> llvmPtrEq sym bvO bvP
                _ -> return $ W4.truePred sym
          _ | funCallStable reg -> llvmPtrEq sym bvO bvP
          -- FIXME: We need to calculate the equivalence condition on functions based on
          -- how they are used
          --_ | False, funCallStable reg -> do
          --      let
          --        preBvO = (resultPreRegs simResultO) ^. MM.boundValue reg
          --        preBvP = (resultPreRegs simResultP) ^. MM.boundValue reg
          --      case ecase of
          --        MT.ExitReturn -> do
          --          eqO <- llvmPtrEq sym (macawRegValue preBvO) bvO
          --          eqP <- llvmPtrEq sym (macawRegValue preBvP) bvP
          --          W4.andPred sym eqO eqP
          --        _ -> return $ W4.truePred sym

          _ -> return $ W4.truePred sym
        _ -> error "Unsupported register type"
  where
    ipReg = MM.ip_reg @(MM.ArchReg arch)
    

flipZipWithM :: Monad m => [a] -> [b] -> (a -> b -> m c) -> m [c]
flipZipWithM as bs f = zipWithM f as bs

userSymbol :: String -> W4.SolverSymbol
userSymbol s = case W4.userSymbol s of
  Left err -> error $ "Bad solver symbol:" ++ show err
  Right ss -> ss

concreteToLLVM ::
  ( 
   w ~ MM.ArchAddrWidth arch, MM.MemWidth w, KnownNat w, 1 <= w
  , W4.IsExprBuilder sym
  ) =>
  sym ->
  ConcreteAddress arch ->
  IO (CLM.LLVMPtr sym w)
concreteToLLVM sym c = do
  region <- W4.natLit sym 0
  offset <- W4.bvLit sym W4.knownRepr (BVS.mkBV W4.knownRepr (toInteger (absoluteAddress c)))
  pure (CLM.LLVMPointer region offset)

llvmPtrEq ::
  CB.IsSymInterface sym =>
  sym ->
  CLM.LLVMPtr sym w ->
  CLM.LLVMPtr sym w ->
  IO (W4.Pred sym)
llvmPtrEq sym (CLM.LLVMPointer region offset) (CLM.LLVMPointer region' offset') = do
  regionsEq <- W4.isEq sym region region'
  offsetsEq <- W4.isEq sym offset offset'
  W4.andPred sym regionsEq offsetsEq
