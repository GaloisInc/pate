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
  , mkIPEquivalence
  ) where

import           Prelude hiding ( fail )

import           GHC.Stack
import           Data.Typeable
import           Data.Bits
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Exception

import           Control.Applicative
import           Control.Lens hiding ( op, pre )
import           Control.Monad.Except
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.ST

import qualified Data.IORef as IO
import qualified Data.BitVector.Sized as BVS
import           Data.Foldable
import           Data.Functor.Compose
import qualified Data.IntervalMap as IM
import           Data.List
import           Data.Maybe (catMaybes)
import qualified Data.Map as M
import           Data.Word (Word64)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.String
import qualified Data.Time as TM
import           Data.Type.Equality (testEquality)
import           GHC.TypeLits
import qualified Lumberjack as LJ
import           System.IO
import qualified Data.HashTable.ST.Basic as H

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MM


import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Data.Parameterized.Map as MapF


import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified What4.Expr.Builder as W4B
import qualified What4.SemiRing as SR

import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.Symbol as W4
import qualified What4.Partial as W4P
import qualified What4.ProblemFeatures as W4PF
import qualified What4.ProgramLoc as W4L
import qualified What4.Protocol.Online as W4O
import qualified What4.Solver.Yices as W4Y
--import qualified What4.Protocol.SMTWriter as W4O
import qualified What4.SatResult as W4R
--import qualified What4.Protocol.SMTLib2 as SMT2

import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import           Pate.Types
import           Pate.Monad
import qualified Pate.Memory.MemTrace as MT

import qualified What4.Config as W4C
import qualified Data.Text as T

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
  (oMain, oPfm)  <- runDiscovery elf
  (pMain, pPfm) <- runDiscovery elf'

  liftIO $ LJ.writeLog logAction (PE.LoadedBinaries (elf, oPfm) (elf', pPfm))

  Some gen' <- liftIO N.newIONonceGenerator
  let pfeats = W4PF.useBitvectors .|. W4PF.useSymbolicArrays .|. W4PF.useIntegerArithmetic .|. W4PF.useStructs
  CBO.withYicesOnlineBackend W4B.FloatRealRepr gen' CBO.NoUnsatFeatures pfeats $ \sym -> do
    let cfg = W4.getConfiguration sym
    --pathSetter <- liftIO $ W4C.getOptionSetting CBO.solverInteractionFile cfg
    timeout <- liftIO $ W4C.getOptionSetting W4Y.yicesGoalTimeout cfg
    void $ liftIO $ W4C.setOpt timeout 5
    
    
    --[] <- liftIO $ W4C.setOpt pathSetter (T.pack "./solver.out")
    proc <- liftIO $ CBO.withSolverProcess sym (fail "invalid") return

    
    eval <- lift (MS.withArchEval vals sym pure)
    model <- lift (MT.mkMemTraceVar @arch ha)
    evar <- lift (MT.mkExitClassVar @arch ha)
    pvar <- lift (MT.mkReturnIPVar @arch ha)
    undefops <- liftIO $ MT.mkUndefinedPtrOps sym
    
    -- FIXME: we should be able to lift this from the ELF, and it may differ between
    -- binaries
    stackRegion <- liftIO $ W4.natLit sym 1
    let
      exts = MT.macawTraceExtensions eval model evar pvar (trivialGlobalMap @_ @arch) undefops

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
        { envSym = sym
        , envProc = proc
        , envWhichBinary = Nothing
        , envCtx = ctxt
        , envArchVals = vals
        , envExtensions = exts
        , envStackRegion = stackRegion
        , envMemTraceVar = model
        , envExitClassVar = evar
        , envReturnIPVar = pvar
        , envBlockMapping = buildBlockMap pPairs blockMap
        , envLogger = logAction
        , envDiscoveryCfg = dcfg
        , envPrecondProp = PropagateComputedDomains
        , envFreeVars = []
        }

    liftIO $ do
      putStr "\n"
      stats <- runVerificationLoop env pPairs
      liftIO . putStr $ ppEquivalenceStatistics stats
      return $ equivSuccess stats

data RegisterCase arch tp where
  RegIP :: RegisterCase arch (MM.BVType (MM.ArchAddrWidth arch))
  RegSP :: RegisterCase arch (MM.BVType (MM.ArchAddrWidth arch))
  RegTOC :: RegisterCase arch (MM.BVType (MM.ArchAddrWidth arch))
  RegG :: RegisterCase arch tp

registerCase ::
  forall arch tp.
  ValidArch arch =>
  MM.ArchReg arch tp ->
  RegisterCase arch tp
registerCase r = case testEquality r (MM.ip_reg @(MM.ArchReg arch)) of
  Just Refl -> RegIP
  _ -> case testEquality r (MM.sp_reg @(MM.ArchReg arch)) of
    Just Refl -> RegSP
    _ -> case toc_reg @arch of
      Just r' | Just Refl <- testEquality r r' -> RegTOC
      _ -> RegG

registerEquivalence ::
  forall sym arch.
  EquivM sym arch (RegEquivRelation sym arch)
registerEquivalence = withSym $ \sym -> do
  return $ RegEquivRelation $ \r vO vP -> do
    case registerCase r of
      RegIP -> return $ W4.truePred sym
      RegSP -> do
        let
          CLM.LLVMPointer _ offO = macawRegValue vO
          CLM.LLVMPointer _ offP = macawRegValue vP
        W4.isEq sym offO offP
      _ -> equalValuesIO sym vO vP

baseEquivRelation ::
  EquivM sym arch (EquivRelation sym arch)
baseEquivRelation = withSym $ \sym -> do
  stackRegion <- asks envStackRegion
  let
    isStackCell cell = do
      let CLM.LLVMPointer region _ = cellPtr cell
      W4.isEq sym region stackRegion

    memEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell >>= W4.notPred sym) $
        MT.llvmPtrEq sym vO vP

    stackEq = MemEquivRelation $ \cell vO vP -> do
      impM sym (isStackCell cell) $
        MT.llvmPtrEq sym vO vP
  regEq <- registerEquivalence 
  return $ EquivRelation regEq stackEq memEq

trivialEquivRelation :: EquivM sym arch (EquivRelation sym arch)
trivialEquivRelation = withSym $ \sym -> do
  return $ EquivRelation
    (RegEquivRelation (\_ _ _-> return $ W4.truePred sym))
    (MemEquivRelation (\_ _ _-> return $ W4.truePred sym))
    (MemEquivRelation (\_ _ _-> return $ W4.truePred sym))

topLevelPostRegisterDomain ::
  forall sym arch.
  EquivM sym arch (M.Map (Some (MM.ArchReg arch)) (W4.Pred sym))
topLevelPostRegisterDomain = withSym $ \sym ->
  case toc_reg @arch of
    Just r -> return $ M.singleton (Some r) (W4.truePred sym)
    Nothing -> return M.empty

-- | Default toplevel post-domain:
--   table of contents register (if present)
--   global (non-stack) memory
topLevelPostDomain ::
  HasCallStack =>
  EquivM sym arch (StatePredSpec sym arch)
topLevelPostDomain = withFreshVars $ \stO stP -> withSym $ \sym -> do
  regDomain <- topLevelPostRegisterDomain
  withAssumption (validInitState Nothing stO stP) $
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


-- | Default toplevel pre-domain:
--   all registers, stack, and memory
--   IPs match given patchpair
topLevelPreDomain ::
  HasCallStack =>
  PatchPair arch ->
  EquivM sym arch (StatePredSpec sym arch)
topLevelPreDomain pPair = withFreshVars $ \stO stP -> withSym $ \sym -> do
  regDomain <- allRegistersDomain
  withAssumption (validInitState (Just pPair) stO stP) $
    return $ StatePred
      {
        predRegs = regDomain
      , predStack = memPredTrue sym
      , predMem = memPredTrue sym
      }

-- | Domain that includes entire state, except IP register
universalDomain ::
  EquivM sym arch (StatePred sym arch)
universalDomain =  withSym $ \sym -> do
  regDomain <- allRegistersDomain
  return $ StatePred
    {
      predRegs = regDomain
    , predStack = memPredTrue sym
    , predMem = memPredTrue sym
    }

-- | Domain that includes entire state, except IP register
universalDomainSpec ::
  HasCallStack =>
  EquivM sym arch (StatePredSpec sym arch)
universalDomainSpec = withFreshVars $ \stO stP ->
  withAssumption (validInitState Nothing stO stP) $
  universalDomain

-- | Verify equivalence of the given pairs, as well as any
-- resulting pairs that emerge
runVerificationLoop ::
  forall sym arch.
  EquivEnv sym arch ->
  [PatchPair arch] ->
  IO EquivalenceStatistics
runVerificationLoop env pPairs = do
  let
    st = EquivState
          { stOpenTriples = M.empty
          , stProvenTriples = M.empty
          , stSimResults = M.empty
          , stFailedTriples = M.empty
          }
  result <- runExceptT $ runEquivM env st doVerify
  case result of
    Left err -> withValidEnv env $ error (show err)
    Right r -> return r

  where
    doVerify :: EquivM sym arch EquivalenceStatistics
    doVerify = do
      pPairs' <- (asks $ cfgPairMain . envDiscoveryCfg) >>= \case
        True -> do
          mainO <- asks $ binEntry . originalCtx . envCtx
          mainP <- asks $ binEntry . rewrittenCtx . envCtx
          blkO <- mkConcreteBlock BlockEntryInitFunction <$> segOffToAddr mainO
          blkP <- mkConcreteBlock BlockEntryInitFunction <$> segOffToAddr mainP
          let pPair = PatchPair blkO blkP
          return $ pPair : pPairs
        False -> return pPairs
      forM_ pPairs' $ \pPair -> do
        precond <- topLevelPreDomain pPair
        postcond <- topLevelPostDomain
        
        modify $ \st -> st { stOpenTriples = M.insertWith (++) pPair [(precond, postcond)] (stOpenTriples st) }
      checkLoop mempty

    popMap pPair = M.insertLookupWithKey (\_ [] trips -> drop 1 trips) pPair []

    -- | Keep checking for open block pairs
    checkLoop :: EquivalenceStatistics -> EquivM sym arch EquivalenceStatistics
    checkLoop stats = do
      openTriples <- gets stOpenTriples
      case M.keys openTriples of
        (pPair : _) -> case popMap pPair openTriples of
          (Just ((precond, postcond) : _), openTriples') -> do
            stats' <- go pPair precond postcond
            modify $ \st -> st { stOpenTriples = openTriples' }
            checkLoop (stats' <> stats)
          _ -> do
            modify $ \st -> st { stOpenTriples = M.delete pPair (stOpenTriples st) }
            checkLoop stats
        _ -> return stats

    go ::
      PatchPair arch ->
      StatePredSpec sym arch ->
      StatePredSpec sym arch ->
      EquivM sym arch EquivalenceStatistics
    go pPair precond postcond = do
      
      result <- manifestError $ checkEquivalence pPair precond postcond
      case result of
        Left _ -> modify $ \st -> st { stFailedTriples = M.insertWith (++) pPair [(precond, postcond)] (stFailedTriples st) }
        Right _ -> modify $ \st -> st { stProvenTriples = M.insertWith (++) pPair [(precond, postcond)] (stProvenTriples st) }
      printResult result
      normResult <- return $ case result of
        Left err | InequivalentError _ <- errEquivError err -> EquivalenceStatistics 1 0 0
        Left _ -> EquivalenceStatistics 1 0 1
        Right _ -> EquivalenceStatistics 1 1 0
      return normResult


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


freshSimVars ::
  forall bin sym arch.
  EquivM sym arch (SimVars sym arch bin)
freshSimVars = do
  (memtrace, memtraceVar) <- withSymIO $ \sym -> MT.initMemTraceVar sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  regs <- MM.mkRegStateM unconstrainedRegister
  return $ SimVars memtraceVar regs (SimState memtrace (MM.mapRegsWith (\_ -> macawVarEntry) regs))

getGlobals ::
  forall sym arch bin.
  SimInput sym arch bin ->
  EquivM sym arch (CS.SymGlobalState sym)
getGlobals simInput = do
  env <- ask
  ret <- withSymIO $ MT.initRetAddr @_ @arch
  eclass <- withSymIO $ MT.initExitClass
  withValid $ return $
      CGS.insertGlobal (envMemTraceVar env) (simInMem simInput)
    $ CGS.insertGlobal (envReturnIPVar env) ret
    $ CGS.insertGlobal (envExitClassVar env) eclass
    $ CGS.emptyGlobals  
  

ipValidPred ::
  forall sym arch.
  PatchPair arch ->
  SimState sym arch Original ->
  SimState sym arch Patched ->
  EquivM sym arch (W4.Pred sym)
ipValidPred pPair stO stP = withSymIO $ \sym -> do
  let
    regsO = simRegs stO
    regsP = simRegs stP
  ptrO <- concreteToLLVM sym $ concreteAddress $ (pOrig pPair)
  eqO <- MT.llvmPtrEq sym ptrO (macawRegValue $ regsO ^. MM.boundValue (MM.ip_reg @(MM.ArchReg arch)))

  ptrP <- concreteToLLVM sym $ concreteAddress $ (pPatched pPair)
  eqP <- MT.llvmPtrEq sym ptrP (macawRegValue $ regsP ^. MM.boundValue (MM.ip_reg @(MM.ArchReg arch)))
  W4.andPred sym eqO eqP

spValidRegion ::
  forall sym arch.
  SimState sym arch Original ->
  SimState sym arch Patched ->
  EquivM sym arch (W4.Pred sym)
spValidRegion stO stP = withSym $ \sym -> do
  let
    regsO = simRegs stO
    regsP = simRegs stP
    CLM.LLVMPointer regionO _ = (macawRegValue $ regsO ^. MM.boundValue (MM.sp_reg @(MM.ArchReg arch)))
    CLM.LLVMPointer regionP _ = (macawRegValue $ regsP ^. MM.boundValue (MM.sp_reg @(MM.ArchReg arch)))
  stackRegion <- asks envStackRegion
  liftIO $ do
    eqO <-  W4.isEq sym regionO stackRegion
    eqP <- W4.isEq sym regionP stackRegion
    W4.andPred sym eqO eqP

tocValidRegion ::
  forall sym arch.
  SimState sym arch Original ->
  SimState sym arch Patched ->
  EquivM sym arch (W4.Pred sym)
tocValidRegion stO stP = withSym $ \sym ->
  case toc_reg @arch of
    Just r -> do      
      let
        regsO = simRegs stO
        regsP = simRegs stP
        CLM.LLVMPointer regionO _ = (macawRegValue $ regsO ^. MM.boundValue r)
        CLM.LLVMPointer regionP _ = (macawRegValue $ regsP ^. MM.boundValue r)
      stackRegion <- asks envStackRegion
      liftIO $ do
        eqO <- W4.notPred sym =<< W4.isEq sym regionO stackRegion
        eqP <- W4.notPred sym =<< W4.isEq sym regionP stackRegion
        W4.andPred sym eqO eqP
    _ -> return $ W4.truePred sym


allPreds ::
  W4.IsExprBuilder sym =>
  sym ->
  [W4.Pred sym] ->
  IO (W4.Pred sym)
allPreds sym preds = foldr (\p -> andM sym (return p)) (return $ W4.truePred sym) preds

anyPred ::
  W4.IsExprBuilder sym =>
  sym ->
  [W4.Pred sym] ->
  IO (W4.Pred sym)
anyPred sym preds = foldr (\p -> orM sym (return p)) (return $ W4.falsePred sym) preds

checkEquivalence ::
  PatchPair arch ->
  StatePredSpec sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch ()
checkEquivalence pPair precondSpec postcondSpec = withSym $ \sym -> do
  withValid @() $ liftIO $ W4B.startCaching sym
  eqRel <- baseEquivRelation

  result <- manifestError $
    local (\env -> env { envPrecondProp = PropagateExactEquality }) $
    provePostcondition pPair postcondSpec

  genPrecondSpec <- case result of
    Left _ -> provePostcondition pPair postcondSpec
    Right spec -> return spec
  --genPrecondSpec <- provePostcondition pPair postcondSpec
  -- prove that the generated precondition is implied by the given precondition
  void $ withSimSpec precondSpec $ \stO stP precond -> do
    let
      inO = SimInput stO (pOrig pPair)
      inP = SimInput stP (pPatched pPair)
    (asms, genPrecond) <- liftIO $ bindSpec sym stO stP genPrecondSpec      
    preImpliesGen <- liftIO $ impliesPrecondition sym inO inP eqRel precond genPrecond

    isPredTrue preImpliesGen >>= \case
      True -> return ()
      False -> throwHere ImpossibleEquivalence

    --FIXME these are slightly too strong to be provable
    
    isPredTrue asms >>= \case
      True -> return ()
      False -> throwHere UnsatisfiableAssumptions
    
  return ()

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

withAssumption ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch (W4.Pred sym, f)
withAssumption asmf f =
  withSym $ \sym -> withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

withAssumption_ ::
  HasCallStack =>
  EquivM sym arch (W4.Pred sym) ->
  EquivM sym arch f ->
  EquivM sym arch f
withAssumption_ asmf f =
  fmap snd $ withSym $ \sym -> withAssumption' asmf ((\a -> (W4.truePred sym, a)) <$> f)

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

withSimBundle ::
  ExprMappable sym f =>
  PatchPair arch ->
  (SimBundle sym arch -> EquivM sym arch f) ->
  EquivM sym arch (SimSpec sym arch f)
withSimBundle pPair f = withSym $ \sym -> do
  results <- gets stSimResults 
  bundleSpec <- case M.lookup pPair results of
    Just bundleSpec -> return bundleSpec    
    Nothing -> do
      bundleSpec <- withFreshVars $ \stO stP -> do
        let
          simInO_ = SimInput stO (pOrig pPair)
          simInP_ = SimInput stP (pPatched pPair)
        withAssumption' (validInitState (Just pPair) stO stP) $ do
          (asmO, simOutO_) <- simulate simInO_
          (asmP, simOutP_) <- simulate simInP_
          -- FIXME: these are embedded side conditions that end up unsolvable at the top level
          -- We already assert in-place that they should be satisified, so this should be
          -- unnecessary regardless
          --asmO' <- getAsserts simOutO_
          --asmP' <- getAsserts simOutP_
          
          asm <- liftIO $ allPreds sym [ asmO, asmP] --[asmO', asmP']
          return $ (asm, SimBundle simInO_ simInP_ simOutO_ simOutP_)
      modify $ \st -> st { stSimResults = M.insert pPair bundleSpec (stSimResults st) }
      return bundleSpec
  withSimSpec bundleSpec $ \_ _ bundle -> f bundle

withSimSpec ::
  ExprMappable sym f =>
  SimSpec sym arch f ->
  (SimState sym arch Original -> SimState sym arch Patched -> f -> EquivM sym arch g) ->
  EquivM sym arch (SimSpec sym arch g)
withSimSpec spec f = withSym $ \sym -> do
  withFreshVars $ \stO stP -> do
    (asm, body) <- liftIO $ bindSpec sym stO stP spec
    withAssumption (return asm) $ f stO stP body

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

getFootprints ::
  SimBundle sym arch ->
  EquivM sym arch (MemFootprints sym arch)
getFootprints bundle = withSym $ \sym -> do
  footO <- liftIO $ MT.traceFootprint sym (MT.memSeq $ simOutMem $ simOutO bundle)
  footP <- liftIO $ MT.traceFootprint sym (MT.memSeq $ simOutMem $ simOutP bundle)
  return $ S.union footO footP

provePostcondition ::
  PatchPair arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePredSpec sym arch)
provePostcondition pPair postcondSpec = do
  printPreamble pPair
  liftIO $ putStr "\n"
  withSimBundle pPair $ \bundle -> provePostcondition' bundle postcondSpec
      

-- | Prove that a postcondition holds for a function pair starting at
-- this address
provePostcondition' ::
  SimBundle sym arch ->
  StatePredSpec sym arch ->
  EquivM sym arch (StatePred sym arch)
provePostcondition' bundle postcondSpec = withSym $ \sym -> do
  pairs <- discoverPairs bundle

  preconds <- forM pairs $ \(blktO, blktP) -> do
    isTarget <- matchesBlockTarget bundle blktO blktP
    withAssumption (return isTarget) $ do
      let
        blkO = targetCall blktO
        blkP = targetCall blktP
        pPair = PatchPair blkO blkP
      case (targetReturn blktO, targetReturn blktP) of
        (Just blkRetO, Just blkRetP) -> do
          continuecond <- provePostcondition (PatchPair blkRetO blkRetP) postcondSpec
          
          precond <- withSimBundle pPair $ \bundleCall -> do
            -- equivalence condition for when this function returns
            case (concreteBlockEntry blkO, concreteBlockEntry blkP) of
              (BlockEntryPostArch, BlockEntryPostArch) -> universalDomain
              (entryO, entryP) | entryO == entryP -> do
                printPreamble pPair
                -- equivalence condition for calling this function
                provePostcondition' bundleCall continuecond
              _ -> throwHere $ BlockExitMismatch

          -- equivalence condition for the function entry
          proveLocalPostcondition bundle isTarget precond

        (Nothing, Nothing) -> do
          precond <- provePostcondition (PatchPair blkO blkP) postcondSpec
          proveLocalPostcondition bundle isTarget precond
        _ -> throwHere $ BlockExitMismatch
  let noResult = (W4.falsePred sym, statePredFalse sym)

  isReturn <- matchingExits bundle MT.ExitReturn
  precondReturn <- withSatAssumption noResult (return isReturn) $ do
    proveLocalPostcondition bundle isReturn postcondSpec

  isUnknown <- matchingExits bundle MT.ExitUnknown
  precondUnknown <- withSatAssumption noResult (return isUnknown) $ do
    univDom <- universalDomainSpec
    proveLocalPostcondition bundle isUnknown univDom

  let allPreconds = precondReturn:precondUnknown:preconds

  checkCasesTotal bundle allPreconds
  foldM (\stPred (p, (_, stPred')) -> liftIO $ muxStatePred sym p stPred' stPred) (statePredFalse sym) allPreconds

confirmSat ::
  EquivM sym arch ()
confirmSat = withSym $ \sym -> do
  checkSatisfiableWithModel "checkCasesTotal" (W4.truePred sym) $ \satRes -> do
    case satRes of
      W4R.Sat _ -> return ()
      W4R.Unsat _ -> throwHere InconclusiveSAT
      W4R.Unknown -> throwHere InconclusiveSAT
  checkSatisfiableWithModel "checkCasesTotal" (W4.falsePred sym) $ \satRes -> do
    case satRes of
      W4R.Sat _ -> throwHere InconclusiveSAT 
      W4R.Unsat _ -> return ()
      W4R.Unknown -> throwHere InconclusiveSAT

matchingExits ::
  SimBundle sym arch ->
  MT.ExitCase ->
  EquivM sym arch (W4.Pred sym)
matchingExits bundle ecase = withSym $ \sym -> do
  case1 <- liftIO $ MT.isExitCase sym (simOutExit $ simOutO bundle) ecase
  case2 <- liftIO $ MT.isExitCase sym (simOutExit $ simOutP bundle) ecase
  liftIO $ W4.andPred sym case1 case2  

-- | Ensure that the given predicates completely describe all possibilities
checkCasesTotal ::
  HasCallStack =>
  SimBundle sym arch ->
  [(W4.Pred sym, (W4.Pred sym, StatePred sym arch))] ->
  EquivM sym arch ()
checkCasesTotal bundle cases = withSym $ \sym -> do  
  --mergedCases <- liftIO $ foldM (\stPred (p, (_, stPred')) -> muxStatePred sym p stPred' stPred) (statePredFalse sym) cases
  --eqRel <- baseEquivRelation
  --someEqRelPred <- liftIO $ getPrecondition sym bundle eqRel mergedCases
  --someCasePred <- liftIO $ foldM (\p (p', _) -> liftIO $ W4.orPred sym p p') (W4.falsePred sym) cases
  trivialEq <- trivialEquivRelation
  (oBlocks, pBlocks) <- getBlocks bundle
  someCase <- liftIO $ anyPred sym =<< mapM (\(cond, (rel, _)) -> W4.impliesPred sym rel cond) cases
  
  result <- do
    notCheck <- liftIO $ W4.notPred sym someCase
    startedAt <- liftIO TM.getCurrentTime
    checkSatisfiableWithModel "checkCasesTotal" notCheck $ \satRes -> do
      finishedBy <- liftIO TM.getCurrentTime
      let
        duration = TM.diffUTCTime finishedBy startedAt
        emit r = emitEvent (PE.CheckedBranchCompleteness oBlocks pBlocks r duration)
      case satRes of
        W4R.Sat fn -> do
          ir <- getInequivalenceResult InvalidCallPair trivialEq bundle fn
          emit $ PE.BranchesIncomplete ir
          return $ Just ir
        W4R.Unsat _ -> do
          emit PE.BranchesComplete
          return Nothing
        W4R.Unknown -> do
          emit PE.InconclusiveBranches
          throwHere InconclusiveSAT
  throwInequivalenceResult result

-- | Guess a sufficient memory domain that will cause the
-- given postcondition to be satisfied on the given equivalence relations
guessMemoryDomain ::
  forall sym arch.
  SimBundle sym arch ->
  W4.Pred sym ->
  (MT.MemTraceImpl sym (MM.ArchAddrWidth arch), W4.Pred sym) ->
  MemPred sym arch ->
  (forall w. MemCell sym arch w -> EquivM sym arch (W4.Pred sym)) ->
  EquivM sym arch (MemPred sym arch)
guessMemoryDomain bundle goal (memP', goal') memPred cellFilter = withSym $ \sym -> do
  foots <- getFootprints bundle
  cells <- do
    localPred <- liftIO $ addFootPrintsToPred sym foots memPred
    mapMemPred localPred $ \cell p -> do
      isFiltered <- cellFilter cell
      liftIO $ W4.andPred sym p isFiltered

  -- we take the entire reads set of the block and then filter it according
  -- to the polarity of the postcondition predicate
  mapMemPred cells $ \cell p -> do
    let repr = MM.BVMemRepr (cellWidth cell) MM.BigEndian
    p' <- bindMemory memP memP' p
    -- clobber the "patched" memory at exactly this cell
    CLM.LLVMPointer _ freshP <- liftIO $ freshPtr sym (cellWidth cell)
    cell' <- mapExpr' (bindMemory memP memP') cell
    
    memP'' <- liftIO $ MT.writeMemArr sym memP (cellPtr cell') repr freshP
    eqMemP <- liftIO $ W4.isEq sym (MT.memArr memP') (MT.memArr memP'')

    -- see if we can prove that the goal is independent of this clobbering
    asm <- liftIO $ allPreds sym [p, p', eqMemP, goal]
    check <- liftIO $ W4.impliesPred sym asm goal'

    asks envPrecondProp >>= \case
      PropagateExactEquality -> return polarity
      PropagateComputedDomains ->
        isPredTrue' check >>= \case
          True -> liftIO $ W4.baseTypeIte sym polarity (W4.falsePred sym) p
          False -> liftIO $ W4.baseTypeIte sym polarity p (W4.falsePred sym)
  where
    polarity = memPredPolarity memPred
    memP = simInMem $ simInP bundle


guessEquivalenceDomain ::
  forall sym arch.
  SimBundle sym arch ->
  W4.Pred sym ->
  StatePred sym arch ->
  EquivM sym arch (StatePred sym arch)
guessEquivalenceDomain bundle goal postcond = withSym $ \sym -> do
  startedAt <- liftIO TM.getCurrentTime
  
  ExprFilter isBoundInGoal <- getIsBoundFilter goal
  eqRel <- baseEquivRelation
  
  regsDom <- fmap (M.fromList . catMaybes) $
    zipRegStates (simRegs inStO) (simRegs inStP) $ \r vO vP -> do
      isInO <- liftFilterMacaw isBoundInGoal vO
      isInP <- liftFilterMacaw isBoundInGoal vP
      case registerCase r of
        RegSP -> return (Just (Some r, W4.truePred sym))
        RegIP -> return Nothing
        _ | isInO || isInP -> do
          asks envPrecondProp >>= \case
            PropagateExactEquality -> return $ Just (Some r, W4.truePred sym)
            PropagateComputedDomains -> do
              freshO <- freshRegEntry vO

              goal' <- bindMacawReg vO freshO goal
              goalIgnoresReg <- liftIO $ W4.impliesPred sym goal goal'

              isPredTrue' goalIgnoresReg >>= \case
                True -> return $ Nothing
                False -> return $ Just (Some r, W4.truePred sym)         
        _ -> return Nothing
  stackRegion <- asks envStackRegion
  let
    isStackCell cell = do
      let CLM.LLVMPointer region _ = cellPtr cell
      liftIO $ W4.isEq sym region stackRegion
    isNotStackCell cell = do
      p <- isStackCell cell
      liftIO $ W4.notPred sym p

  ExprMapper doEquate <- equateRegisters regsDom bundle
   
  -- rewrite the state elements to explicitly equate registers we have assumed equivalent
  bundle_regsEq <- liftIO $ mapExpr sym doEquate bundle
  goal_regsEq <- liftIO $ doEquate goal
  postcond_regsEq <- liftIO $ mapExpr sym doEquate postcond
  
  memP' <- liftIO $ MT.initMemTrace sym (MM.addrWidthRepr (Proxy @(MM.ArchAddrWidth arch)))
  goal' <- bindMemory memP memP' goal_regsEq
 
  stackDom <- guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (predStack postcond_regsEq) isStackCell
  memDom <- withAssumption_ (liftIO $ memPredPre sym inO inP (eqRelStack eqRel) stackDom) $ do
    guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (predMem postcond_regsEq) isNotStackCell

  finishedBy <- liftIO TM.getCurrentTime
  let duration = TM.diffUTCTime finishedBy startedAt
  (oBlocks, pBlocks) <- getBlocks bundle
  emitEvent (PE.ComputedPrecondition oBlocks pBlocks duration)
  
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

liftFilterMacaw ::
  (forall tp'. W4.SymExpr sym tp' -> IO Bool) ->
  MacawRegEntry sym tp -> EquivM sym arch Bool
liftFilterMacaw f entry = do
  case macawRegRepr entry of
    CLM.LLVMPointerRepr{} -> liftIO $ do
      let CLM.LLVMPointer reg off = macawRegValue entry
      reg' <- f reg
      off' <- f off
      return $ reg' || off'
    repr -> throwHere $ UnsupportedRegisterType (Some repr)

isPredSat ::
  W4.Pred sym ->
  EquivM sym arch Bool
isPredSat p = case W4.asConstantPred p of
  Just b -> return b
  Nothing -> checkSatisfiableWithModel "check" p $ \case
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
    checkSatisfiableWithModel "check" notp $ \case
        W4R.Sat _ -> return False
        W4R.Unsat _ -> return True
        W4R.Unknown -> return False

validInitState ::
  Maybe (PatchPair arch) ->
  SimState sym arch Original ->
  SimState sym arch Patched ->
  EquivM sym arch (W4.Pred sym)
validInitState mpPair stO stP = withSym $ \sym -> do
  ipValid <- case mpPair of
    Just pPair -> ipValidPred pPair stO stP
    Nothing -> return $ W4.truePred sym
  spValid <- spValidRegion stO stP
  tocValid <- tocValidRegion stO stP
  liftIO $ allPreds sym [ipValid, spValid, tocValid]

-- | Prove a local postcondition for a single block slice
proveLocalPostcondition ::
  HasCallStack =>
  SimBundle sym arch ->
  W4.Pred sym ->
  StatePredSpec sym arch ->
  EquivM sym arch (W4.Pred sym, StatePred sym arch)
proveLocalPostcondition bundle branchCase postcondSpec = withSym $ \sym -> do
  eqRel <- baseEquivRelation
  (asm, postcond) <- liftIO $ bindSpec sym (simOutState $ simOutO bundle) (simOutState $ simOutP bundle) postcondSpec
  -- this weakened equivalence relation is only used for error reporting
  (postEqRel, postcondPred) <- liftIO $ getPostcondition sym bundle eqRel postcond
  
  validExits <- liftIO $ do
    let
      MT.ExitClassifyImpl exitO = simOutExit $ simOutO bundle
      MT.ExitClassifyImpl exitP = simOutExit $ simOutP bundle
    W4.isEq sym exitO exitP
  
  fullPostCond <- liftIO $ allPreds sym [postcondPred, validExits, branchCase]  
  eqInputs <- withAssumption_ (return asm) $
    guessEquivalenceDomain bundle fullPostCond postcond
  eqInputsPred <- liftIO $ getPrecondition sym bundle eqRel eqInputs 

  --checks <- liftIO $ W4.impliesPred sym eqInputsPred fullPostCond
  asms <- liftIO $ allPreds sym [eqInputsPred, asm]
  notChecks <- liftIO $ W4.notPred sym fullPostCond
  (oBlocks, pBlocks) <- getBlocks bundle

  startedAt <- liftIO TM.getCurrentTime
  result <- withAssumption_ (return asms) $ do
    checkSatisfiableWithModel "check" notChecks $ \satRes -> do        
      finishedBy <- liftIO TM.getCurrentTime
      let duration = TM.diffUTCTime finishedBy startedAt

      case satRes of
        W4R.Unsat _ -> do
          emitEvent (PE.CheckedEquivalence oBlocks pBlocks PE.Equivalent duration)
          return Nothing
        W4R.Unknown -> do
          emitEvent (PE.CheckedEquivalence oBlocks pBlocks PE.Inconclusive duration)
          throwHere InconclusiveSAT
        W4R.Sat fn -> do
          ir <- getInequivalenceResult InvalidPostState postEqRel bundle fn
          emitEvent (PE.CheckedEquivalence oBlocks pBlocks (PE.Inequivalent ir) duration)
          return $ Just ir
        
  case result of
    Just result' -> throwHere $ InequivalentError result'
    _ -> return (eqInputsPred, eqInputs)


getBlocks ::
  SimBundle sym arch ->
  EquivM sym arch (PE.Blocks arch, PE.Blocks arch)
getBlocks bundle = do
  CC.Some (Compose opbs) <- lookupBlocks blkO
  let oBlocks = PE.Blocks (concreteAddress blkO) opbs
  CC.Some (Compose ppbs) <- lookupBlocks blkP
  let pBlocks = PE.Blocks (concreteAddress blkP) ppbs
  return (oBlocks, pBlocks)
  where
    blkO = simInBlock $ simInO bundle
    blkP = simInBlock $ simInP bundle  

_isIPAligned ::
  forall sym arch.
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (W4.Pred sym)
_isIPAligned (CLM.LLVMPointer _blk offset)
  | bits <- MM.memWidthNatRepr @(MM.ArchAddrWidth arch) = withSymIO $ \sym -> do
    lowbits <- W4.bvSelect sym (W4.knownNat :: W4.NatRepr 0) bits offset
    W4.bvEq sym lowbits =<< W4.bvLit sym bits (BVS.zero bits)

-- Clagged from What4.Builder
type BoundVarMap t = H.HashTable RealWorld Word64 (Set (Some (W4B.ExprBoundVar t)))

boundVars :: W4B.Expr t tp -> IO (BoundVarMap t)
boundVars e0 = do
  visited <- stToIO $ H.new
  _ <- boundVars' visited e0
  return visited

cache :: (Eq k, CC.Hashable k) => H.HashTable RealWorld k r -> k -> IO r -> IO r
cache h k m = do
  mr <- stToIO $ H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      stToIO $ H.insert h k r
      return r

boundVars' :: BoundVarMap t
           -> W4B.Expr t tp
           -> IO (Set (Some (W4B.ExprBoundVar t)))
boundVars' visited (W4B.AppExpr e) = do
  let idx = N.indexValue (W4B.appExprId e)
  cache visited idx $ do
    sums <- sequence (TFC.toListFC (boundVars' visited) (W4B.appExprApp e))
    return $ foldl' S.union S.empty sums
boundVars' visited (W4B.NonceAppExpr e) = do
  let idx = N.indexValue (W4B.nonceExprId e)
  cache visited idx $ do
    sums <- sequence (TFC.toListFC (boundVars' visited) (W4B.nonceExprApp e))
    return $ foldl' S.union S.empty sums
boundVars' visited (W4B.BoundVarExpr v)
  | W4B.QuantifierVarKind <- W4B.bvarKind v = do
      let idx = N.indexValue (W4B.bvarId v)
      cache visited idx $
        return (S.singleton (Some v))
boundVars' _ _ = return S.empty
-- End Clag

-- Collect embedded assertions inside expressions as uninterpreted functions
-- In theory, this allows us to assume that undefined pointers won't occur in in any models we produce
type EmbeddedAssertMap t = H.HashTable RealWorld Word64 (Set (W4B.Expr t W4.BaseBoolType))

isAssert :: W4.SolverSymbol -> Bool
isAssert symbol = T.isPrefixOf (T.pack "assert") $ W4.solverSymbolAsText symbol

getAsserts' ::
  sym ~ W4B.ExprBuilder t st fs =>
  sym ->
  EmbeddedAssertMap t ->
  W4B.Expr t tp ->
  IO (Set (W4B.Expr t W4.BaseBoolType))
getAsserts' sym visited e
  | W4B.NonceAppExpr e' <- e
  , Just (W4B.FnApp fn args) <- W4B.asNonceApp e
  , W4B.UninterpFnInfo argtps _ <- W4B.symFnInfo fn
  , isAssert (W4B.symFnName fn)
  , _ Ctx.:> W4.BaseBoolRepr <- argtps
  , body Ctx.:> cond <- args = do
    let idx = N.indexValue (W4B.nonceExprId e')
    cache visited idx $ do
      bodyAsserts <- mapM (\(Some e'') -> getAsserts' sym visited e'') (TFC.toListFC Some body)
      return $ S.insert cond (S.unions bodyAsserts)
getAsserts' sym visited e
  | Just (W4B.FnApp fn args) <- W4B.asNonceApp e
  , W4B.DefinedFnInfo vars body _ <- W4B.symFnInfo fn = do
    argAsserts <- S.unions <$> mapM (\(Some e') -> getAsserts' sym visited e') (TFC.toListFC Some args)
    asserts <- S.toList <$> getAsserts' sym visited body
    bindings <- return $ Ctx.zipWith VarBinding vars args
    bodyAsserts <- S.fromList <$> mapM (rebindExpr sym bindings) asserts
    return $ S.union argAsserts bodyAsserts
getAsserts' sym visited (W4B.AppExpr e) = do
  let idx = N.indexValue (W4B.appExprId e)
  cache visited idx $ do
    sums <- sequence (TFC.toListFC (getAsserts' sym visited) (W4B.appExprApp e))
    return $ foldl' S.union S.empty sums
getAsserts' sym visited (W4B.NonceAppExpr e) = do
  let idx = N.indexValue (W4B.nonceExprId e)
  cache visited idx $ do
    sums <- sequence (TFC.toListFC (getAsserts' sym visited) (W4B.nonceExprApp e))
    return $ foldl' S.union S.empty sums
getAsserts' _ _ _ = return S.empty

extractAssertions ::
  ExprMappable sym f =>
  sym ->
  f ->
  IO f
extractAssertions sym f = do
  cache <- W4B.newIdxCache
  return $ error ""

getSubExprs ::
  forall sym f.
  W4.IsSymExprBuilder sym =>
  ExprMappable sym f =>
  sym ->
  f ->
  IO ([Some (W4.SymExpr sym)])
getSubExprs sym f = do
  ref <- IO.newIORef []
  let
    docollect :: forall tp. W4.SymExpr sym tp -> IO (W4.SymExpr sym tp)
    docollect e = do
      IO.modifyIORef ref (\es -> (Some e) : es)
      return e
  _ <- mapExpr sym docollect f
  IO.readIORef ref

getAssertsIO ::
  sym ~ W4B.ExprBuilder t st fs =>
  ExprMappable sym f =>
  sym ->
  f ->
  IO (Set (W4B.Expr t W4.BaseBoolType))
getAssertsIO sym f = do
  visited <- stToIO $ H.new
  exprs <- getSubExprs sym f
  foldM (\s (Some e) -> S.union s <$> getAsserts' sym visited e) S.empty exprs

getAsserts ::
  ExprMappable sym f =>
  f ->
  EquivM sym arch (W4.Pred sym)
getAsserts f = withValid $ withSymIO $ \sym -> do
  asms <- getAssertsIO sym f
  allPreds sym (S.toList asms)

newtype ExprFilter sym = ExprFilter (forall tp'. W4.SymExpr sym tp' -> IO Bool)

getIsBoundFilter ::
  W4.SymExpr sym tp ->
  EquivM sym arch (ExprFilter sym)
getIsBoundFilter expr = withValid $ do
  bvs <- liftIO $ boundVars expr
  return $ ExprFilter $ \bv -> do
    case bv of
      W4B.BoundVarExpr bv' -> do
        let idx = N.indexValue (W4B.bvarId bv')
        stToIO $ H.lookup bvs idx >>= \case
          Just bvs' -> return $ S.member (Some bv') bvs'
          _ -> return False
      _ -> return False

equalValues ::
  MacawRegEntry sym tp ->
  MacawRegEntry sym tp' ->
  EquivM sym arch (W4.Pred sym)
equalValues entry1 entry2 = withSymIO $ \sym -> equalValuesIO sym entry1 entry2

equalValuesIO ::
  W4.IsExprBuilder sym =>
  sym ->
  MacawRegEntry sym tp ->
  MacawRegEntry sym tp' ->
  IO (W4.Pred sym)
equalValuesIO sym entry1 entry2 = case (macawRegRepr entry1, macawRegRepr entry2) of
  (CLM.LLVMPointerRepr w1, CLM.LLVMPointerRepr w2) ->
    case testEquality w1 w2 of
      Just Refl -> liftIO $ MT.llvmPtrEq sym (macawRegValue entry1) (macawRegValue entry2)
      Nothing -> return $ W4.falsePred sym
  _ -> fail "equalValues: unsupported type"


asVar ::
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.BoundVar sym tp')
asVar expr = withValid $ case expr of
  W4B.BoundVarExpr bv' -> return bv'
  _ -> throwHere UnexpectedNonBoundVar

macawRegBinding ::
  MacawRegEntry sym tp ->
  -- ^ value to rebind
  MacawRegEntry sym tp ->
  -- ^ new value
  EquivM sym arch ([Some (VarBinding sym)])
macawRegBinding var val = do
  case macawRegRepr var of
    CLM.LLVMPointerRepr _ -> do
      CLM.LLVMPointer regVar offVar <- return $ macawRegValue var
      CLM.LLVMPointer regVal offVal <- return $ macawRegValue val
      regVar' <- asVar regVar
      offVar' <- asVar offVar
      return $ [Some $ VarBinding regVar' regVal, Some $ VarBinding offVar' offVal]
    repr -> throwHere $ UnsupportedRegisterType (Some repr)

bindMacawReg ::
  MacawRegEntry sym tp ->
  -- ^ value to rebind
  MacawRegEntry sym tp ->
  -- ^ new value
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')
bindMacawReg var val expr = withSym $ \sym -> do
  Some binds <- Ctx.fromList <$> macawRegBinding var val
  liftIO $ rebindExpr sym binds expr

mapExpr' ::
  ExprMappable sym f =>
  (forall tp. W4.SymExpr sym tp -> EquivM sym arch (W4.SymExpr sym tp)) ->
  f ->
  EquivM sym arch f
mapExpr' f e = withSym $ \sym ->
  IO.withRunInIO $ \runInIO -> mapExpr sym (\a -> runInIO (f a)) e

newtype ExprMapper sym = ExprMapper (forall tp'. W4.SymExpr sym tp' -> IO (W4.SymExpr sym tp'))

equateRegisters ::
  M.Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  SimBundle sym arch ->
  EquivM sym arch (ExprMapper sym)
equateRegisters regRel bundle = withSym $ \sym -> do
  eqRel <- baseEquivRelation
  
  Some binds <- fmap (Ctx.fromList . concat) $ zipRegStates (simRegs inStO) (simRegs inStP) $ \r vO vP -> do
     p <- liftIO $ applyRegEquivRelation (eqRelRegs eqRel) r vO vP
     case M.lookup (Some r) regRel of
       Just cond | Just True <- W4.asConstantPred cond -> do
         eqVals <- equalValues vO vP
         (W4.asConstantPred <$> liftIO (W4.isEq sym p eqVals)) >>= \case
           Just True -> macawRegBinding vO vP
           _ -> return []
       _ -> return []
  return $ ExprMapper $ rebindExpr sym binds
  where
    inStO = simInState $ simInO bundle
    inStP = simInState $ simInP bundle

bindMemory ::
  MT.MemTraceImpl sym ptrW ->
  -- ^ value to rebind
  MT.MemTraceImpl sym ptrW ->
  -- ^ new value
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')  
bindMemory memVar memVal expr = withSym $ \sym -> do
  memVar' <- asVar (MT.memArr memVar)
  liftIO $ rebindExpr sym (Ctx.empty Ctx.:> VarBinding memVar' (MT.memArr memVal)) expr

throwInequivalenceResult ::
  Maybe (InequivalenceResult arch) ->
  EquivM sym arch ()
throwInequivalenceResult Nothing = return ()
throwInequivalenceResult (Just ir) = throwHere $ InequivalentError ir

getInequivalenceResult ::
  forall sym arch.
  HasCallStack =>
  InequivalenceReason ->
  EquivRelation sym arch ->
  SimBundle sym arch ->
  SymGroundEvalFn sym ->
  EquivM sym arch (InequivalenceResult arch)
getInequivalenceResult defaultReason eqRel bundle fn@(SymGroundEvalFn fn')  = do
  ecaseO <- liftIO $ MT.groundExitCase fn' (simOutExit $ simOutO $ bundle)
  ecaseP <- liftIO $ MT.groundExitCase fn' (simOutExit $ simOutP $ bundle)
  
  memdiff <- groundTraceDiff fn eqRel bundle
  regdiff <- MM.traverseRegsWith
    (\r preO -> do
        let
          preP = preRegsP ^. MM.boundValue r
          postO = postRegsO ^. MM.boundValue r
          postP = postRegsP ^. MM.boundValue r
        eqReg <- liftIO $ applyRegEquivRelation (eqRelRegs eqRel) r postO postP
        d <- mkRegisterDiff fn r preO preP postO postP eqReg
        return d
    ) preRegsO
    
  retO <- groundReturnPtr fn (simOutReturn $ simOutO bundle)
  retP <- groundReturnPtr fn (simOutReturn $ simOutP bundle)

  let reason =
        if isMemoryDifferent memdiff then InequivalentMemory
        else if areRegistersDifferent regdiff then InequivalentRegisters
        else defaultReason
  return $ InequivalentResults memdiff (ecaseO, ecaseP) regdiff (retO, retP) reason
  where
    preRegsO = simInRegs $ simInO bundle
    preRegsP = simInRegs $ simInP bundle

    postRegsO = simOutRegs $ simOutO bundle
    postRegsP = simOutRegs $ simOutP bundle
    
isMemoryDifferent :: forall arch. MemTraceDiff arch -> Bool
isMemoryDifferent diffs = any (not . mIsValid) diffs

areRegistersDifferent :: forall arch. MM.RegState (MM.ArchReg arch) (RegisterDiff arch) -> Bool
areRegistersDifferent regs = case MM.traverseRegsWith_ go regs of
  Just () -> False
  Nothing -> True
  where
    go :: forall tp. MM.ArchReg arch tp -> RegisterDiff arch tp -> Maybe ()
    go _ diff = if rPostEquivalent diff then Just () else Nothing

exactEquivalence ::
  SimInput sym arch Original ->
  SimInput sym arch Patched ->
  EquivM sym arch (W4.Pred sym)
exactEquivalence inO inP = withSym $ \sym -> do
  eqRel <- baseEquivRelation
  regsEqs <- liftIO $ zipRegStates (simInRegs inO) (simInRegs inP) (applyRegEquivRelation (eqRelRegs eqRel))
  regsEq <- liftIO $ allPreds sym regsEqs
  memEq <- liftIO $ W4.isEq sym (MT.memArr (simInMem inO)) (MT.memArr (simInMem inP))
  liftIO $ W4.andPred sym regsEq memEq


-- | Add additional patch pairs by pairing up function exit points
discoverPairs ::
  forall sym arch.
  SimBundle sym arch ->
  EquivM sym arch [(BlockTarget arch Original, BlockTarget arch Patched)]
discoverPairs bundle = do
  precond <- exactEquivalence (simInO bundle) (simInP bundle)
  
  blksO <- getSubBlocks (simInBlock $ simInO $ bundle)
  blksP <- getSubBlocks (simInBlock $ simInP $ bundle)

  let
    allCalls = [ (blkO, blkP)
               | blkO <- blksO
               , blkP <- blksP
               , compatibleTargets blkO blkP]

  (oBlocks, pBlocks) <- getBlocks bundle
  
  validTargets <- fmap catMaybes $
    forM allCalls $ \(blktO, blktP) -> do
      matches <- matchesBlockTarget bundle blktO blktP
      check <- withSymIO $ \sym -> W4.andPred sym precond matches
      startedAt <- liftIO TM.getCurrentTime
      checkSatisfiableWithModel "check" check $ \satRes -> do
        finishedBy <- liftIO TM.getCurrentTime
        let
          duration = TM.diffUTCTime finishedBy startedAt
          emit r = emitEvent (PE.DiscoverBlockPair oBlocks pBlocks blktO blktP r duration)
        case satRes of
          W4R.Sat _ -> do
            emit PE.Reachable
            return $ Just $ (blktO, blktP)
          W4R.Unsat _ -> do
            emit PE.Unreachable
            return Nothing
          W4R.Unknown -> do
            emit PE.InconclusiveTarget
            throwHere InconclusiveSAT
  return validTargets

matchesBlockTarget ::
  SimBundle sym arch ->
  BlockTarget arch Original ->
  BlockTarget arch Patched ->
  EquivM sym arch (W4.Pred sym)
matchesBlockTarget bundle blktO blktP = withSymIO $ \sym -> do
  -- true when the resulting IPs call the given block targets
  ptrO <- concreteToLLVM sym (concreteAddress $ targetCall blktO)
  ptrP <- concreteToLLVM sym (concreteAddress $ targetCall blktP)

  eqO <- MT.llvmPtrEq sym ptrO (macawRegValue ipO)
  eqP <- MT.llvmPtrEq sym ptrP (macawRegValue ipP)
  eqCall <- W4.andPred sym eqO eqP

  -- true when the resulting return IPs match the given block return addresses
  targetRetO <- targetReturnPtr sym blktO
  targetRetP <- targetReturnPtr sym blktP

  eqRetO <- liftPartialRel sym (MT.llvmPtrEq sym) retO targetRetO
  eqRetP <- liftPartialRel sym (MT.llvmPtrEq sym) retP targetRetP
  eqRet <-  W4.andPred sym eqRetO eqRetP
  W4.andPred sym eqCall eqRet
  where
    regsO = simOutRegs $ simOutO bundle
    regsP = simOutRegs $ simOutP bundle
    
    ipO = regsO ^. MM.curIP
    ipP = regsP ^. MM.curIP

    retO = simOutReturn $ simOutO bundle
    retP = simOutReturn $ simOutP bundle

liftPartialRel ::
  CB.IsSymInterface sym =>
  sym ->
  (a -> a -> IO (W4.Pred sym)) ->
  W4P.PartExpr (W4.Pred sym) a ->
  W4P.PartExpr (W4.Pred sym) a ->
  IO (W4.Pred sym)
liftPartialRel sym rel (W4P.PE p1 e1) (W4P.PE p2 e2) = do
  eqPreds <- W4.isEq sym p1 p2
  bothConds <- W4.andPred sym p1 p2
  rel' <- rel e1 e2
  justCase <- W4.impliesPred sym bothConds rel'
  W4.andPred sym eqPreds justCase
liftPartialRel sym _ W4P.Unassigned W4P.Unassigned = return $ W4.truePred sym
liftPartialRel sym _ W4P.Unassigned (W4P.PE p2 _) = W4.notPred sym p2
liftPartialRel sym _ (W4P.PE p1 _) W4P.Unassigned = W4.notPred sym p1

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
 
-- | True for a pair of original and patched block targets that represent a valid pair of
-- jumps
compatibleTargets ::
  BlockTarget arch Original ->
  BlockTarget arch Patched ->
  Bool
compatibleTargets blkt1 blkt2 =
  concreteBlockEntry (targetCall blkt1) == concreteBlockEntry (targetCall blkt2) &&
  case (targetReturn blkt1, targetReturn blkt2) of
    (Just blk1, Just blk2) -> concreteBlockEntry blk1 == concreteBlockEntry blk2
    (Nothing, Nothing) -> True
    _ -> False

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



simulate ::
  forall sym arch bin.
  KnownBinary bin =>
  SimInput sym arch bin ->
  EquivM sym arch (W4.Pred sym, SimOutput sym arch bin)
simulate simInput = withBinary @bin $ do
  -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
  CC.SomeCFG cfg <- do
    CC.Some (Compose pbs_) <- lookupBlocks (simInBlock simInput)
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
        killEdges =
          concatMap (backJumps internalAddrs) (pb : pbs) ++
          concatMap (externalTransitions internalAddrs) (pb:pbs)
    fns <- archFuns
    ha <- asks $ handles . envCtx
    liftIO $ MS.mkBlockSliceCFG fns ha (W4L.OtherPos . fromString . show) pb nonTerminal terminal killEdges
  let preRegs = simInRegs simInput
  preRegsAsn <- regStateToAsn preRegs
  archRepr <- archStructRepr
  let regs = CS.assignReg archRepr preRegsAsn CS.emptyRegMap
  globals <- getGlobals simInput
  cres <- evalCFG globals regs cfg
  (asm, postRegs, memTrace, jumpClass, returnIP) <- getGPValueAndTrace cres
  return $ (asm, SimOutput (SimState memTrace postRegs) jumpClass returnIP)

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
checkSatisfiableWithModel desc p k = withSym $ \sym -> withProc $ \proc -> do
  let mkResult r = W4R.traverseSatResult (\r' -> SymGroundEvalFn <$> (liftIO $ mkSafeAsserts sym r')) pure r
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
     MD.ParsedLookupTable _ _ tgts -> toList tgts
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
-- preStableReg ::
--   forall arch tp.
--   ValidArch arch =>
--   ConcreteBlock arch ->
--   MM.ArchReg arch tp ->
--   Bool
-- preStableReg _ reg | Just _ <- testEquality reg (MM.sp_reg @(MM.ArchReg arch)) = True
-- preStableReg blk reg = case concreteBlockEntry blk of
--   BlockEntryInitFunction -> funCallArg reg || funCallStable reg
--   BlockEntryPostFunction -> funCallRet reg || funCallStable reg
--   -- FIXME: not entirely true, needs proper dependency analysis
--   BlockEntryPostArch -> funCallStable reg
--   BlockEntryJump -> True  

mkRegisterDiff ::
  HasCallStack =>
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
  HasCallStack =>
  SymGroundEvalFn sym ->
  MacawRegEntry sym tp ->
  EquivM sym arch (ConcreteValue (MS.ToCrucibleType tp))
concreteValue fn e
  | CLM.LLVMPointerRepr _ <- macawRegRepr e
  , ptr <- macawRegValue e = do
    groundBV fn ptr
concreteValue _ e = throwHere (UnsupportedRegisterType (Some (macawRegRepr e)))

groundReturnPtr ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch))) ->
  EquivM sym arch (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch)))
groundReturnPtr fn (W4P.PE p e) = execGroundFn fn p >>= \case
  True -> Just <$> groundLLVMPointer fn e
  False -> return Nothing
groundReturnPtr _ W4P.Unassigned = return Nothing


groundTraceDiff :: forall sym arch.
  SymGroundEvalFn sym ->
  EquivRelation sym arch ->
  SimBundle sym arch ->
  EquivM sym arch (MemTraceDiff arch)
groundTraceDiff fn eqRel bundle = do
  footprints <- getFootprints bundle
  (S.toList . S.fromList . catMaybes) <$> mapM checkFootprint (S.toList $ footprints)
  where
    memO = simOutMem $ simOutO bundle
    memP = simOutMem $ simOutP bundle
    preMemO = simInMem $ simInO bundle
    preMemP = simInMem $ simInP bundle
    
    checkFootprint ::
      MT.MemFootprint sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (Maybe (MemOpDiff arch))
    checkFootprint (MT.MemFootprint ptr w dir cond) = do
      let repr = MM.BVMemRepr w MM.BigEndian
      stackRegion <- asks envStackRegion
      gstackRegion <- execGroundFn fn stackRegion
      -- "reads" here are simply the memory pre-state
      (oMem, pMem) <- case dir of
            MT.Read -> return $ (preMemO, preMemP)
            MT.Write -> return $ (memO, memP)
      val1 <- withSymIO $ \sym -> MT.readMemArr sym oMem ptr repr
      val2 <- withSymIO $ \sym -> MT.readMemArr sym pMem ptr repr
      cond' <- memOpCondition cond
      execGroundFn fn cond' >>= \case
        True -> do
          gptr <- groundLLVMPointer fn ptr
          let cell = MemCell ptr w
          memRel <- case ptrRegion gptr == gstackRegion of
            True -> return $ eqRelStack eqRel
            False -> return $ eqRelMem eqRel
          isValid <- liftIO $ applyMemEquivRelation memRel cell val1 val2
          groundIsValid <- execGroundFn fn isValid
          op1  <- groundMemOp fn ptr cond' val1
          op2  <- groundMemOp fn ptr cond' val2
          return $ Just $ MemOpDiff { mIsRead = case dir of {MT.Write -> False; _ -> True}
                                    , mOpOriginal = op1
                                    , mOpRewritten = op2
                                    , mIsValid = groundIsValid
                                    , mDesc = ""
                                    }
        False -> return Nothing


groundMemOp ::
  HasCallStack =>
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
  HasCallStack =>
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
  HasCallStack =>
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
    ( W4.Pred sym
    , MM.RegState (MM.ArchReg arch) (MacawRegEntry sym)
    , MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    , MT.ExitClassifyImpl sym
    , CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch)))
    )
getGPValueAndTrace (CS.FinishedResult _ pres) = do
  mem <- asks envMemTraceVar
  eclass <- asks envExitClassVar
  rpv <- asks envReturnIPVar
  asm <- case pres of
    CS.TotalRes _ -> withSym $ \sym -> return $ W4.truePred sym
    CS.PartialRes _ p _ _ -> return p

  case pres ^. CS.partialValue of
    CS.GlobalPair val globs
      | Just mt <- CGS.lookupGlobal mem globs
      , Just jc <- CGS.lookupGlobal eclass globs
      , Just rp <- CGS.lookupGlobal rpv globs -> withValid $ do
        val' <- structToRegState @sym @arch val
        return $ (asm, val', mt, jc, rp)
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
  MM.ArchReg arch tp ->
  EquivM sym arch (MacawRegVar sym tp)
unconstrainedRegister reg = do
  archFs <- archFuns
  let
    symbol = MS.crucGenArchRegName archFs reg
    repr = MM.typeRepr reg
  case repr of
    -- -- | Instruction pointers are exactly the start of the block
    -- MM.BVTypeRepr n | Just Refl <- testEquality reg (MM.ip_reg @(MM.ArchReg arch)) ->
    --   withSymIO $ \sym -> do
    --     regVar <- W4.freshBoundVar sym symbol W4.BaseNatRepr
    --     offVar <- W4.freshBoundVar sym symbol (W4.BaseBVRepr n)
    --     ptr <- concreteToLLVM sym $ concreteAddress blk
    --     return $ MacawRegVar (MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> regVar Ctx.:> offVar)
    -- -- | Stack pointer is in a unique region
    -- MM.BVTypeRepr n | Just Refl <- testEquality reg (MM.sp_reg @(MM.ArchReg arch)) -> do
    --     stackRegion <- asks envStackRegion
    --     withSymIO $ \sym -> do
    --       regVar <- W4.freshBoundVar sym symbol W4.BaseNatRepr
    --       offVar <- W4.freshBoundVar sym symbol (W4.BaseBVRepr n)
    --       let ptr = CLM.LLVMPointer stackRegion (W4.varExpr sym offVar)
    --       return $ MacawRegVar (MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> regVar Ctx.:> offVar)
    MM.BVTypeRepr n -> withSymIO $ \sym -> do
      regVar <- W4.freshBoundVar sym symbol W4.BaseNatRepr
      offVar <- W4.freshBoundVar sym symbol (W4.BaseBVRepr n)
      let ptr = CLM.LLVMPointer (W4.varExpr sym regVar) (W4.varExpr sym offVar)
      return $ MacawRegVar (MacawRegEntry (MS.typeToCrucible repr) ptr) (Ctx.empty Ctx.:> regVar Ctx.:> offVar)
    _ -> throwHere $ UnsupportedRegisterType (Some (MS.typeToCrucible repr))


freshRegEntry ::
  MacawRegEntry sym tp ->
  EquivM sym arch (MacawRegEntry sym tp)
freshRegEntry entry = withSym $ \sym -> case macawRegRepr entry of
  CLM.LLVMPointerRepr w -> liftIO $ do
    reg <- W4.freshConstant sym W4.emptySymbol W4.BaseNatRepr
    off <- W4.freshConstant sym W4.emptySymbol (W4.BaseBVRepr w)
    let ptr = CLM.LLVMPointer reg off
    return $ MacawRegEntry (macawRegRepr entry) ptr
  repr -> throwHere $ UnsupportedRegisterType $ Some repr

lookupBlocks ::
  forall sym arch bin.
  KnownBinary bin =>
  ConcreteBlock arch bin ->
  EquivM sym arch (CC.Some (Compose [] (MD.ParsedBlock arch)))
lookupBlocks b = do
  binCtx <- getBinCtx @bin
  let pfm = parsedFunctionMap binCtx
  case M.assocs $ M.unions $ fmap snd $ IM.lookupLE i pfm of
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


targetReturnPtr ::
  ValidSym sym =>
  ValidArch arch =>
  sym ->
  BlockTarget arch bin ->
  IO (CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch))))
targetReturnPtr sym blkt | Just blk <- targetReturn blkt = do
  ptr <- concreteToLLVM sym (concreteAddress blk)
  return $ W4P.justPartExpr sym ptr
targetReturnPtr sym _ = return $ W4P.maybePartExpr sym Nothing


-- | From the given starting point, find all of the accessible
-- blocks
getSubBlocks ::
  forall sym arch bin.
  KnownBinary bin =>
  ConcreteBlock arch bin ->
  EquivM sym arch [BlockTarget arch bin]
getSubBlocks b = do
  pfm <- parsedFunctionMap <$> getBinCtx @bin
  case M.assocs $ M.unions $ fmap snd $ IM.lookupLE i pfm of
    [(_, CC.Some (ParsedBlockMap pbm))] -> do
      let pbs = concat $ IM.elems $ IM.intersecting pbm i
      concat <$> mapM (concreteValidJumpTargets pbs) pbs
    blks -> throwHere $ NoUniqueFunctionOwner i (fst <$> blks)
  where
  start@(ConcreteAddress saddr) = concreteAddress b
  end = ConcreteAddress (MM.MemAddr (MM.addrBase saddr) maxBound)
  i = IM.OpenInterval start end

concreteValidJumpTargets ::
  forall bin sym arch ids.
  KnownBinary bin =>
  ValidArch arch =>
  [MD.ParsedBlock arch ids] ->
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch bin]
concreteValidJumpTargets allPbs pb = do
  targets <- concreteJumpTargets pb
  thisAddr <- segOffToAddr (MD.pblockAddr pb)
  addrs <- mapM (segOffToAddr . MD.pblockAddr) allPbs
  let
    isTargetExternal btgt = not ((concreteAddress (targetCall btgt)) `elem` addrs)
    isTargetBackJump btgt = (concreteAddress (targetCall btgt)) < thisAddr
    isTargetArch btgt = concreteBlockEntry (targetCall btgt) == BlockEntryPostArch

    isTargetValid btgt = isTargetArch btgt || isTargetExternal btgt || isTargetBackJump btgt
  return $ filter isTargetValid targets

mkConcreteBlock ::
  KnownBinary bin =>
  BlockEntryKind arch ->
  ConcreteAddress arch ->
  ConcreteBlock arch bin
mkConcreteBlock k a = ConcreteBlock a k W4.knownRepr

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
  forall bin sym arch ids.
  KnownBinary bin =>
  ValidArch arch =>
  MD.ParsedBlock arch ids ->
  EquivM sym arch [BlockTarget arch bin]
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
  MD.ParsedArchTermStmt _ st ret -> do
    ret_blk <- fmap (mkConcreteBlock BlockEntryPostArch) <$> mapM segOffToAddr ret
    return $ [ BlockTarget (mkConcreteBlock BlockEntryPostArch next) ret_blk
             | next <- (concreteNextIPs st) ]
  _ -> return []
  where
    go ::
      [ConcreteAddress arch] ->
      Maybe (MM.ArchSegmentOff arch) ->
      EquivM sym arch [BlockTarget arch bin]
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
  open <- gets (M.keys . stOpenTriples)
  failures <- gets (M.keys . stFailedTriples)
  successes <- gets (M.keys  . stProvenTriples)
  return $ open ++ successes ++ failures

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
    alternatives <- flipZipWithM ips ips' $ \ip ip' -> MT.llvmPtrEq sym ipArg ip <&&> MT.llvmPtrEq sym ipArg' ip'
    anyAlternative <- foldM (W4.orPred sym) (W4.falsePred sym) alternatives

    tableEntries <- forM ips $ \ip -> MT.llvmPtrEq sym ipArg ip
    isInTable <- foldM (W4.orPred sym) (W4.falsePred sym) tableEntries

    plainEq <- MT.llvmPtrEq sym ipArg ipArg'
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
