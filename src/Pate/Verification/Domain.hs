{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification.Domain (
    allRegistersDomain
  , guessEquivalenceDomain
  , equateInitialStates
  , universalDomain
  , universalDomainSpec
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as CMR
import           Data.Functor.Const ( Const(..) )
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           GHC.Stack ( HasCallStack )
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.Symbol as WS

import qualified Data.Macaw.CFG as MM
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT


import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Event as PE
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Register as PRe
import qualified Pate.SimState as PSi
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Verification.Simplify as PVS
import qualified Pate.Verification.Validity as PVV
import qualified What4.ExprHelpers as WEH

freshRegEntry ::
  PB.KnownBinary bin =>
  PB.ConcreteBlock arch bin ->
  MM.ArchReg arch tp ->
  PSR.MacawRegEntry sym tp ->
  EquivM sym arch (W4.Pred sym, PSR.MacawRegEntry sym tp)
freshRegEntry initBlk r entry = withSym $ \sym -> do
  fresh <- case PSR.macawRegRepr entry of
    CLM.LLVMPointerRepr w -> liftIO $ do
      ptr <- WEH.freshPtr sym (PC.showF r) w
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) ptr
    CT.BoolRepr -> liftIO $ do
      b <- W4.freshConstant sym (WS.safeSymbol (PC.showF r)) WT.BaseBoolRepr
      return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) b
    CT.StructRepr Ctx.Empty -> return $ PSR.MacawRegEntry (PSR.macawRegRepr entry) Ctx.Empty
    repr -> throwHere $ PEE.UnsupportedRegisterType $ Some repr
  isValid <- PVV.validRegister (Just initBlk) fresh r
  isValid_pred <- liftIO $ PSi.getAssumedPred sym isValid
  return (isValid_pred, fresh)

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
    memO = PSi.simInMem $ PSi.simInO bundle
    memP = PSi.simInMem $ PSi.simInP bundle

bindMemory ::
  -- | value to rebind
  MT.MemTraceImpl sym ptrW ->
  -- | new value
  MT.MemTraceImpl sym ptrW ->
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')
bindMemory memVar memVal expr = withSym $ \sym -> do
  liftIO $ PSi.rebindExpr sym (Ctx.empty Ctx.:> WEH.VarBinding (MT.memArr memVar) (MT.memArr memVal)) expr

bindMacawReg ::
  -- | value to rebind
  PSR.MacawRegEntry sym tp ->
  -- | new value
  PSR.MacawRegEntry sym tp ->
  W4.SymExpr sym tp' ->
  EquivM sym arch (W4.SymExpr sym tp')
bindMacawReg var val expr = withValid $ withSym $ \sym -> do
  bind <- liftIO $ PSi.macawRegBinding sym var val
  liftIO $ PSi.rebindWithFrame sym bind expr

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

getIsBoundFilter' ::
  W4.SymExpr sym tp ->
  EquivM sym arch (WEH.ExprFilter sym)
getIsBoundFilter' e = withValid $ liftIO $ WEH.getIsBoundFilter e

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
      PVS.simplifyPred pathCond

  -- we take the entire reads set of the block and then filter it according
  -- to the polarity of the postcondition predicate
  result <- PEM.mapMemPredPar cells $ \cell p -> maybeEqualAt bundle cell p >>= \case
    True -> ifConfig (not . PC.cfgComputeEquivalenceFrames) (Par.present $ return polarity) $ do
      let repr = MM.BVMemRepr (PMC.cellWidth cell) (PMC.cellEndian cell)
      -- clobber the "patched" memory at exactly this cell
      CLM.LLVMPointer _ freshP <- liftIO $ WEH.freshPtrBytes sym "MemCell_guessMemoryDomain" (PMC.cellWidth cell)

      memP'' <- liftIO $ MT.writeMemArr sym memP (PMC.cellPtr cell) repr freshP
      eqMemP <- liftIO $ W4.isEq sym (MT.memArr memP') (MT.memArr memP'')

      -- see if we can prove that the goal is independent of this clobbering
      heuristicTimeout <- CMR.asks (PC.cfgHeuristicTimeout . envConfig)
      withAssumption_ (liftIO $ WEH.allPreds sym [p, eqMemP, goal]) $ do
        result <- isPredTruePar' heuristicTimeout goal'
        Par.forFuture result $ \case
          True -> liftIO $ W4.baseTypeIte sym polarity (W4.falsePred sym) p
          False -> liftIO $ W4.baseTypeIte sym polarity p (W4.falsePred sym)
    False -> Par.present $ liftIO $ W4.notPred sym polarity
  Par.joinFuture (result :: Par.Future (PEM.MemPred sym arch))
  where
    polarity = PEM.memPredPolarity memPred
    memP = PSi.simInMem $ PSi.simInP bundle

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

equateRegisters ::
  M.Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  SimBundle sym arch ->
  EquivM sym arch (PSi.AssumptionFrame sym)
equateRegisters regRel bundle = withValid $ withSym $ \sym -> do
  PA.SomeValidArch _ _ hdr <- CMR.asks envValidArch
  fmap (mconcat) $ PRe.zipRegStates (PSi.simRegs inStO) (PSi.simRegs inStP) $ \r vO vP -> case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
    PRe.RegIP -> return mempty
    _ -> case M.lookup (Some r) regRel of
      Just cond | Just True <- W4.asConstantPred cond -> liftIO $ PSi.macawRegBinding sym vO vP
      _ -> return mempty
  where
    inStO = PSi.simInState $ PSi.simInO bundle
    inStP = PSi.simInState $ PSi.simInP bundle

equateInitialMemory :: SimBundle sym arch -> EquivM sym arch (PSi.AssumptionFrame sym)
equateInitialMemory bundle =
  return $ PSi.exprBinding (MT.memArr (PSi.simInMem $ PSi.simInO bundle)) (MT.memArr (PSi.simInMem $ PSi.simInP bundle))

equateInitialStates :: SimBundle sym arch -> EquivM sym arch (PSi.AssumptionFrame sym)
equateInitialStates bundle = do
  regDomain <- allRegistersDomain
  eqRegs <- equateRegisters regDomain bundle
  eqMem <- equateInitialMemory bundle
  return $ eqRegs <> eqMem


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
  PA.SomeValidArch _ _ hdr <- CMR.asks envValidArch
  traceBundle bundle "Entering guessEquivalenceDomain"
  WEH.ExprFilter isBoundInGoal <- getIsBoundFilter' goal
  eqRel <- CMR.asks envBaseEquiv
  result <- PRe.zipRegStatesPar (PSi.simRegs inStO) (PSi.simRegs inStP) $ \r vO vP -> do
      isInO <- liftFilterMacaw isBoundInGoal vO
      isInP <- liftFilterMacaw isBoundInGoal vP
      let
        include = Par.present $ return $ Just (Some r, W4.truePred sym)
        exclude :: EquivM sym arch (Par.Future (Maybe (Some (MM.ArchReg arch), W4B.Expr t W4.BaseBoolType)))
        exclude = Par.present $ return Nothing
      case PRe.registerCase hdr (PSR.macawRegRepr vO) r of
        -- we have concrete values for the pre-IP and dedicated registers, so we don't need
        -- to include them in the pre-domain
        --
        -- NOTE: We could extend this to make the handling of dedicated
        -- registers a parameter via the HasDedicatedRegister type
        PRe.RegIP -> exclude
        PRe.RegDedicated _ -> exclude
        -- this requires some more careful consideration. We don't want to include
        -- the stack pointer in computed domains, because this unreasonably
        -- restricts preceding blocks from having different numbers of stack allocations.
        -- However our equivalence relation is not strong enough to handle mismatches in
        -- values written to memory that happen to be stack addresses, if those
        -- addresses were computed with different stack bases.
        PRe.RegSP -> ifConfig PC.cfgComputeEquivalenceFrames exclude include
        _ | isInO || isInP ->
          ifConfig (not . PC.cfgComputeEquivalenceFrames) include $ do
            (isFreshValid, freshO) <- freshRegEntry (PPa.pPatched $ PSi.simPair bundle) r vO

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
  stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
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
  let stackEq = liftIO $ PEq.memPredPre sym (PEq.memEqAtRegion sym stackRegion) inO inP (PEq.eqRelStack eqRel) stackDom
  memDom <- withAssumption_ stackEq $ do
    guessMemoryDomain bundle_regsEq goal_regsEq (memP', goal') (PES.predMem postcond_regsEq) isNotStackCell

  blocks <- PD.getBlocks $ PSi.simPair bundle

  emitEvent (PE.ComputedPrecondition blocks)
  return $ PES.StatePred
    { PES.predRegs = regsDom
    , PES.predStack = stackDom
    , PES.predMem = memDom
    }
  where
    memP = PSi.simInMem $ PSi.simInP bundle
    inO = PSi.simInO bundle
    inP = PSi.simInP bundle
    inStO = PSi.simInState $ PSi.simInO bundle
    inStP = PSi.simInState $ PSi.simInP bundle

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
  EquivM sym arch (PEq.StatePredSpec sym arch)
universalDomainSpec = withFreshVars $ \stO stP ->
  withAssumptionFrame (PVV.validInitState Nothing stO stP) $
  universalDomain
