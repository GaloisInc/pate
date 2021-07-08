{-|
Module           : Pate.Proof.Operations
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Functions for creating and operating with equivalence proofs
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Pate.Proof.Operations
  ( simBundleToSlice
  , noTransition
  , emptyDomain
  , statePredToDomain
  , statePredToPreDomain
  , statePredToPostDomain
  , blockSliceBlocks
  , proofResult
    -- lazy proofs
  , LazyProof(..)
  , LazyProofApp
  , lazyProofApp
  , lazyProof
  , joinLazyProof
  , asLazyProof
  , forkProof
  , proofNonceExpr
  , lazyProofFinal
  , lazyProofEvent
  , lazyProofEvent_
  , forkProofFinal
  , forkProofEvent_
  , forkProofEvent
  , flattenDomainConditions
  , wrapFutureNonceApp
  , asFutureNonceApp
  ) where

import qualified Control.Monad.Reader as CMR
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.IO.Unlift as IO

import           Data.Functor.Const
import           Data.Map ( Map )
import qualified Data.Map as Map

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS

import qualified Lang.Crucible.Simulator as CS

import qualified What4.Interface as W4

import qualified Pate.Arch as PA
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence as PE
import qualified Pate.Equivalence.MemPred as PEM
import qualified Pate.Equivalence.StatePred as PES
import qualified Pate.Event as PE
import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import           Pate.Monad
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Register as PR
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Types as PT

-- | Convert the result of symbolic execution into a structured slice
-- representation
simBundleToSlice ::
  PS.SimBundle sym arch ->
  EquivM sym arch (PF.BlockSliceTransition (PFI.ProofSym sym arch))
simBundleToSlice bundle = withSym $ \sym -> do
  let
    ecaseO = PS.simOutBlockEnd $ PS.simOutO $ bundle
    ecaseP = PS.simOutBlockEnd $ PS.simOutP $ bundle
  footprints <- getFootprints bundle
  memReads <- PEM.memPredToList <$> (liftIO $ PEM.footPrintsToPred sym footprints (W4.truePred sym))
  memWrites <- PEM.memPredToList <$> (liftIO $ PEM.footPrintsToPred sym footprints (W4.falsePred sym))

  preMem <- MapF.fromList <$> mapM (memCellToOp initState) memReads
  postMem <- MapF.fromList <$> mapM (memCellToOp finState) memWrites

  preRegs <- PR.zipWithRegStatesM (PS.simInRegs $ PS.simInO bundle) (PS.simInRegs $ PS.simInP bundle) getReg
  postRegs <- PR.zipWithRegStatesM (PS.simOutRegs $ PS.simOutO bundle) (PS.simOutRegs $ PS.simOutP bundle) getReg
  
  let
    preState = PF.BlockSliceState preMem preRegs
    postState = PF.BlockSliceState postMem postRegs
  return $ PF.BlockSliceTransition preState postState (PPa.PatchPairC ecaseO ecaseP)
  where
    initState = TF.fmapF PS.simInState (PS.simIn bundle)
    finState = TF.fmapF PS.simOutState (PS.simOut bundle)

    getReg ::
      MM.ArchReg arch tp ->
      PSR.MacawRegEntry sym tp ->
      PSR.MacawRegEntry sym tp ->
      EquivM sym arch (PF.BlockSliceRegOp (PFI.ProofSym sym arch) tp)
    getReg reg valO valP = do
      eqRel <- CMR.asks envBaseEquiv
      isEquiv <- liftIO $ PE.applyRegEquivRelation (PE.eqRelRegs eqRel) reg valO valP
      return $ PF.BlockSliceRegOp
        (PPa.PatchPairC valO valP)
        (PSR.macawRegRepr valO)
        isEquiv
    
    memCellToOp ::
      PPa.PatchPair (PS.SimState sym arch) ->
      (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      EquivM sym arch (MapF.Pair (PMC.MemCell sym arch) (PF.BlockSliceMemOp (PFI.ProofSym sym arch)))
    memCellToOp (PPa.PatchPair stO stP) (Some cell, cond) = withSym $ \sym -> do
      valO <- liftIO $ PMC.readMemCell sym (PS.simMem stO) cell
      valP <- liftIO $ PMC.readMemCell sym (PS.simMem stP) cell
      eqRel <- CMR.asks envBaseEquiv      
      isValidStack <- liftIO $ PE.applyMemEquivRelation (PE.eqRelStack eqRel) cell valO valP
      isValidGlobalMem <- liftIO $ PE.applyMemEquivRelation (PE.eqRelMem eqRel) cell valO valP
      isEquiv <- liftIO $ W4.andPred sym isValidStack isValidGlobalMem
      return $ MapF.Pair cell $ PF.BlockSliceMemOp
        { PF.slMemOpValues = PPa.PatchPairC (PFI.SymBV valO) (PFI.SymBV valP)
        , PF.slMemOpEquiv = isEquiv
        , PF.slMemOpCond = cond
        }

-- | Compute a single predicate representing the conjunction of all conditions
-- in the domain. Conditions in negative polarity domains are negated.
flattenDomainConditions ::
  forall sym arch.
  PF.ProofExpr (PFI.ProofSym sym arch) PF.ProofDomainType ->
  EquivM sym arch (W4.Pred sym)
flattenDomainConditions domApp = withSym $ \sym -> do
  reg_cond <- MapF.foldrMWithKey (\_ (Const p) p' -> liftIO $ W4.andPred sym p p') (W4.truePred sym) (MM.regStateMap $ PF.prfDomainRegisters dom)
  stack_cond <- MapF.foldrMWithKey (go stack_pol) reg_cond (PF.prfMemoryDomain $ PF.prfDomainStackMemory dom)
  MapF.foldrMWithKey (go glob_pol) stack_cond (PF.prfMemoryDomain $ PF.prfDomainGlobalMemory dom)
  where
    dom = PF.unApp domApp
    stack_pol = PF.prfMemoryDomainPolarity $ PF.prfDomainStackMemory dom
    glob_pol = PF.prfMemoryDomainPolarity $ PF.prfDomainGlobalMemory dom
    go ::
      -- | polarity
      W4.Pred sym ->
      PMC.MemCell sym arch w ->
      -- | condition
      Const (W4.Pred sym) w ->
      -- | accumulator
      W4.Pred sym ->
      EquivM sym arch (W4.Pred sym)
    go pol _cell (Const p) acc = withSym $ \sym -> do
      p' <- liftIO $ W4.isEq sym pol p
      liftIO $ W4.andPred sym p' acc
      

blockSliceBlocks :: PFI.ProofSymExpr sym arch PF.ProofBlockSliceType -> PPa.BlockPair arch
blockSliceBlocks prf = PF.prfTripleBlocks $ PF.unApp (PF.prfBlockSliceTriple (PF.unApp prf))

-- | Compute an aggregate verification condition: preferring an inequivalence result
-- if it exists, but potentially yielding an 'PF.Unverified' result.
proofResult ::
  forall prf tp a.
  a ~ (PF.ProofCounterExample prf, PF.ProofCondition prf) =>
  PF.ProofExpr prf tp ->
  PF.VerificationStatus a
proofResult e = foldr merge PF.VerificationSuccess statuses
  where
    merge ::
      PF.VerificationStatus a ->
      PF.VerificationStatus a ->
      PF.VerificationStatus a
    merge (PF.VerificationFail ce) _ = PF.VerificationFail ce
    merge _ (PF.VerificationFail ce) = PF.VerificationFail ce
    merge PF.Unverified _ = PF.Unverified
    merge _ PF.Unverified = PF.Unverified
    merge PF.VerificationSkipped a = a
    merge a PF.VerificationSkipped = a
    merge PF.VerificationSuccess PF.VerificationSuccess = PF.VerificationSuccess
    
    statuses :: [PF.VerificationStatus a]
    statuses = PF.collectProofExpr go e

    go :: PF.ProofExpr prf tp' -> [PF.VerificationStatus a]
    go (PF.ProofExpr (PF.ProofStatus st)) = [st]
    go _ = []

noTransition ::
  PPa.PatchPair (PS.SimInput sym arch) ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch (PF.BlockSliceTransition (PFI.ProofSym sym arch))
noTransition stIn blockEnd = do
  let
    stOut = TF.fmapF (\st -> PS.SimOutput (PS.simInState st) blockEnd) stIn
    bundle = PS.SimBundle stIn stOut
  simBundleToSlice bundle
  

-- these are shims that we can potentially eliminate by unifying
-- the corresponding types

statePredToDomain ::
  PPa.PatchPair (PS.SimState sym arch) ->
  PES.StatePred sym arch ->
  EquivM sym arch (PFI.SymDomain sym arch)
statePredToDomain states stPred = withSym $ \sym -> do
  dom <-
    PF.ProofDomain
      <$> (return $ predRegsToDomain sym $ PES.predRegs stPred)
      <*> (flattenToStackRegion $ memPredToDomain $ PES.predStack stPred)
      <*> (return $ memPredToDomain $ PES.predMem stPred)
      <*> (return states)
  return $ PF.ProofExpr dom

flattenToStackRegion ::
  PF.ProofMemoryDomain (PFI.ProofSym sym arch) ->
  EquivM sym arch (PF.ProofMemoryDomain (PFI.ProofSym sym arch))
flattenToStackRegion dom = do
  stackRegion <- CMR.asks envStackRegion
  let
    dom' = map (\(MapF.Pair cell p) -> MapF.Pair (PMC.setMemCellRegion stackRegion cell) p) (MapF.toList (PF.prfMemoryDomain dom))
  return $ dom { PF.prfMemoryDomain = MapF.fromList dom' }


predRegsToDomain ::
  forall arch sym.
  PA.ValidArch arch =>
  PT.ValidSym sym =>
  sym ->
  Map (Some (MM.ArchReg arch)) (W4.Pred sym) ->
  MM.RegState (MM.ArchReg arch) (Const (W4.Pred sym))
predRegsToDomain sym regs = MM.mkRegState go
  where
    go :: MM.ArchReg arch tp -> Const (W4.Pred sym) tp
    go r = case Map.lookup (Some r) regs of
      Just p -> Const p
      Nothing -> Const (W4.falsePred sym)

-- TODO: flatten 'MemCells' to avoid rebuilding this map
memPredToDomain ::
  PT.ValidSym sym =>
  PEM.MemPred sym arch ->
  PF.ProofMemoryDomain (PFI.ProofSym sym arch)
memPredToDomain memPred =
  PF.ProofMemoryDomain
    { PF.prfMemoryDomain = MapF.fromList $ map go $ PEM.memPredToList memPred
    , PF.prfMemoryDomainPolarity = PEM.memPredPolarity memPred
    }
  where
    go :: (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      MapF.Pair (PMC.MemCell sym arch) (Const (W4.Pred sym))
    go (Some cell, p) = MapF.Pair cell (Const p)

statePredToPreDomain ::
  PS.SimBundle sym arch ->
  PES.StatePred sym arch ->
  EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
statePredToPreDomain bundle stPred = proofNonceExpr $ do
  PF.appDomain <$> statePredToDomain states stPred
  where
    states = TF.fmapF PS.simInState $ PS.simIn bundle

statePredToPostDomain ::
  PE.StatePredSpec sym arch ->
  EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
statePredToPostDomain stPredSpec = proofNonceExpr $ do
  let
    states = TF.fmapF PS.simVarState $ PS.specVars stPredSpec
    stPred = PS.specBody stPredSpec
  PF.appDomain <$> statePredToDomain states stPred


emptyDomain :: EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
emptyDomain = proofNonceExpr $ withSym $ \sym -> fmap PS.specBody $ withFreshVars $ \stO stP -> do
  dom <- PF.appDomain <$> statePredToDomain (PPa.PatchPair stO stP) (PES.statePredFalse sym)
  return $ (W4.truePred sym, dom)

proofNonceExpr ::
  EquivM sym arch (PFI.ProofSymNonceApp sym arch tp) ->
  EquivM sym arch (PFI.ProofSymNonceExpr sym arch tp)
proofNonceExpr f = do
  parentNonce <- CMR.asks envParentNonce
  withProofNonce $ \nonce -> do
    app <- f
    return $ PF.ProofNonceExpr nonce parentNonce app

------------------------------
-- Future proofs

-- | A lazy proof is a tree of lazy proofs, annotated with nonces
data LazyProof sym arch tp where
  LazyProof ::
    {
      lazyProofNonce :: PF.ProofNonce (PFI.ProofSym sym arch) tp
    , lazyProofParent :: Some (PF.ProofNonce (PFI.ProofSym sym arch))
    , lazyProofBody :: LazyProofBody sym arch tp
    , lazyProofFinalize :: PFI.ProofSymNonceExpr sym arch tp -> IO ()
    } -> LazyProof sym arch tp


-- | Lazy proof bodies are either sub-trees of lazy proofs, or future values
-- of completed proofs
data LazyProofBody sym arch tp where
  LazyProofBodyApp :: LazyProofApp sym arch tp -> LazyProofBody sym arch tp
  LazyProofBodyFuture :: Par.Future (PFI.ProofSymNonceApp sym arch tp) -> LazyProofBody sym arch tp

type LazyProofApp sym arch = PF.ProofApp (PFI.ProofSym sym arch) (LazyProof sym arch)

instance (PA.ValidArch arch, ValidSym sym) => PEM.ExprMappable sym (LazyProofBody sym arch tp) where
  mapExpr sym f (LazyProofBodyApp app) = LazyProofBodyApp <$> PEM.mapExpr sym f app
  mapExpr sym f (LazyProofBodyFuture future) = LazyProofBodyFuture <$> PEM.mapExpr sym f future

instance (PA.ValidArch arch, ValidSym sym) => PEM.ExprMappable sym (LazyProof sym arch tp) where
  mapExpr sym f (LazyProof a1 a2 v fin) = do
    v' <- PEM.mapExpr sym f v
    return $ LazyProof a1 a2 v' fin

mkLazyProof ::
  EquivM sym arch (a, LazyProofBody sym arch tp) ->
  (PFI.ProofSymNonceExpr sym arch tp -> EquivM sym arch ()) ->
  EquivM sym arch (a, LazyProof sym arch tp)
mkLazyProof f fin = do
  parentNonce <- CMR.asks envParentNonce
  withProofNonce $ \nonce -> startTimer $ do
    (a, body) <- f
    -- capture the monadic context here when evaluating the final action
    IO.withRunInIO $ \runInIO ->
      return $ (a, LazyProof nonce parentNonce body (\e -> runInIO $ fin e))  

-- | Create a lazy proof node by evaluating the given function immediately
lazyProof ::
  EquivM sym arch (LazyProofApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
lazyProof f = snd <$> lazyProofFinal (f >>= \a -> (return ((), a))) (\_ -> return ())


lazyProofApp ::
  LazyProofApp sym arch tp ->
  EquivM sym arch (LazyProof sym arch tp)
lazyProofApp v = lazyProof (return v)

-- | Same as 'lazyProof' but with an additional action that runs when the
-- lazy proof is evaluated.
lazyProofFinal ::
  EquivM sym arch (a, LazyProofApp sym arch tp) ->
  (PFI.ProofSymNonceExpr sym arch tp -> EquivM sym arch ()) ->
  EquivM sym arch (a, LazyProof sym arch tp)
lazyProofFinal f fin = mkLazyProof (f >>= \(a, app) -> return (a, LazyProofBodyApp app)) fin

-- | Make a proof event on the current thread
--
-- Despite the name, this does not lazily compute anything
lazyProofEvent ::
  PPa.BlockPair arch ->
  EquivM sym arch (a, LazyProofApp sym arch tp) ->
  EquivM sym arch (a, LazyProof sym arch tp)
lazyProofEvent ppair f = lazyProofFinal f $ \e -> do
  blocks <- PD.getBlocks ppair 
  vsym <- CMR.asks envValidSym
  emitEvent (PE.ProofIntermediate blocks (PFI.SomeProofSym vsym e))

lazyProofEvent_ ::
  PPa.BlockPair arch ->
  EquivM sym arch (LazyProofApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
lazyProofEvent_ ppair f = snd <$> lazyProofEvent ppair (f >>= \a -> return ((), a))


asLazyProof ::
  PFI.ProofSymNonceExpr sym arch tp -> LazyProof sym arch tp
asLazyProof e =
  LazyProof (PF.prfNonce e) (PF.prfParent e) (asLazyProofApp (PF.prfNonceBody e)) (\_ -> return ())

asLazyProofApp ::
  PFI.ProofSymNonceApp sym arch tp -> LazyProofBody sym arch tp
asLazyProofApp app = LazyProofBodyApp $ PF.mapProofApp asLazyProof app

-- | Create a lazy proof node by fully evaluating the given lazy proof app in a
-- separate thread
forkProof ::
  EquivM sym arch (LazyProofApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
forkProof f = snd <$> forkProofFinal (f >>= \app -> return ((), app)) (\_ -> return ())

-- | Same as 'forkProof' but with an additional action that runs after the
-- proof has completed.
forkProofFinal ::
  forall sym arch tp a.
  EquivM sym arch (a, LazyProofApp sym arch tp) ->
  (PFI.ProofSymNonceExpr sym arch tp -> EquivM sym arch ()) ->
  EquivM sym arch (Par.Future a, LazyProof sym arch tp)
forkProofFinal f fin = mkLazyProof go fin
  where
    go :: EquivM sym arch (Par.Future a, LazyProofBody sym arch tp)
    go = do
      future <- Par.promise (f >>= \(a, app) -> (,) <$> pure a <*> joinLazyProofApp app)
      futurePrf <- Par.forFuture future (\(_,prf) -> return prf)
      futureRes <- Par.forFuture future (\(a,_) -> return a)
      return (futureRes, LazyProofBodyFuture futurePrf)

forkProofEvent_ ::
  PPa.BlockPair arch ->
  EquivM sym arch (LazyProofApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
forkProofEvent_ ppair f = snd <$> forkProofEvent ppair (f >>= \app -> return ((), app)) 

forkProofEvent ::
  PPa.BlockPair arch ->
  EquivM sym arch (a, LazyProofApp sym arch tp) ->
  EquivM sym arch (Par.Future a, LazyProof sym arch tp)
forkProofEvent ppair f = forkProofFinal f $ \e -> do
  blocks <- PD.getBlocks ppair 
  vsym <- CMR.asks envValidSym
  emitEvent (PE.ProofIntermediate blocks (PFI.SomeProofSym vsym e))

joinLazyProofApp :: LazyProofApp sym arch tp -> EquivM sym arch (PFI.ProofSymNonceApp sym arch tp)
joinLazyProofApp = PF.traverseProofApp joinLazyProof

joinLazyProof :: LazyProof sym arch tp -> EquivM sym arch (PFI.ProofSymNonceExpr sym arch tp)
joinLazyProof prf = withValid $ do
  app <- case lazyProofBody prf of
    LazyProofBodyApp app -> joinLazyProofApp app
    LazyProofBodyFuture future -> Par.joinFuture future
  let nonce_prf = PF.ProofNonceExpr (lazyProofNonce prf) (lazyProofParent prf) app
  liftIO $ lazyProofFinalize prf nonce_prf
  return nonce_prf

asFutureNonceApp ::
  LazyProof sym arch tp ->
  EquivM sym arch (Par.Future (PFI.ProofSymNonceApp sym arch tp))
asFutureNonceApp prf = case lazyProofBody prf of
  LazyProofBodyFuture future -> return future
  LazyProofBodyApp app -> Par.present $ joinLazyProofApp app

wrapFutureNonceApp ::
  Par.Future (PFI.ProofSymNonceApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
wrapFutureNonceApp future = snd <$> mkLazyProof (return ((), LazyProofBodyFuture future)) (\_ -> return ())
