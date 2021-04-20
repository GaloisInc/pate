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
  , lazyProofFinal
  , lazyProofEvent
  , lazyProofEvent_
  , forkProofFinal
  , forkProofEvent
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

import qualified Pate.ExprMappable as PEM
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as PMT
import           Pate.Monad
import qualified Pate.Discovery as PD
import qualified Pate.Equivalence as PE
import qualified Pate.Event as PE
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT
import qualified Pate.Parallel as Par
import qualified Pate.Arch as PA

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
  memReads <- PE.memPredToList <$> (liftIO $ PE.footPrintsToPred sym footprints (W4.truePred sym))
  memWrites <- PE.memPredToList <$> (liftIO $ PE.footPrintsToPred sym footprints (W4.falsePred sym))

  preMem <- MapF.fromList <$> mapM (memCellToOp initState) memReads
  postMem <- MapF.fromList <$> mapM (memCellToOp finState) memWrites

  preRegs <- PT.zipWithRegStatesM (PS.simInRegs $ PS.simInO bundle) (PS.simInRegs $ PS.simInP bundle) getReg
  postRegs <- PT.zipWithRegStatesM (PS.simOutRegs $ PS.simOutO bundle) (PS.simOutRegs $ PS.simOutP bundle) getReg
  
  let
    preState = PF.BlockSliceState preMem preRegs
    postState = PF.BlockSliceState postMem postRegs
  return $ PF.BlockSliceTransition preState postState (PT.PatchPairC ecaseO ecaseP)
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
        (PT.PatchPairC valO valP)
        (PSR.macawRegRepr valO)
        isEquiv
    
    memCellToOp ::
      PT.PatchPair (PS.SimState sym arch) -> 
      (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      EquivM sym arch (MapF.Pair (PMC.MemCell sym arch) (PF.BlockSliceMemOp (PFI.ProofSym sym arch)))
    memCellToOp (PT.PatchPair stO stP) (Some cell, cond) = withSym $ \sym -> do
      undef <- liftIO $ PMT.mkUndefinedPtrOps sym
      valO <- liftIO $ PMC.readMemCell sym undef (PS.simMem stO) cell
      valP <- liftIO $ PMC.readMemCell sym undef (PS.simMem stP) cell
      eqRel <- CMR.asks envBaseEquiv      
      isValidStack <- liftIO $ PE.applyMemEquivRelation (PE.eqRelStack eqRel) cell valO valP
      isValidGlobalMem <- liftIO $ PE.applyMemEquivRelation (PE.eqRelMem eqRel) cell valO valP
      isEquiv <- liftIO $ W4.andPred sym isValidStack isValidGlobalMem
      return $ MapF.Pair cell $ PF.BlockSliceMemOp
        { PF.slMemOpValues = PT.PatchPairC (PFI.SymBV valO) (PFI.SymBV valP)
        , PF.slMemOpEquiv = isEquiv
        , PF.slMemOpCond = cond
        }

blockSliceBlocks :: PFI.ProofSymExpr sym arch PF.ProofBlockSliceType -> PT.BlockPair arch
blockSliceBlocks prf = PF.prfTripleBlocks $ PF.unApp (PF.prfBlockSliceTriple (PF.unApp prf))

-- | Find an inequivalence result in the proof if it exists. A 'Nothing' result indicates
-- that the proof was successful.
proofResult ::
  forall sym arch tp.
  PFI.ProofSymExpr sym arch tp ->
  Maybe (PFI.InequivalenceResult arch)
proofResult e = foldr merge Nothing statuses
  where
    merge ::
      PF.VerificationStatus (PFI.InequivalenceResult arch) ->
      Maybe (PFI.InequivalenceResult arch) ->
      Maybe (PFI.InequivalenceResult arch)
    merge (PF.VerificationFail ce) _ = Just ce
    merge _ (Just ce) = Just ce
    merge _ a = a
    
    statuses :: [PF.VerificationStatus (PFI.InequivalenceResult arch)]
    statuses = PF.collectProofExpr go e

    go :: PFI.ProofSymExpr sym arch tp' -> [PF.VerificationStatus (PFI.InequivalenceResult arch)]
    go (PF.ProofExpr (PF.ProofStatus st)) = [st]
    go _ = []
    

noTransition ::
  PT.PatchPair (PS.SimInput sym arch) ->
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
  PA.ValidArch arch =>
  PT.ValidSym sym =>
  sym ->
  PT.PatchPair (PS.SimState sym arch) ->
  PE.StatePred sym arch ->
  PF.ProofApp (PFI.ProofSym sym arch) app PF.ProofDomainType
statePredToDomain sym states stPred =
  PF.ProofDomain
    { PF.prfDomainRegisters = predRegsToDomain sym $ PE.predRegs stPred
    , PF.prfDomainStackMemory = memPredToDomain $ PE.predStack stPred
    , PF.prfDomainGlobalMemory = memPredToDomain $ PE.predMem stPred
    , PF.prfDomainContext = states
    }

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
  PE.MemPred sym arch ->
  PF.ProofMemoryDomain (PFI.ProofSym sym arch)
memPredToDomain memPred =
  PF.ProofMemoryDomain
    { PF.prfMemoryDomain = MapF.fromList $ map go $ PE.memPredToList memPred
    , PF.prfMemoryDomainPolarity = PE.memPredPolarity memPred
    }
  where
    go :: (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      MapF.Pair (PMC.MemCell sym arch) (Const (W4.Pred sym))
    go (Some cell, p) = MapF.Pair cell (Const p)
      
statePredToPreDomain ::
  PS.SimBundle sym arch ->
  PE.StatePred sym arch ->
  EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
statePredToPreDomain bundle stPred = proofNonceExpr $ withSym $ \sym -> do
  return $ statePredToDomain sym states stPred
  where
    states = TF.fmapF PS.simInState $ PS.simIn bundle

statePredToPostDomain ::
  PE.StatePredSpec sym arch ->
  EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
statePredToPostDomain stPredSpec = proofNonceExpr $ withSym $ \sym -> do
  let
    states = TF.fmapF PS.simVarState $ PS.specVars stPredSpec
    stPred = PS.specBody stPredSpec
  return $ statePredToDomain sym states stPred

emptyDomain :: EquivM sym arch (PFI.ProofSymNonceExpr sym arch PF.ProofDomainType)
emptyDomain = proofNonceExpr $ withSym $ \sym -> fmap PS.specBody $ withFreshVars $ \stO stP ->
  return $ (W4.truePred sym, statePredToDomain sym (PT.PatchPair stO stP) (PE.statePredFalse sym))

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

lazyProofEvent ::
  PT.BlockPair arch ->
  EquivM sym arch (a, LazyProofApp sym arch tp) ->
  EquivM sym arch (a, LazyProof sym arch tp)
lazyProofEvent ppair f = lazyProofFinal f $ \e -> do
  blocks <- PD.getBlocks ppair 
  vsym <- CMR.asks envValidSym
  emitEvent (PE.ProofIntermediate blocks (PFI.SomeProofSym vsym e))

lazyProofEvent_ ::
  PT.BlockPair arch ->
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
forkProof f = forkProofFinal f (\_ -> return ())

-- | Same as 'forkProof' but with an additional action that runs after the
-- proof has completed.
forkProofFinal ::
  forall sym arch tp.
  EquivM sym arch (LazyProofApp sym arch tp) ->
  (PFI.ProofSymNonceExpr sym arch tp -> EquivM sym arch ()) ->
  EquivM sym arch (LazyProof sym arch tp)
forkProofFinal f fin = snd <$> mkLazyProof go fin
  where
    go :: EquivM sym arch ((), LazyProofBody sym arch tp)
    go = do
      future <- Par.promise (f >>= joinLazyProofApp)
      return ((), LazyProofBodyFuture future)

forkProofEvent ::
  PT.BlockPair arch ->
  EquivM sym arch (LazyProofApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
forkProofEvent ppair f = forkProofFinal f $ \e -> do
  blocks <- PD.getBlocks ppair 
  vsym <- CMR.asks envValidSym
  emitEvent (PE.ProofIntermediate blocks (PFI.SomeProofSym vsym e))

joinLazyProofApp :: LazyProofApp sym arch tp -> EquivM sym arch (PFI.ProofSymNonceApp sym arch tp)
joinLazyProofApp = PF.traverseProofApp joinLazyProof

joinLazyProof :: LazyProof sym arch tp -> EquivM sym arch (PFI.ProofSymNonceExpr sym arch tp)
joinLazyProof prf = do
  app <- case lazyProofBody prf of
    LazyProofBodyApp app -> joinLazyProofApp app
    LazyProofBodyFuture future -> Par.joinFuture future
  let nonce_prf = PF.ProofNonceExpr (lazyProofNonce prf) (lazyProofParent prf) app 
  liftIO $ lazyProofFinalize prf nonce_prf 
  return nonce_prf
