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
  , proofResult
    -- lazy proofs
  , LazyProof(..)
  , LazyProofApp
  , lazyProofApp
  , lazyProof
  , joinLazyProof
  , lazyProofAtom
  , asLazyProof
  , forkProof
  , proofNonceExpr
  , lazyProofFinal
  , lazyProofEvent
  , lazyProofEvent_
  , forkProofFinal
  , forkProofEvent_
  , forkProofEvent
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
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Parallel as Par
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Register as PR
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.Solver as PSo

-- | Convert the result of symbolic execution into a structured slice
-- representation
simBundleToSlice ::
  PS.SimBundle sym arch ->
  EquivM sym arch (PF.BlockSliceTransition sym arch)
simBundleToSlice bundle = withSym $ \sym -> do
  let
    ecaseO = PS.simOutBlockEnd $ PS.simOutO $ bundle
    ecaseP = PS.simOutBlockEnd $ PS.simOutP $ bundle
  footprints <- getFootprints bundle
  memReads <- PEM.memPredToList <$> (liftIO $ PEM.footPrintsToPred sym footprints (W4.truePred sym))
  memWrites <- PEM.memPredToList <$> (liftIO $ PEM.footPrintsToPred sym footprints (W4.falsePred sym))

  preMem <- MapF.fromList <$> mapM (\x -> memCellToOp initState x) memReads
  postMem <- MapF.fromList <$> mapM (\x -> memCellToOp finState x) memWrites

  preRegs <- PR.zipWithRegStatesM (PS.simInRegs $ PS.simInO bundle) (PS.simInRegs $ PS.simInP bundle) (\r vo vp -> getReg r vo vp)
  postRegs <- PR.zipWithRegStatesM (PS.simOutRegs $ PS.simOutO bundle) (PS.simOutRegs $ PS.simOutP bundle) (\r vo vp -> getReg r vo vp)
  
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
      EquivM sym arch (PF.BlockSliceRegOp sym tp)
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
      EquivM sym arch (MapF.Pair (PMC.MemCell sym arch) (PF.BlockSliceMemOp sym))
    memCellToOp (PPa.PatchPair stO stP) (Some cell, cond) = withSym $ \sym -> do
      valO <- liftIO $ PMC.readMemCell sym (MT.memState $ PS.simMem stO) cell
      valP <- liftIO $ PMC.readMemCell sym (MT.memState $ PS.simMem stP) cell
      eqRel <- CMR.asks envBaseEquiv      
      isValidStack <- liftIO $ PE.applyMemEquivRelation (PE.eqRelStack eqRel) cell valO valP
      isValidGlobalMem <- liftIO $ PE.applyMemEquivRelation (PE.eqRelMem eqRel) cell valO valP
      isEquiv <- liftIO $ W4.andPred sym isValidStack isValidGlobalMem
      return $ MapF.Pair cell $ PF.BlockSliceMemOp
        { PF.slMemOpValues = PPa.PatchPairC valO valP
        , PF.slMemOpEquiv = isEquiv
        , PF.slMemOpCond = cond
        }

-- | Compute an aggregate verification condition: preferring an inequivalence result
-- if it exists, but potentially yielding an 'PF.Unverified' result.
proofResult ::
  forall sym arch tp.
  PF.ProofExpr sym arch tp ->
  PF.VerificationStatus sym arch
proofResult e = foldr merge PF.VerificationSuccess statuses
  where
    merge ::
      PF.VerificationStatus sym arch ->
      PF.VerificationStatus sym arch ->
      PF.VerificationStatus sym arch
    merge a@PF.VerificationFail{} _ = a
    merge _ b@PF.VerificationFail{} = b
    merge PF.Unverified _ = PF.Unverified
    merge _ PF.Unverified = PF.Unverified
    merge PF.VerificationSkipped a = a
    merge a PF.VerificationSkipped = a
    merge PF.VerificationSuccess PF.VerificationSuccess = PF.VerificationSuccess
    
    statuses :: [PF.VerificationStatus sym arch]
    statuses = PF.collectProofExpr go e

    go :: PF.ProofExpr sym arch tp' -> [PF.VerificationStatus sym arch]
    go (PF.ProofExpr (PF.ProofStatus st)) = [st]
    go _ = []

noTransition ::
  PPa.PatchPair (PS.SimInput sym arch) ->
  CS.RegValue sym (MS.MacawBlockEndType arch) ->
  EquivM sym arch (PF.BlockSliceTransition sym arch)
noTransition stIn blockEnd = do
  let
    stOut = TF.fmapF (\st -> PS.SimOutput (PS.simInState st) blockEnd) stIn
    bundle = PS.SimBundle stIn stOut
  simBundleToSlice bundle
  

-- these are shims that we can potentially eliminate by unifying
-- the corresponding types

statePredToDomain ::
  PES.StatePred sym arch ->
  EquivM sym arch (PF.EquivalenceDomain sym arch)
statePredToDomain stPred = withSym $ \sym ->
  PF.EquivalenceDomain
    <$> (return $ predRegsToDomain sym $ PES.predRegs stPred)
    <*> (flattenToStackRegion $ memPredToDomain $ PES.predStack stPred)
    <*> (return $ memPredToDomain $ PES.predMem stPred)

flattenToStackRegion ::
  PF.MemoryDomain sym arch ->
  EquivM sym arch (PF.MemoryDomain sym arch)
flattenToStackRegion dom = do
  stackRegion <- CMR.asks (PMC.stackRegion . envCtx)
  let
    dom' = map (\(MapF.Pair cell p) -> MapF.Pair (PMC.setMemCellRegion stackRegion cell) p) (MapF.toList (PF.memoryDomain dom))
  return $ dom { PF.memoryDomain = MapF.fromList dom' }


predRegsToDomain ::
  forall arch sym.
  PA.ValidArch arch =>
  PSo.ValidSym sym =>
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
  PSo.ValidSym sym =>
  PEM.MemPred sym arch ->
  PF.MemoryDomain sym arch
memPredToDomain memPred =
  PF.MemoryDomain
    { PF.memoryDomain = MapF.fromList $ map go $ PEM.memPredToList memPred
    , PF.memoryDomainPolarity = PEM.memPredPolarity memPred
    }
  where
    go :: (Some (PMC.MemCell sym arch), W4.Pred sym) ->
      MapF.Pair (PMC.MemCell sym arch) (Const (W4.Pred sym))
    go (Some cell, p) = MapF.Pair cell (Const p)

statePredToPreDomain ::
  PES.StatePred sym arch ->
  EquivM sym arch (PF.ProofNonceExpr sym arch PF.ProofDomainType)
statePredToPreDomain stPred = proofNonceExpr $ do
  PF.ProofDomain <$> statePredToDomain stPred

statePredToPostDomain ::
  PE.StatePredSpec sym arch ->
  EquivM sym arch (PF.ProofNonceExpr sym arch PF.ProofDomainType)
statePredToPostDomain stPredSpec = proofNonceExpr $ do
  let
    stPred = PS.specBody stPredSpec
  PF.ProofDomain <$> statePredToDomain stPred

emptyDomain :: EquivM sym arch (PF.ProofNonceExpr sym arch PF.ProofDomainType)
emptyDomain = proofNonceExpr $ withSym $ \sym ->
  PF.ProofDomain <$> statePredToDomain (PES.statePredFalse sym)

proofNonceExpr ::
  EquivM sym arch (PF.ProofNonceApp sym arch tp) ->
  EquivM sym arch (PF.ProofNonceExpr sym arch tp)
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
      lazyProofNonce :: PF.ProofNonce sym tp
    , lazyProofParent :: Some (PF.ProofNonce sym)
    , lazyProofBody :: LazyProofBody sym arch tp
    , lazyProofFinalize :: PF.ProofNonceExpr sym arch tp -> IO ()
    } -> LazyProof sym arch tp


-- | Lazy proof bodies are either sub-trees of lazy proofs, or future values
-- of completed proofs
data LazyProofBody sym arch tp where
  LazyProofBodyApp :: LazyProofApp sym arch tp -> LazyProofBody sym arch tp
  LazyProofBodyFuture :: Par.Future (PF.ProofNonceApp sym arch tp) -> LazyProofBody sym arch tp

type LazyProofApp sym arch = PF.ProofApp sym arch (LazyProof sym arch)

-- instance (PA.ValidArch arch, PSo.ValidSym sym) => PEM.ExprMappable sym (LazyProofBody sym arch tp) where
--   mapExpr sym f (LazyProofBodyApp app) = LazyProofBodyApp <$> PEM.mapExpr sym f app
--   mapExpr sym f (LazyProofBodyFuture future) = LazyProofBodyFuture <$> PEM.mapExpr sym f future
-- 
-- instance (PA.ValidArch arch, PSo.ValidSym sym) => PEM.ExprMappable sym (LazyProof sym arch tp) where
--   mapExpr sym f (LazyProof a1 a2 v fin) = do
--     v' <- PEM.mapExpr sym f v
--     return $ LazyProof a1 a2 v' fin
--

mkLazyProof ::
  EquivM sym arch (a, LazyProofBody sym arch tp) ->
  (PF.ProofNonceExpr sym arch tp -> EquivM sym arch ()) ->
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
  (PF.ProofNonceExpr sym arch tp -> EquivM sym arch ()) ->
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
  PF.ProofNonceExpr sym arch tp -> LazyProof sym arch tp
asLazyProof e =
  LazyProof (PF.prfNonce e) (PF.prfParent e) (asLazyProofApp (PF.prfNonceBody e)) (\_ -> return ())

asLazyProofApp ::
  PF.ProofNonceApp sym arch tp -> LazyProofBody sym arch tp
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
  (PF.ProofNonceExpr sym arch tp -> EquivM sym arch ()) ->
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

joinLazyProofApp :: LazyProofApp sym arch tp -> EquivM sym arch (PF.ProofNonceApp sym arch tp)
joinLazyProofApp pa = PF.traverseProofApp (\x -> joinLazyProof x) pa

joinLazyProof :: LazyProof sym arch tp -> EquivM sym arch (PF.ProofNonceExpr sym arch tp)
joinLazyProof prf = withValid $ do
  app <- case lazyProofBody prf of
    LazyProofBodyApp app -> joinLazyProofApp app
    LazyProofBodyFuture future -> Par.joinFuture future
  let nonce_prf = PF.ProofNonceExpr (lazyProofNonce prf) (lazyProofParent prf) app
  liftIO $ lazyProofFinalize prf nonce_prf
  return nonce_prf

lazyProofAtom :: LazyProof sym arch tp -> EquivM sym arch (PF.ProofApp sym arch (PF.ProofNonceExpr sym arch) tp)
lazyProofAtom prf = PF.prfNonceBody <$> joinLazyProof prf

asFutureNonceApp ::
  LazyProof sym arch tp ->
  EquivM sym arch (Par.Future (PF.ProofNonceApp sym arch tp))
asFutureNonceApp prf = case lazyProofBody prf of
  LazyProofBodyFuture future -> return future
  LazyProofBodyApp app -> Par.present $ joinLazyProofApp app

wrapFutureNonceApp ::
  Par.Future (PF.ProofNonceApp sym arch tp) ->
  EquivM sym arch (LazyProof sym arch tp)
wrapFutureNonceApp future = snd <$> mkLazyProof (return ((), LazyProofBodyFuture future)) (\_ -> return ())
