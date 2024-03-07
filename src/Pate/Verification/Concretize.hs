{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Pate.Verification.Concretize (
    Concretize
  , concreteBV
  , concreteInteger
  , concreteBool
  , resolveSingletonSymbolicAs
  , resolveSingletonSymbolicAsDefault
  , resolveSingletonPointer
  , WrappedSolver(..)
  , wrappedBackend
  , symbolicFromConcrete
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

import           What4.ExprHelpers ( integerToNat )
import qualified Pate.Panic as PP

data Concretize sym tp where
  Concretize :: (Show (WEG.GroundValue tp))
             => WT.BaseTypeRepr tp
             -> (WI.SymExpr sym tp -> Maybe (WEG.GroundValue tp)) -- Convert a symbolic term to a concrete value
             -> (sym -> WI.SymExpr sym tp -> WEG.GroundValue tp -> IO (WI.SymExpr sym WT.BaseBoolType)) -- Create a blocking clause from a concrete value
             -> (sym -> WEG.GroundValue tp -> IO (WI.SymExpr sym tp)) -- Create a symbolic term wrapping the concrete result
             -> Concretize sym tp

concreteBV :: (WI.IsSymExprBuilder sym, 1 <= w) => PN.NatRepr w -> Concretize sym (WI.BaseBVType w)
concreteBV w = Concretize (WT.BaseBVRepr w) WI.asBV toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.bvEq sym symVal =<< WI.bvLit sym w gv
    injectSymbolic sym gv = WI.bvLit sym w gv

concreteInteger :: (WI.IsSymExprBuilder sym) => Concretize sym WI.BaseIntegerType
concreteInteger = Concretize WT.BaseIntegerRepr WI.asInteger toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.intEq sym symVal =<< WI.intLit sym gv
    injectSymbolic = WI.intLit


concreteBool :: (WI.IsSymExprBuilder sym) => Concretize sym WI.BaseBoolType
concreteBool = Concretize WT.BaseBoolRepr WI.asConstantPred toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.eqPred sym symVal =<< injectSymbolic sym gv
    injectSymbolic sym True = return $ WI.truePred sym 
    injectSymbolic sym False = return $ WI.falsePred sym

data WrappedSolver sym m where
  WrappedSolver :: sym ~ (WE.ExprBuilder scope solver fs) =>
    { solverSym :: sym
    , _runSolver :: (forall a. String -> WI.Pred sym -> (WSat.SatResult (WEG.GroundEvalFn scope) () -> m a) -> m a)
    } -> WrappedSolver sym m

withSolver ::
  WrappedSolver sym m ->
  (forall scope solver fs.
    sym ~ (WE.ExprBuilder scope solver fs) =>
    sym ->
    (forall a.  String -> WI.Pred sym -> (WSat.SatResult (WEG.GroundEvalFn scope) () -> m a) -> m a) -> m b) ->
  m b
withSolver (WrappedSolver sym f) g = g sym f

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it. Otherwise, return the original symbolic value
resolveSingletonSymbolicAs
  :: ( LCB.IsSymInterface sym
     , HasCallStack
     , MonadIO m
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> WrappedSolver sym m
  -- ^ Solver continuation
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> m (WI.SymExpr sym tp)
resolveSingletonSymbolicAs (Concretize _tp asConcrete toBlocking injectSymbolic) wsolver val = withSolver wsolver $ \(sym :: WE.ExprBuilder scope solver fs) runSolver ->
  case asConcrete val of
    Just _ -> return val
    Nothing -> do
      val' <- runSolver "Concretize value (with no assumptions)" (WI.truePred sym) $ \msat -> do
        mmodel <- case msat of
          WSat.Unknown -> return Nothing
          WSat.Unsat {} -> return Nothing
          WSat.Sat mdl -> return (Just mdl)
        liftIO $ T.forM mmodel $ \mdl -> WEG.groundEval mdl val
      case val' of
        Nothing -> return val -- We failed to get a model... leave it symbolic
        Just concVal -> do
          block <- liftIO $ toBlocking sym val concVal
          runSolver "Concretize value (with blocking clause)" block $ \msat ->
            case msat of
              WSat.Unknown -> return val -- Total failure
              WSat.Sat _mdl -> return val  -- There are multiple models
              WSat.Unsat {} -> liftIO $ injectSymbolic sym concVal -- There is a single concrete result

wrappedBackend
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , HasCallStack
     , WPO.OnlineSolver solver
     )
  => LCBO.OnlineBackend solver scope st fs
  -> WrappedSolver sym IO
wrappedBackend bak = WrappedSolver (LCB.backendGetSym bak) $ \desc p k ->
  LCBO.withSolverProcess bak onlinePanic $ \sp -> WPO.inNewFrame sp $ do
  WPS.assume (WPO.solverConn sp) p
  WPO.checkAndGetModel sp desc >>= k
  where
    onlinePanic = PP.panic PP.InlineCallee "wrappedBackend" ["Online solver support is not enabled"]

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
-- Defers to 'resolveSingletonSymbolicAs' with default concretization strategies
resolveSingletonSymbolicAsDefault
  :: ( LCB.IsSymInterface sym
     , HasCallStack
     , MonadIO m
     )
  => WrappedSolver sym m
  -- ^ Solver continuation
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> m (WI.SymExpr sym tp)
resolveSingletonSymbolicAsDefault wsolver val = case WI.exprType val of
  WI.BaseBoolRepr -> resolveSingletonSymbolicAs concreteBool wsolver val
  WI.BaseIntegerRepr -> resolveSingletonSymbolicAs concreteInteger wsolver val
  WI.BaseBVRepr w -> resolveSingletonSymbolicAs (concreteBV w) wsolver val
  _ -> return val -- unsupported type, therefore failure


-- | Resolve an 'LCLM.LLVMPtr' to concrete, if possible
--
-- The block id and offset are concretized independently, and either (or
-- neither) could be updated
resolveSingletonPointer
  :: ( LCB.IsSymInterface sym
     , 1 <= w
     , HasCallStack
     , MonadIO m
     )
  => WrappedSolver sym m
  -- ^ Solver continuation
  -> LCLM.LLVMPtr sym w
  -- ^ The symbolic term to concretize
  -> m (LCLM.LLVMPtr sym w)
resolveSingletonPointer wsolver ptr@(LCLM.LLVMPointer base off) = do
  let sym = solverSym wsolver
  base_i <- (resolveSingletonSymbolicAs concreteInteger wsolver (WI.natToIntegerPure base))
  base' <- liftIO $ integerToNat sym base_i
  off' <- resolveSingletonSymbolicAs (concreteBV (LCLM.ptrWidth ptr)) wsolver off
  return (LCLM.LLVMPointer base' off')


symbolicFromConcrete
  :: ( WI.IsSymExprBuilder sym
     , HasCallStack
     )
  => sym
  -> WEG.GroundValue tp
  -> WI.SymExpr sym tp
  -> IO (WI.SymExpr sym tp)
symbolicFromConcrete sym gv e = case WI.exprType e of
  WI.BaseBoolRepr -> let (Concretize _ _ _ inject) = concreteBool in inject sym gv
  WI.BaseIntegerRepr -> let (Concretize _ _ _ inject) = concreteInteger in inject sym gv
  WI.BaseBVRepr w -> let (Concretize _ _ _ inject) = concreteBV w in inject sym gv
  _ -> return e
