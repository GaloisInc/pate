{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Definitions of solvers usable in the pate verifier
module Pate.Solver (
    Solver(..)
  , solverAdapter
  , ValidSym
  , Sym(..)
  , withOnlineSolver
  , BackendPool
  , SyncedBackend
  , viewSyncedBackend
  , withSyncedBackend
  , withBackendPool
  , bracketSyncedBackends
  , bracketSyncedBackends_
  ) where

import           Control.Monad.Catch ( MonadMask, MonadCatch, bracket, tryJust, SomeException )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Bits ( (.|.) )
import           Data.Parameterized.Classes ( ShowF )
import qualified Data.Parameterized.Nonce as PN
import qualified Data.Text as T
import qualified What4.Config as WC
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.ProblemFeatures as WP
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import Data.Data (Typeable)
import qualified What4.JSON as W4S
import Control.Concurrent (MVar, takeMVar, newMVar, tryPutMVar, tryTakeMVar, putMVar)
import Control.Monad (void)
import What4.Utils.Process (filterAsync)
import Control.Exception (throw)

-- | The solvers supported by the pate verifier
--
-- We use this type to select solvers from the command line, as some work is
-- required to actually set up the symbolic backend for each solver adapter.
data Solver = CVC4
            | Yices
            | Z3
            deriving (Eq, Ord, Show, Read)

-- | Start a connection to an online solver (using the chosen 'Solver')
withOnlineSolver
  :: (MonadIO m, MonadMask m, sym ~ WE.ExprBuilder scope st fs, CB.IsSymInterface sym)
  => Solver
  -- ^ The chosen solver
  -> Maybe FilePath
  -- ^ A file to save solver interactions to
  -> WE.ExprBuilder scope st fs
  -> (forall solver. WPO.OnlineSolver solver =>
       CBO.OnlineBackend solver scope st fs -> m a)
  -- ^ The continuation where the online solver connection is active
  -> m a
withOnlineSolver solver mif sym k = do
  sym' <- liftIO $ WE.exprBuilderSplitConfig sym
  case solver of
    CVC4 -> CBO.withCVC4OnlineBackend sym' CBO.NoUnsatFeatures probFeatures
                  (\bak -> installSolverInteraction mif >> k bak)
    Yices -> CBO.withYicesOnlineBackend sym' CBO.NoUnsatFeatures probFeatures
                  (\bak -> installSolverInteraction mif >> k bak)
    Z3 -> CBO.withZ3OnlineBackend sym' CBO.NoUnsatFeatures probFeatures
                  (\bak -> installSolverInteraction mif >> k bak)

  where
    -- Install some selected SMT problem features, as the online backend is not
    -- able to analyze the query to determine what features are needed (since it
    -- doesn't get to preview any formulas)
    probFeatures = WP.useSymbolicArrays .|. WP.useStructs .|. WP.useBitvectors

    -- A wrapper to install a solver interaction file, if requested by the user
    installSolverInteraction Nothing = return ()
    installSolverInteraction (Just interactionFile) = do
      let conf = WI.getConfiguration sym
      setSIF <- liftIO $ WC.getOptionSetting CBO.solverInteractionFile conf
      _diags <- liftIO $ WC.setOpt setSIF (T.pack interactionFile)
      return ()

-- | Convert the solver selector type ('Solver') into a what4
-- 'WS.SolverAdapter', extending the symbolic backend with the necessary options
-- (which requires IO)
solverAdapter :: (WI.IsExprBuilder sym) => sym -> Solver -> IO (WS.SolverAdapter st)
solverAdapter _sym s =
  case s of
    CVC4 -> return WS.cvc4Adapter
    Yices -> return WS.yicesAdapter
    Z3 -> return WS.z3Adapter

type ValidSym sym =
  ( WI.IsExprBuilder sym
  , CB.IsSymInterface sym
  , ShowF (WI.SymExpr sym)
  , W4S.W4SerializableF sym (WI.SymExpr sym)
  )

-- | An 'CBO.OnlineBackend' with an associated semaphore, indicating that the backend thread is idle
data SyncedBackend sym where
  SyncedBackend :: (sym ~ WE.ExprBuilder scope st fs, WPO.OnlineSolver solver) => 
    MVar () ->
    CBO.OnlineBackend solver scope st fs -> 
    SyncedBackend sym

-- | A pool of online backends, with an associated MVar used to signal when
--   some pool has become free. We can safely traverse the list of backends to
--   find a free solver, and then block on this mvar if none are available
data BackendPool sym where
  BackendPool :: MVar () -> [SyncedBackend sym] -> BackendPool sym

withBackendPool ::
  forall m sym a scope st fs.
  (MonadIO m, MonadMask m, sym ~ WE.ExprBuilder scope st fs, CB.IsSymInterface sym)
  => Solver
  -- ^ The chosen solver
  -> Maybe FilePath
  -- ^ A file to save solver interactions to
  -> WE.ExprBuilder scope st fs
  -> Integer
  -- ^ how many solvers to add to the pool (number of hardware threads?)
  -> (BackendPool sym -> m a)
  -> m a
withBackendPool solverK fp sym i f = do
  outer_mv <- liftIO $ newMVar ()
  go i (BackendPool outer_mv [])
  where
    go :: Integer -> BackendPool sym -> m a
    go l bp | l <= 0 = do
      a <- f bp
      liftIO $ flushBackends bp
      return a
    go l (BackendPool outer_mv backends) = do
      let fp' = fmap (\x -> x ++ "_" ++ show l) fp
      withOnlineSolver solverK fp' sym $ \solver -> do
        mv <- liftIO $ newMVar ()
        let backend = SyncedBackend mv solver
        go (l-1) (BackendPool outer_mv (backend:backends))


viewSyncedBackend :: SyncedBackend sym -> (forall solver scope st fs. (sym ~ WE.ExprBuilder scope st fs, WPO.OnlineSolver solver) => CBO.OnlineBackend solver scope st fs -> f a) -> f a
viewSyncedBackend (SyncedBackend _ solver) f = f solver

-- | Pick a 'SyncedBackend' that is ready in the given pool, blocking if
--   no backends are ready. Runs the inner computation and then finally unblocks
--   the backend
withSyncedBackend :: forall m sym a. (MonadIO m, MonadMask m) => BackendPool sym -> (SyncedBackend sym -> m a) -> m a
withSyncedBackend (BackendPool outer_mv all_backends) f = do
  bracket 
    (pick_free all_backends)
    -- TODO: raise an error if the backend-specific semaphore was somehow released?
    (\x -> do
      () <- case x of
        (SyncedBackend mv _) -> (liftIO (tryPutMVar mv () >> tryPutMVar outer_mv () >> return ()))
      return ())
    f
  where
    pick_free :: [SyncedBackend sym] -> m (SyncedBackend sym)
    pick_free [] = do
      -- block on signal saying some pool is ready
      liftIO $ takeMVar outer_mv
      pick_free all_backends
    pick_free (sbak@(SyncedBackend mv _):backends) = (liftIO $ tryTakeMVar mv) >>= \case
      Just () -> return sbak
      Nothing -> pick_free backends

-- | Perform a given setup and subsequent close operation on all the backends in a pool
bracketSyncedBackends :: 
  forall m sym a b c. 
  (MonadIO m, MonadMask m) => 
  BackendPool sym -> 
  (SyncedBackend sym -> m a) -> 
  ([a] -> m c) -> 
  (SyncedBackend sym -> a -> m b) -> 
  m ([b], c)
bracketSyncedBackends bp@(BackendPool _outer_mv all_backends) open body close = do
  liftIO $ flushBackends bp
  as <- mapM (\bak -> wait_then_free bak (open bak)) all_backends
  mc <- tryJust filterAsync (body as)
  bs <- mapM (\(bak,a) -> wait_then_free bak (close bak a)) (zip all_backends as)
  case mc of
    Left ex -> throw ex
    Right c -> return (bs,c)
  where
    wait_then_free :: forall x. SyncedBackend sym -> m x -> m x
    wait_then_free bak f = do
      wait_bak bak
      a <- f
      free_bak bak
      return a

    wait_bak :: SyncedBackend sym -> m ()
    wait_bak (SyncedBackend mv _) = do
      liftIO $ takeMVar mv
    
    free_bak :: SyncedBackend sym -> m ()
    free_bak (SyncedBackend mv _) = do
      void $ liftIO $ tryPutMVar mv ()

-- | Canonical form of 'bracketSyncedBackends'
bracketSyncedBackends_ :: 
  forall m sym a c. 
  (MonadIO m, MonadMask m) => 
  BackendPool sym -> 
  (SyncedBackend sym -> m a) -> 
  m c -> 
  (SyncedBackend sym -> a -> m ()) -> 
  m c
bracketSyncedBackends_ bp open body close = snd <$> bracketSyncedBackends bp open (\_ -> body) (\bak a -> close bak a)

-- | Block until all backends have finished
flushBackends :: BackendPool sym -> IO ()
flushBackends (BackendPool outer_mv all_backends) = do
  go all_backends
  where
    go :: [SyncedBackend sym] -> IO ()
    -- make sure nobody is waiting at the toplevel
    go [] = tryPutMVar outer_mv () >>= \case
        True -> go all_backends
        False -> return ()
    go ((SyncedBackend mv _):backends) = do
      -- wait until it's ready
      takeMVar mv
      -- mark it ready again
      putMVar mv ()
      -- raise signal that a solver is ready
      tryPutMVar outer_mv () >>= \case
        True -> go all_backends
        False -> go backends

-- | A wrapper around the symbolic backend (a 'WE.ExprBuilder') that captures
-- various constraints that we need in the verifier
--
-- In many uses of what4, the concrete type of the symbolic backend does not
-- need to be known. However, the pate tool does need to know because it
-- manually traverses terms to simplify and analyze them.
--
-- We also carry the chosen solver adapter in this wrapper, as the symbolic
-- backend and the adapter share a type parameter (@st@) that we do not want to
-- expose to the rest of the verifier (since it would pollute every type
-- signature).
--
-- This type allows us to unwrap the constraints when we need them to observe
-- the relationships between these otherwise internal types.
data Sym sym where
  Sym :: ( sym ~ WE.ExprBuilder scope st fs
         , ValidSym sym
         )
      => PN.Nonce PN.GlobalNonceGenerator sym
      -> sym
      -> BackendPool sym
      -> Sym sym
