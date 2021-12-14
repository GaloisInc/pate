{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
-- | Definitions of solvers usable in the pate verifier
module Pate.Solver (
    Solver(..)
  , solverAdapter
  , ValidSym
  , Sym(..)
  , withOnlineSolver
  ) where

import           Control.Monad.Catch ( MonadMask )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Bits ( (.|.) )
import           Data.Parameterized.Classes ( ShowF )
import qualified Data.Parameterized.Nonce as PN
import qualified Data.Text as T
import qualified What4.Config as WC
import qualified What4.Expr.Builder as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.ProblemFeatures as WP
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO

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
  :: (MonadIO m, MonadMask m)
  => Solver
  -- ^ The chosen solver
  -> Maybe FilePath
  -- ^ A file to save solver interactions to
  -> PN.NonceGenerator IO scope
  -> (forall sym solver fm . (sym ~ CBO.OnlineBackend scope solver (WE.Flags fm), WPO.OnlineSolver solver, CB.IsSymInterface sym) => CBO.OnlineBackend scope solver (WE.Flags fm) -> m a)
  -- ^ The continuation where the online solver connection is active
  -> m a
withOnlineSolver solver mif ng k =
  case solver of
    CVC4 -> CBO.withCVC4OnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures probFeatures (installSolverInteraction mif k)
    Yices -> CBO.withYicesOnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures probFeatures (installSolverInteraction mif k)
    Z3 -> CBO.withZ3OnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures probFeatures (installSolverInteraction mif k)
  where
    -- Install some selected SMT problem features, as the online backend is not
    -- able to analyze the query to determine what features are needed (since it
    -- doesn't get to preview any formulas)
    probFeatures = WP.useSymbolicArrays .|. WP.useStructs .|. WP.useBitvectors

    -- A wrapper to install a solver interaction file, if requested by the user
    installSolverInteraction Nothing k' sym = k' sym
    installSolverInteraction (Just interactionFile) k' sym = do
      let conf = WI.getConfiguration sym
      setSIF <- liftIO $ WC.getOptionSetting CBO.solverInteractionFile conf
      _diags <- liftIO $ WC.setOpt setSIF (T.pack interactionFile)
      k' sym

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
  )

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
  Sym :: ( sym ~ CBO.OnlineBackend scope solver (WE.Flags fm)
         , WPO.OnlineSolver solver
         , ValidSym sym
         , st ~ CBO.OnlineBackendState solver CBO.EmptyUserState
         )
      => PN.Nonce PN.GlobalNonceGenerator sym
      -> sym
      -> WS.SolverAdapter st
      -> Sym sym
