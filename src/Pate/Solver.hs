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
import           Control.Monad.IO.Class ( MonadIO )
import           Data.Parameterized.Classes ( ShowF )
import qualified Data.Parameterized.Nonce as PN
import qualified What4.Config as WC
import qualified What4.Expr.Builder as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.ProblemFeatures as WP
import qualified What4.Solver as WS
import qualified What4.Solver.CVC4 as WSC
import qualified What4.Solver.Yices as WSY
import qualified What4.Solver.Z3 as WSZ

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
  -- -> WE.FloatModeRepr fm
  -> PN.NonceGenerator IO scope
  -> (forall sym solver fm . (sym ~ CBO.OnlineBackend scope solver (WE.Flags fm), WPO.OnlineSolver solver, CB.IsSymInterface sym) => CBO.OnlineBackend scope solver (WE.Flags fm) -> m a)
  -- ^ The continuation where the online solver connection is active
  -> m a
withOnlineSolver solver ng k =
  case solver of
    CVC4 -> CBO.withCVC4OnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures WP.noFeatures k
    Yices -> CBO.withYicesOnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures WP.noFeatures k
    Z3 -> CBO.withZ3OnlineBackend WE.FloatRealRepr ng CBO.NoUnsatFeatures WP.noFeatures k

-- | Convert the solver selector type ('Solver') into a what4
-- 'WS.SolverAdapter', extending the symbolic backend with the necessary options
-- (which requires IO)
solverAdapter :: (WI.IsExprBuilder sym) => sym -> Solver -> IO (WS.SolverAdapter st)
solverAdapter sym s = do
  let cfg = WI.getConfiguration sym
  case s of
    CVC4 -> do
      WC.extendConfig WSC.cvc4Options cfg
      return WS.cvc4Adapter
    Yices -> do
      WC.extendConfig WSY.yicesOptions cfg
      return WS.yicesAdapter
    Z3 -> do
      WC.extendConfig WSZ.z3Options cfg
      return WS.z3Adapter

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
  Sym :: (sym ~ (WE.ExprBuilder t st fs), ValidSym sym) => PN.Nonce PN.GlobalNonceGenerator sym -> sym -> WS.SolverAdapter st -> Sym sym
