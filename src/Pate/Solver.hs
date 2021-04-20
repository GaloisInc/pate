-- | Definitions of solvers usable in the pate verifier
module Pate.Solver (
  Solver(..),
  solverAdapter
  ) where

import qualified What4.Config as WC
import qualified What4.Interface as WI
import qualified What4.Solver as WS
import qualified What4.Solver.CVC4 as WSC
import qualified What4.Solver.Yices as WSY
import qualified What4.Solver.Z3 as WSZ

-- | The solvers supported by the pate verifier
data Solver = CVC4
            | Yices
            | Z3
            deriving (Eq, Ord, Show, Read)

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
