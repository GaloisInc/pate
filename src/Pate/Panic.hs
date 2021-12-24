{-# LANGUAGE TemplateHaskell #-}
module Pate.Panic (
  P.panic,
  PateComponent(..)
  ) where

import qualified Panic as P

data PateComponent = Verifier
                   | Visualizer
                   | ProofConstruction
                   | InlineCallee
                   | Discovery
                   | Solver
                   | Override
                   | AArch32
                   | MemoryModel
                   deriving (Show)

instance P.PanicComponent PateComponent where
  panicComponentName = show
  panicComponentIssues _ = "https://github.com/GaloisInc/pate/issues"
  panicComponentRevision = $(P.useGitRevision)
