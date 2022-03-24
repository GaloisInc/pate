#!/usr/bin/env bash
#
# Regenerate the freeze files for CI. This should be run from the root of the repository

cabal freeze -w ghc-8.8.4
mv cabal.project.freeze cabal.GHC-8.8.4.freeze

cabal freeze -w 8.10.7
mv cabal.project.freeze cabal.GHC-8.10.7.freeze

# We need allow-newer here because snap has lagging dependencies
cabal freeze -w 9.0.2 --allow-newer=base
mv cabal.project.freeze cabal.GHC-9.0.2.freeze
