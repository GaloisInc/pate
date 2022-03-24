This document contains information that developers should keep in mind while working on the PATE verifier codebase

Continuous Integration
======================

Our CI system is Github Actions on our internally-hosted runners. These runners have enough memory to build all of the dependencies quickly, as well as run the tests in parallel. The public runners do not have enough memory to build e.g., macaw-aarch32, which used to result in many CI jobs failing due to out-of-memory conditions. The CI setup employs aggressive caching of all build dependencies so that each CI run only needs to build the pate codebase itself. This is challenging for a number of reasons:

- We use submodules to track non-Hackage dependencies, which are critical but problematic, as ``cabal`` does filesystem local (non-Hackage) (re-)builds based on file timestamps. Caching obliterates those timestamps, so caching our submodule builds (via ``dist-submodules``) is ineffective and always rebuilt
- To work around this, we use a script by Ryan Scott that rewrites our submodule references as cabal source repository packages, which are built in the cabal store. Rebuild checks in the cabal store are based on file hash rather than timestamps, so caching can be effective
- The caching in Github Actions has the property that if a build triggers a cache hit, the cache artifact will *not* be updated. This means that any changes to the build configuration are problematic. For example, if an update to the Hackage index brings in a dependency update that triggers a rebuild of crucible or macaw, the cache is "spoiled", but not updated. To avoid this, we essentially have to use cabal freeze files to fix our dependencies. The CI configuration hashes the cabal freeze file and our submodule hashes to ensure that any changes to the cached information triggers a full rebuild.


Updating Freeze Files
---------------------

To update the cabal freeze files, run the ``scripts/regenerate-freeze-files.sh`` script from the repository root. This will invoke cabal with each of the supported compilers and put the resulting freeze files in the places that the CI system expects. The updated freeze files need to be checked in.
