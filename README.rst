Overview
========

This repository implements a tool to verify that patches are assured up to trace equivalence (PATE).

The goal is to prove that security patches applied to binaries only remove bad behaviors, or otherwise characterize them precisely for the developer of the patch. The verifier supports PowerPC and AArch32 binaries (currently requiring statically linked ELF binaries).

Quick Start
-----------

The fastest way to get started is to build the Docker image and use the tool via Docker.  For more in-depth build instructions, see the Development section, below.

First, build the Docker image with the command::

  docker build . -t pate

Next, run the verifier on an example from the test suite::

  docker run -it -p 5000:5000 -v `pwd`/tests:/tests pate --original /tests/aarch32/conditional/test-signed-equiv.original.exe --patched /tests/aarch32/conditional/test-signed-equiv.patched.exe --interactive

Visit http://localhost:5000 to view the interactive proof explorer.

Command Line Options
--------------------

The verifier accepts the following command line arguments::

  -h,--help                Show this help text
  -o,--original EXE        Original binary
  -p,--patched EXE         Patched binary
  -b,--blockinfo FILENAME  Block information relating binaries
  -i,--interactive         Start a web server providing an interactive view of results
  --original-source FILE   The source file for the original program
  --patched-source FILE    The source file for the patched program
  --log-file FILE          Record logs in the given file
  --discard-logs           Discard all logging information
  -m,--ignoremain          Don't add the main entry points to the set of function equivalence checks.
  -d,--nodiscovery         Don't dynamically discover function pairs based on calls.
  --noproofs               Don't print structured proofs after checking.
  --try-simple-frames      Attempt simple frame propagation first, falling back to heuristic analysis upon failure.
  --solver ARG             The SMT solver to use to solve verification conditions. One of CVC4, Yices, or Z3 (default: Yices)
  --goal-timeout ARG       The timeout for verifying individual goals in seconds (default: 300)
  --heuristic-timeout ARG  The timeout for verifying heuristic goals in seconds (default: 10)
  --anvill-hints ARG       Parse an Anvill specification for code discovery hints
  --probabilistic-hints ARG
                           Parse a JSON file containing probabilistic function name/address hints
  --csv-function-hints ARG Parse a CSV file containing function name/address hints
  --dwarf-hints            Extract hints from the unpatched DWARF binary

Design
======

The verifier takes two binaries as input: an original binary and a patched binary. The assumption is that some security-oriented patch has been applied to the original binary that largely preserves its behavior, but may fix some undesirable behaviors. The verifier then attempts to prove that the two binaries exhibit the same observable behavior; if it cannot, it produces a *differential summary* that describes the conditions under which the patched binary exhibits different behavior from the original.  This enables patch developers to understand the impact of their patches on the program semantics and evaluate if the impact is restricted to the execution paths that they intended.

The verifier does not require a manually-provided specification from users; instead, it treats the original program as the desired behavioral specification. This arrangement makes pate a *relational* verifier, as it relates the patched binary to the original. The verifier is based on a number of existing libraries for binary code discovery and symbolic execution of programs (including machine code programs).  Roughly, the verifier works by:

1. Performing code discovery on both binaries
2. Breaking the binaries into *slices*, which are collections of basic blocks with control flow between them, but without backedges; it also breaks regions at function call boundaries
3. It aligns slices based on control flow and under the heuristic assumption that machine states will be similar after each pair of corresponding slices in the original and patched binaries
4. It infers frame conditions (in the form of pre- and post- conditions) for each slice that are sufficient to prove that the original slice has the same behavior as the patched slice
5. It attempts to verify that all of the slice pairs satisfy their frame conditions by symbolically executing both slices on the same inputs (under the set of inferred preconditions) and verifying that the patched program satisfies its required inferred postcondition
6. If a pair of slices fails to satisfy the frame condition, it computes a differential summary describing the conditions under which they exhibit different behaviors

Development
===========

Requirements
------------

- ghc (8.10.4 suggested)
- cabal
- yices

Build Steps
-----------

The pate tool is written in Haskell and requires the GHC compiler (version 8.6-8.10) and the cabal build tool to compile.  Building from source can be accomplished by::

  git clone git@github.com:GaloisInc/pate.git
  cd pate
  git submodule update --init
  cp cabal.project.dist cabal.project
  cabal configure pkg:pate
  cabal build pkg:pate

The verifier requires an SMT solver to be available in ``PATH``. The default is ``yices``, but ``z3`` and ``cvc4`` are also supported.
