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

  docker run --rm -it -p 5000:5000 -v `pwd`/tests:/tests pate --original /tests/aarch32/conditional/test-signed-equiv.original.exe --patched /tests/aarch32/conditional/test-signed-equiv.patched.exe --interactive

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
  --no-dwarf-hints         Disable extraction of hints from the unpatched DWARF binary
  --save-macaw-cfgs DIR    Save macaw CFGs to the provided directory
  --solver-interaction-file FILE
                           Save interactions with the SMT solver during symbolic
                           execution to this file
  --proof-summary-json FILE
                           A file to save interesting proof results to in JSON
                           format
  --log-file FILE          A file to save debug logs to

Extended Examples
-----------------

The quick start section described a command to run the verifier on a test case using the Docker container.  This section will cover some useful commands for other scenarios.

Docker Usage
^^^^^^^^^^^^

If you have a ``tar`` file of a Docker image of the verifier, you can install it using the command::

  docker load -i /path/to/pate.tar

To run the verifier via Docker after this::

  docker run --rm -it pate --help

To make use of the verifier with Docker, it is useful to map a directory on your local filesystem into the Docker container to be able to save output files. Assuming that your original and patched binaries are ``original.exe`` and ``patched.exe``, respectively::

  mkdir VerifierData
  cp original.exe patched.exe VerifierData/
  docker run --rm -it -v `pwd`/VerifierData`:/VerifierData pate \
             --original /VerifierData/original.exe \
             --patched /VerifierData/patched.exe \
             --proof-summary-json /VerifierData/report.json \
             --log-file /VerifierData/pate.log \
             --save-macaw-cfgs /VerifierData/cfgs

This command will run the verifier on the two binaries and produce three outputs:

1. A JSON report summarizing the verifier's findings (``report.json``)
2. A log file with very detailed output explaining what the verifier examined and concluded (``pate.log``)
3. Dumped Control Flow Graphs (CFGs) for all functions that the verifier discovered and analyzed (one file per CFG under ``cfgs``)

Controlling the Verifier Entry Point
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

By default, the verifier starts verifying from the formal program entry point. This is often not very useful (and can be problematic for complex binaries with a large ``_start`` that causes problem for our code discovery).  Additionally, for changes with a known (or at least expected) scope of impact, analyzing just the affected functions is significantly faster.  Customizing the analysis entry point has two steps: 1) passing the ``--ignoremain --blockinfo <config>`` options, 2) providing the configuration file.  Configuration files are in the TOML format. For example, with a configuration file called ``config.toml`` with the following contents::

  patch-pairs = [ { original-block-address = <OriginalEntryPoint>, patched-block-address = <PatchedEntryPoint> }
                ]

one would invoke the verifier with the command::

  mkdir VerifierData
  cp original.exe patched.exe config.toml VerifierData/
  docker run --rm -it -v `pwd`/VerifierData`:/VerifierData pate \
             --original /VerifierData/original.exe \
             --patched /VerifierData/patched.exe \
             --proof-summary-json /VerifierData/report.json \
             --log-file /VerifierData/pate.log \
             --save-macaw-cfgs /VerifierData/cfgs \
             --ignoremain --blockinfo /VerifierData/config.toml

Treating Functions As No-Ops
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While it is unsound, it is sometimes useful to treat a function call as a no-op. For example, ignoring large functions that have not changed and are unlikely to have an effect on correctness (e.g., large cryptographic functions from trusted libraries) can significantly improve performance.  To use this feature, pass a configuration file to the verifier using the ``--blockinfo`` option, ensuring that the configuration file includes the following directives::

  ignore-original-functions = [ <ADDRESS>, ... ]
  ignore-patched-functions = [ <ADDRESS>, ... ]

where each of the lists is a list of addresses of functions to ignore. While the two lists are specified separately, they should almost certainly be "aligned" between the two binaries (i.e., ignoring a function in the original binary probably means that the corresponding function in the patched binary also needs to be ignored).

Adding DWARF Metadata to a Binary
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The verifier benefits from DWARF metadata in two ways:

1. It improves code discovery by identifying function entry points that the verifier could otherwise miss
2. It improves some diagnostics where references to machine state can be rendered as references to named program constructs, with names provided by DWARF

To inject DWARF metadata into binaries without it (e.g., stripped binaries), we recommend using the `dwarf-writer <https://github.com/immunant/dwarf-writer>`_ tool.  As an example of using ``dwarf-writer`` through its Docker image assuming the existence of a target (``target-binary.exe``) and metadata in the Anvill JSON format (``target-binary.exe.json``)::

  docker load -i dwarf-writer-docker.tar
  mkdir DwarfWriterData
  cp target-binary.exe target-binary.exe.json DwarfWriterData/
  docker run --rm -it -v `pwd`/DwarfWriterData:/DwarfWriterData dwarf-writer \
            --anvill /DwarfWriterData/target-binary.exe.json \
            /DwarfWriterData/target-binary.exe \
            /DwarfWriterData/target-binary-dwarf.exe

This will produce a version of the binary annotated with DWARF metadata in ``DwarfWriterData/target-binary-dwarf.exe``.

If you have the ``llvm-dwarfdump`` tool, you can use it to inspect the generated DWARF metadata.  The ``pate`` verifier will automatically take advantage of DWARF metadata hints unless it is directed to ignore them.

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

Acknowledgements
============
This material is based upon work supported by the Defense Advanced Research Projects Agency (DARPA) and Naval Information Warfare Center Pacific (NIWC Pacific) under Contract Number N66001-20-C-4027. Any opinions, findings and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the DARPA & NIWC Pacific.
