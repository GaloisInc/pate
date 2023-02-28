February 2023 Evaluation
========

Modified Challenge Binaries
------------

This directory contains modified patches for challenges 9 and 10 for the purposes
of demonstrating the PATE verification tool. These modifications were necessary
to remove instructions that are not yet supported, as the verifier currently
does not have the ability to analyze binaries that contain unrecognized instructions.

Generate patched binaries
^^^^^^^^^^^
Set the environment variable `CHALLENGE_DIR` to the root directory of the challenge problems repo::
  export CHALLENGE_DIR=/path/to/Challenge-Problems

Apply binary patches to challenges 9 and 10::
  cd demos/feb-2023/challenge9
  make
  cd ../challenge10
  make

Challenge 9 Modifications
^^^^^^^^^^^
Removed vector instructions, which are currently unsupported by the ARM semantics.

* vmov
* vcvt
* vdiv
* vcmpe
* vmrs

This effectively removes the branch introduced by challenge 8, since it
uses floating point arithmetic to calculate the check.

Challenge 10 Modifications
^^^^^^^^^^^^
Removed instructions specific to the PPC e500 core, which are currently unsupported
by the PPC semantics.

* efscfui
* efsdiv

The above modifications were performed in order to support analysis of
the `transport_handler` function, but more changes would be needed to
support analysis of the entire binary.

Building the PATE verification tool
-----------

From the root directory of the project, build the Docker image with the command::

  docker build . -t pate

This is expected to take a few hours the first time in order to build the
semantics for PPC and ARM.

Next, run the verifier from the docker image to check that it has been
built correctly ::

  docker run --rm -it -p 5000:5000 pate --help

This should display the list of available command line options.

Running PATE on challenge 9
-----------

Run the following command from the project root to 
analyze the modified challenge 9 binaries::
  docker run --rm -it -v `pwd`/demos/feb-2023/challenge09:/challenge09 pate \
             --original /challenge09/challenge09.original.exe \
             --patched /challenge09/challenge09.patched.exe \
             -b /challenge09/challenge09.toml \
             --original-bsi-hints /challenge09/challenge09.json \
             --patched-bsi-hints /challenge09/challenge09.json \
             -s transport_handler

The file `challenge09.toml` specifies additional metadata needed for
verificaiton. Specifically it instructs the verifier to start decoding
the in thumb mode.

The file `challenge09.json` contains symbol information extracted using
the BSI tool. This is necessary to identify functions that should use
stub semantics rather than be analyzed (e.g. libc calls).

The last line tells the verifier to start the analysis at the function
corresponding to the symbol `transport_handler`, which is known from
the BSI symbol data.

Once the verifier starts printing output it can be interrupted at any time by pressing
ENTER, but will continue processing in the background. Its results can then be
interactively inspected as they become available.

See `COMMANDS.rst` for an overview of all available commands.

Interactive Verification of Challenge 9
-----------

Step 1: Generate an equivalence condition
^^^^^^^^^^^

The PATE verifier requires some user input in order to determine how
to synchronize control flow between the given binaries in the case where
they diverge significantly. When running challenge 9, the verifier will
produce 6 top-level results before then asking the user for input for 
result 7. Execute `top` to see the current top-level state.::
  ?>top
  <Toplevel>
  ...
  7: 0x11d60 (original) [ via: "transport_handler" (0x11c9c) (original) ] (?)
  ?>

Here the verifier has identified a control flow divergence in the block
starting at `0x11d60`. To address this, the analysis has been split to
independently consider the original and patched binaries. This is just
prior to the jump that was inserted for the patch.

The verifier now asking at which block the control flow should converge again.
Go to the prompt by executing `goto_prompt` to see the list of blocks to select from::
  ?>goto_prompt
  Choose a synchronization point:::[node]
  0: Function Entry "transport_handler" (0x11c9c) (patched)
  1: 0x11cba (patched) [ via: "transport_handler" (0x11c9c) (patched) ]
  ...
  20: 0x11d66 (patched) [ via: "transport_handler" (0x11c9c) (patched) ]
  ...
  45: Return "transport_handler" (0x11c9c) (patched)
  ?>

Select option `20` to specify `0x11d66` as the synchronization point
(i.e. where the trampoline returns to).::
  ?>20
  ...
  Use same PC for original binary?::[bool]
  0: : True
  1: : False
  ?>

The verifier now asking if the address provided for the synchronization point
is the same in the original binary. In general the programs may re-synchronize
control flow, have different program counters. In this case, both programs
synchronize at the same address, therefore select `0` to indicate `True`::
  ?>0
  ...
  Continue analysis after resynchronization?::[bool]
  0: : True
  1: : False
  ?>

The verifier now asking if it should continue its analysis after this
synchronization point, or if it should stop and attempt to generate an
equivalence condition immediately after control flow re-synchronizes.
Select `1` for `False`::
  ?>0
  ...
  Include Register:::[registerChoice]
  0: _PC
  1: r2
  2: r4
  3: r5
  4: r7
  5: __BranchTaken
  6: Include Remaining Registers
  7: Exclude Remaining Registers
  ?>

At this point the verifier has completed its analysis of the original
program, up to the synchronization point, and has found that the given
registers have been modified between the divergence point and synchronization
(i.e. between the instructions at `0x11d60` and `0x11d66`).

To compute an equivalence condition, we can select any of these registers
to be considered mandatory in the resulting equivalence domain. Select
`7` to not include any additional registers::
  ?>7
  ...
  Include Register:::[registerChoice]
  0: PSTATE_C
  1: _PC
  2: r0
  3: r1
  4: r13
  5: r14
  6: r2
  7: r3
  8: r4
  9: r5
  10: r7
  11: Include Remaining Registers
  12: Exclude Remaining Registers
  ?>

Here the verifier has completed the analysis of the patched program
up to the synchronization point (i.e. following the control flow through
the trampoline) and has determined that these registers may be unequal 
between the original and patched binaries at the synchronization point.

Select r7 by entering `10`. This tells the verifier to enforce the property
that GPR 7 has the same value in the original and patched binaries at the 
beginning of the instruction at `0x11d66`. This is enforced by computing
a sufficient *equivalence condition* and propagating this backwards
to the beginning of the function (i.e. the entry point to `transport_handler`).


Step 2: Generate an equivalence condition
^^^^^^^^^^^

Currently the verifier is unable to generate a sufficient equivalence condition
to satisfy the refined equivalence domain from Step 1. 
At the moment, an error is therefore raised and the verifier stops its analysis.

This is a known limitation with the equivalence condition propagation and we
are working to address it in the following ways:
  1. Refine the equivalence condition propagation to support threading 
    restricted equivalence domains.
  2. Allow users to provide an equivalence condition: either
    as a refinement of an automatically-derived condition or manually
    derived.

We are prioritizing point 2 to mitigate the risk of point 1 taking more
time than the evaluation would allow.

Step 3: Verify local equivalence given the condition
^^^^^^^^^^^

Once the mitigation in Step 2 is complete we will update this section to
include instructions for how to run the verifier with that equivalence condition
assumed. The expected result is that, given a sufficient equivalence condition,
the verifier will be able to establish *local* equivalence of the `transport_handler`
function.


Step 4: Verify global equivalence given the condition
^^^^^^^^^^^

Using the result from Step 3, the verifier will then be able to expand the
equivalence analysis to the entire program (i.e. starting from `main`).
It will verify that the original and patched binaries are *observably* equivalent,
under the assumption that the equivalence condition established in Step 2 always
holds when `transport_handler` is called.

Similar to Step 3, we will update this section to include instructions for how
to run the verifier in order to perform this global analysis.

Interactive Verification of Challenge 10
-----------

Run the following command from the project root to 
analyze the modified challenge 10 binaries::
  docker run --rm -it -v `pwd`/demos/feb-2023/challenge10:/challenge10 pate \
             --original /challenge10/challenge10.original.exe \
             --patched /challenge10/challenge10.patched.exe \
             -s transport_handler

The analysis will proceed similar to challenge 9, however the user will need to
interactively provide an alternative synchronization point that depends on the specific
implementation of the supplied patch (see Step 1 for challenge 9 where `0x11d66` was provided
as the synchronization point).