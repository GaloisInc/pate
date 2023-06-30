May 2023 Hackathon
========

Generate patched binary
^^^^^^^^^^^
Set the environment variable `CHALLENGE_DIR` to the root directory of the challenge problems repo::
  export CHALLENGE_DIR=/path/to/Challenge-Problems

Apply binary patch to challenge 10::
  cd demos/may-2023/challenge10
  make

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

Running PATE on challenge 10
-----------

Run the following command from the project root to 
analyze the original and patched challenge 10 binaries::
  docker run --rm -it -v `pwd`/demos/may-2023/challenge10:/challenge10 pate \
             --original /challenge10/challenge10.original.exe \
             --patched /challenge10/challenge10.patched.exe \
             -b /challenge10/challenge10.toml \
             --original-bsi-hints /challenge10/challenge10.json \
             --patched-bsi-hints /challenge10/challenge10.json \
             --original-csv-function-hints /challenge10/challenge10.csv \
             --patched-csv-function-hints /challenge10/challenge10.csv \
             -s transport_handler

The file `challenge10.toml` specifies additional metadata needed for
verificaiton. Specifically it instructs the verifier to start decoding
the in thumb mode.

The file `challenge10.json` contains symbol information extracted using
the BSI tool. This is necessary to identify functions that should use
stub semantics rather than be analyzed (e.g. libc calls).

The file `challenge10.csv` contains manually-defined symbol information
that was not automatically extracted from BSI tool. This is necessary to
handle some PLT stubs that were not identified.

The last line tells the verifier to start the analysis at the function
corresponding to the symbol `transport_handler`, which is known from
the BSI symbol data.

Once the verifier starts printing output it can be interrupted at any time by pressing
ENTER, but will continue processing in the background. Its results can then be
interactively inspected as they become available.

See `COMMANDS.rst` for an overview of all available commands and `REPL.rst` for a reference for
how to navigate the verifier repl.

Interactive Verification of Challenge 10
-----------

Step 1: Select the entry point and wait
^^^^^^^^^^^

 Select
`1` to start the analysis from the `transport_handler` function.::
  Choose Entry Point
  0: Function Entry segment1+0x3ba9
  1: Function Entry "transport_handler" (segment1+0x400c)
  ?> 1
  ....................
  0: Function Entry "transport_handler" (segment1+0x400c) (User Request) (!).
  ...

The verifier then proceeds to print out each analysis step until user input
is required. See "Toplevel Proof Nodes" in `REPL.rst`.

Step 2: Choose a synchronization point
^^^^^^^^^^^

During the analysis of the block starting at `0x4114` the analysis encounters
a control flow divergence. This is an expected result of the patch, which has
inserted a trampoline starting at `0x4128`. If the verifier is polling for output
this will appear automatically, otherwise if the output was interrupted we can
navigate to prompt by executing `top` followed by `goto_prompt`.::
  ?>goto_prompt
  Control flow desynchronization found at: GraphNode segment1+0x4114 [ via: "transport_handler" (segment1+0x400c) ]
  0: Choose synchronization points 
  1: Assert divergence is infeasible 
  2: Assume divergence is infeasible 
  3: Remove divergence in equivalence condition 
  4: Defer decision 
  ?>

We can check the context of this choice by executing `up` then `up` to see the node that
was being processed when this prompt was created.::
  ?>up
  ...
  ?>up
  segment1+0x4114 [ via: "transport_handler" (segment1+0x400c) ] (Widening Equivalence Domains)
  0: Widening Equivalence Domains
  1: Modify Proof Node
  2: Predomain
  3: Observably Equivalent
  4: Block Exits (?)
  5:   Call to: "puts" (segment1+0x33ac) Returns to: "transport_handler" (segment1+0x41b8) (original) vs. Call to: segment1+0x3dd24 Returns to: "transport_handler" (segment1+0x3dd44) (patched) (?)
  ?>

Here we see that, from `0x4114` there are disagreeing block exits. Specifically in the original program the block can exit
with a call to `puts` while the patched exits with a call to the anonymous function at `0x3dd24` (the inserted patch function).

To handle this, we need to instruct the verifier to perform a single-sided analysis on each program, and specify
the point at which control flow re-synchronizes. Specifically, we need to provide instruction addresses for the
original and patched programs where, if execution reaches these addresses, both programs will resume in lockstep
(i.e. all possible block exits (function calls) will be equal). We navigate to the prompt with `goto_prompt`
and select `0: Choose synchronization points`.

We are then prompted to provide a pair of program points by selecting from a list of instructions.
With a separate analysis we can determine that the required synchronization points are `segment1+0x3dd44 (patched)`
and `segment1+0x4128 (original)`. This is from the fact that, at `0x3dd44` (in the inserted trampoline), 
the patched program mirrors the branch instruction at `0x4128` in the original program.

Select these instructions from the list (one at a time) and the analysis will then continue.

Step 3: Generate an equivalence condition
^^^^^^^^^^^

The top-level nodes produced after this are suffixed by `(original)` or `(patched)`, indicating
which single-step analysis they correspond to. After some analysis, the verifier prompts with another
control flow desynchronization.::
  Control flow desynchronization found at: GraphNode segment1+0x4128 (original) vs. segment1+0x3dd44 (patched) [ via: "transport_handler" (segment1+0x400c) ]
  0: Choose synchronization points 
  1: Assert divergence is infeasible 
  2: Assume divergence is infeasible 
  3: Remove divergence in equivalence condition 
  4: Defer decision 
  ?>

This desynchronization correponds to the fact that control flow may still diverge between the original and patched
programs after the synchronization point we provided. This is exactly the intended result of our patch: after this
point the program control flows *may* be equal (i.e. in the case where the patch has simply recovered the original
behavior of the program), but they may also be unequal (i.e. in the case where the patch has modified the program behavior).

Since this desynchronization precisely describes the non-equal branching behavior, we can exclude it from
our analysis by asserting its negation as our generated *equivalence condition*. This is option 
`3: Remove divergence in equivalence condition `.

After some analysis a similar prompt is given (corresponding to the inverse branching behavior), which
we similarly handle by selecting `3` to assert the negation of this path condition.

The analysis then proceeds with this desynchronization omitted (and with a generated equivalence condition asserted
at the synchronization point).

Step 4: Strengthening the equivalence domain
^^^^^^^^^^^

After some time, the analysis eventually halts with a prompt indicating that a control flow difference
has been found at `0x4181`. With some investigation we can determine that this difference is actually *spurious*.
At the prompt, navigate to the toplevel node for `0x4181` via `up` then `up`, and select the option `2: Predomain`::
  ?>up
  ..
  ?>up
  segment1+0x4181 [ via: "transport_handler" (segment1+0x400c) ] (Widening Equivalence Domains)
  0: Widening Equivalence Domains
  1: Modify Proof Node
  2: Predomain
  3: Observably Equivalent
  4: Block Exits (?)
  5:   Call to: "err" (segment1+0x33ec) Returns to: "transport_handler" (segment1+0x4191)
  6:   Call to: "err" (segment1+0x33ec) Returns to: "transport_handler" (segment1+0x4191) (original) vs. Branch to: "transport_handler" (segment1+0x402d) (patched) (?)  
  ?>2

The output here indicates that, although control flow is synchronized between the programs, several registers as well
as global memory values are excluded from the equivalence domain (i.e. not known to be necessarily equivalence at this point).

The source of this inequivalence can be traced to the instruction immediately following the synchronization point
at `0x412a` (`top` then `25` then `2`). At this point, the equivalence domain has excluded r0-r7 as well as the stack pointer,
and several stack slots.

The source of this (spurious) inequivalence is a result of the trampoline saving and then restoring these registers
onto the stack before resuming normal control flow. The analysis has not retained enough context about the trampoline
execution to automatically prove that this save/restore operation is sound.

We can instruct the verifier to strengthen the equivalence domain by explictly *asserting* that, at this program point,
these registers are necessarily equivalent between the original and patched programs.

At the node for `0x412a` (`top` then `25`), select the option `1: Modify Proof Node`. From this list we simply
want to add an asserting by selecting `1:   Assert condition`.

After making this decision, we are presented with the same control flow desynchronization prompt, which we
now defer by selecting `4: Defer decision`, which will then present the prompt for the assertion we wish to add::
  Include Register:
  0: r0
  1: r1
  2: r13
  3: r2
  4: r3
  5: r4
  6: r5
  7: r7
  8: Include Remaining Registers
  9: Exclude Remaining Registers
  ?> 8

This is the list of registers which were *excluded* from the equivalence domain from `0x412a` Select `8` to include
all of the given registers. This *asserts* that all of the user registers are necessarily equal between the original
and patched programs when they both reach `0x412a`.

The analysis then proceeds by propagating the assertion up several nodes (indicated by the `Propagating Conditions` status),
which is then eventually discharged. The subsequent proof nodes are then re-checked under this new assertion, and
correspondingly strengthened equivalence domain.

Step 5: Propagating and interpreting the equivalence condition
^^^^^^^^^^^

The analysis is now able to finish, proving that the programs are exactly equivalent under
the generated equivalence condition. By default the condition is only asserted at exactly
the location it is needed, however it can also be *propagated* to the entry point, in order
to compute a sufficient condition at the beginning of the function call.

To do this, we navigate to the synchronization node (`top` then `57`) where we can see
that an equivalence condition has been assumed. However this is only in terms of the
condition registers at this point. Select `1: Modify Proof Node` and then `21:   Propagate fully`.

Then select `2: Handle pending refinements` at the next prompt to handle the requested action.
Once finished, the resulting equivalence condition can be examined by navigating to the node
corresponding to the function entry point for `transport_handler`.