This document describes the requirements of the Patches Assured up to Trace Equivalence verifier. It also suggests some metrics by which the verifier can be evaluated.  This document describes the static verifier; the dynamic analysis components of our work are fundamental research, but will be integrated as possible.


Requirements
============
1. Build assurance that binary modifications are safe, or explain why they are not
1. Support the AArch32 and PowerPC binaries (with a focus on embedded systems)
  - Support the user mode subset of instructions (i.e., not system mode for OS/bootloader/hypervisor instructions)
2. Scale up to progressively more complex patches over the course of the program
3. Do not require any behavioral specifications of the patch or program being patched beyond the original binary
4. Accept advisory input from other teams
5. Explain verification results in terms programmers can understand

Assurance Commentary
--------------------
We sometimes imprecisely use the word "verifier" to describe our tool, as it is based on tools and techniques commonly used for program verification.  More precisely, our tool will build *assurance* around the correctness of a patch with respect to a model that we will document thoroughly during the development process.  However, it will never be sound and complete because the process of code discovery itself is neither sound nor complete.

Architecture Support Commentary
-------------------------------
While our tools will not support system level instructions, we will still be able to analyze binaries using those instructions by skipping the portions of the code using them. This should not be a significant barrier, as system level instructions (e.g., page table handling or interrupt manipulation) make up only a tiny portion of systems and are usually provided by an RTOS, rather than application logic.

Patch Complexity Commentary
---------------------------
We expect to scale our analysis to progressively more complex patches. Note that we do not necessarily measure the complexity of patches by the number of lines of code they touch; instead, we are primarily concerned with the scope of their impact.  To some extent, this reflects the difference between the size of a source-level patch versus a binary-level patch.  A very small source-level patch, when rendered as a binary, can have program-wide impacts (e.g., adding a field to a structure).  As a rough indicator of complexity, we think of patches as:

1. Changes scoped to a single function
   a. Changes that alter loop termination conditions
2. Changes in a function that affect its callees
3. Changes in a function that affect its callers
4. Correlated changes across multiple functions
5. Correlated changes across multiple programs

Note that (3) is less localized than (2), as it requires determining all of the possible sites at which a function is called, which is often very difficult in the presence of indirect function calls.


Metrics
=======

We are considering the following metrics for our static verification tools:

1. Time taken to verify a patch

   We expect that the time taken to verify patches will decrease over time. Note that these decreases are comparing the performance of the verifier on the same patch over; more complex patches will naturally take longer to verify. Also note that this metric may not progress monotonically in cases where the verifier gains the ability to make stronger equivalence statements (but at higher cost); these cases will be accompanied by explanations.

  This metric is measured in wallclock seconds

2. Size of programs that can be verified

   We expect that we will be able to verify patches against progressively larger programs over the course of the program.  Note that program size is not a perfect metric, as it is only generally correlated with complexity.  Some very large programs can be easy to verify, while some very small programs can be impossible to verify.  Much of the complexity relates to the control flow structure (e.g., heavy use of virtual dispatch in C++ will be more expensive to verify than normal function calls).

   This metric is measured in bytes of text section (or number of instructions)
   - The number of instructions can be difficult to compute precisely because small amounts of data are often mixed with code (e.g., for jump tables and ARM literal pools)
   - The relation to source lines of code is not clear or easy to compute without source code, but the number of machine instructions should be proportional in most cases

3. Size of patches that can be verified

   As discussed in the patch complexity summary above, patch complexity is not necessarily related to the size of the patch at the source level.  However, complexity is more closely related to the size of the binary patch (i.e., number of different or added bytes).  We should expect that the verifier can handle progressively larger binary differences.

   This metric is measured in bytes different or added between the original binary and patched binary

4. Number of basic block pairs that the verifier cannot verify or refute

   We expect that the verifier may fail to verify or refute pairs of blocks for a number of reasons including, but not limited to: disassembly failures, missing instruction semantics, or complex operations that cannot be automatically checked for equivalence due to undecidability.  While failures of this form would mean that a change cannot be completely verified, the verifier can nonetheless build assurance even in their presence (possibly augmented with dynamic testing).  We expect that the number of failures of this form should decrease as the verifier matures.

   This metric is measured in a count of basic block pairs

5. Amount of context pushed down from the entry point of the program

   The verifier operates in a top-down / bottom-up manner.  It pushes context down from the start of the program and uses that to inform bottom up generation of verification conditions, where top and bottom refer to the root and leaves of the call graph, respectively.  Pushing more context down from the entry point of the program will enable the verifier to generate more precise and smaller verification conditions, which should improve scalability.

   This metric could be measured in the number of facts pushed down to the leaves of the program
   - It may be useful to measure the complexity of the facts passed down, though the units of that metric are not currently obvious

6. Number of heuristic failures in frame generation

   The verifier uses a number of heuristics to compute separation frames for each basic block.  The heuristics are not trusted; instead, they are guesses that are later verified. These heuristics can fail in two ways:
   - They can be too strong (i.e., they require too much state to be preserved, when it is actually not preserved)
   - They can be too weak (i.e., insufficient to prove equivalence)

   Measuring the quality of the heuristics is difficult.  Ideally, the verifier should have heuristics that fail less as they are improved.  However, in an alternative interpretation, more failing heuristics may be good, as failures may guide the application of more precise, but expensive, heuristics that perform better.

   It is not clear how to measure this metric at this point

7. Quality of explanations for verification failures

   Ideally, the verifier should produce explanations that are understandable by domain experts (rather than reverse engineers).  The quality of explanations is highly subjective, but it could be measured by proxy in terms of characteristics of the explanations.  Good explanations should refer to program state that domain experts understand (i.e., not including register state or hidden state that is an artifact of machine code semantics).
