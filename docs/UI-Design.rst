Requirements
============

The interactive UI for the PATE verifier should:

1. Provide an interactive view of the results streamed from the verifier
2. Enable a visually-assisted explanation of the proof structure used by the verifier
3. Help visually localize proof failures and relate them back to the program

Design
======

The major components will be:
- A console logging streaming output from the verifier on its progress
- A summary of results (verified, not verified, unknown)
- A detailed view of the currently-focused thing

The detailed view will be dependent on the currently selected object.  Some objects of interest include:
- Individual block pairs (drilling down into the side-by-side comparison of the two things being compared)
- A view of the proof structure (with the ability to focus on individual nodes, and especially on failures)

Console View
------------

The console view will show the top N (where N could be configurable, but could also just be a fixed amount) of the most recent events streamed from the verifier. Events include successful and unsuccessful verification attempts (along with associated metadata).  These are all of the events described in the ``Pate.Event`` module.

Summary View
------------

The summary view will provide an aggregate view of the verification process (and be continually updated as new information arrives).  This will include at least statistics on the number of successfully verified pairs, unsuccessfully verified pairs, and timeouts.

The summary should also include meta-statistics about the proof structure (e.g., number of nodes, size of obligations in a histogram).  This would serve as an entry point to the proof structure context (see below).

Detailed View
-------------

The detailed view will show different information depending on context.  When the context is a block pair (e.g., because the user clicked on a function address in the output window), the detail view should show detailed information about the block pair and their status.

Block Pairs
+++++++++++

To display a pair of blocks, each of the original and patched program slices should be represented using a cytoscape graph.  This will allow rendering the control flow edges between them.  We can identify the control flow edges by inspecting the macaw blocks, which are included in the information streamed to the frontend.

Each macaw block should have two rendering modes:
1. With full macaw IR detail
2. Reduced mode with just machine instructions (for clarity)

Conditional branches should be labeled with their edges (though this will be in terms of macaw IR instead of machine instructions, so conditions may appear flipped compared to the machine code instructions).

Each pair should be labeled with information about its frame conditions.

Proof Structure
+++++++++++++++

The full proof structure will be far too large to visualize except in the most trivial of cases.  To that end, the proof structure explorer should allow for on-demand expansion of the proof tree (fetching the data from the verifier instead of storing the whole tree in JS).

It should be able to localize failures in the graph, showing nodes around the failure to provide context.  That context could include the path to the program entry point.

In future iterations, this should include search.
