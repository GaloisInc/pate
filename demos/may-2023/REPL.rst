Guide for interacting with the PATE interactive repl
========

Overview
--------
See `COMMANDS.rst` for an overview of the commands available at the repl.

Entry Point
--------

Once the REPL has started, the first step of the analysis is to select an entry point to
start from. By default the options are either the entry point provided
by the ELF header, or any function symbol provided with `-s`::
  Choose Entry Point
  0: Function Entry 0xdead
  1: Function Entry "my_fun" (0xfeed)
  ?> 1

Toplevel Output
-----

The toplevel of the interactive repl (reachable via the `top` command) is
a list of all analysis steps that were taken, starting from the selected
entry point. For example, if a function `my_fun` calls `my_sub_fun`, we might see the following toplevel
output.


```
0: Function Entry "my_fun" (0xfeed) (User Request)
1: Function Entry "my_sub_fun" (0xdeef) [ via: "my_fun" (0xfeef) ]  (Widening Equivalence Domains)
2: 0xdeff [ via: "my_sub_fun" (0xdeef) <- "my_fun" (0xfeed) ] (Widening Equivalence Domains)
4: Return "my_sub_fun" (0xdeef) (Widening Equivalence Domains)
5: 0xfeef [ via: "my_sub_fun" (0xdeef) <- "my_fun" (0xfeed) ] (Widening Equivalence Domains)
4: Return "my_fun" (0xfeed) (Widening Equivalence Domains)
```


Toplevel Proof Nodes
-----

Each pair of address and calling contexts defines a unique toplevel proof "node". A given address and context
may appear multiple times in the toplevel list, corresponding to each individual time that the address/context 
pair was analyzed. The latest (highest-numbered) entry corresponds to the
most recent analysis of an address/context. Consider the second element of the list in the previous section.

`2: 0xdeff [ via: "my_sub_fun" (0xdeef) <- "my_fun" (0xfeed) ] (Widening Equivalence Domains)`

The components of this are as follows:
  * `2:` - the number of this node, enter at the prompt to navigate to it
    and see a detailed view of the analysis step
  * `0xdeff` - the address that this analysis started from
  * `[ via: "my_sub_fun" (0xdeef) <- "my_fun" (0xfeed) ]` -
    the calling context for this node, shown as the trace of function calls taken on the path
    to it (most recent call is first, left-to-right).
  * `(Widening Equivalence Domains)` - the reason this analysis step was taken. This is provided
    by whichever previous analysis step scheduled this node to be processed.


The contents of a node can be inspected by entering the corresponding number at the prompt. A toplevel node
contains sub-nodes corresponding to each possible "exit" that was discovered.

If we examine the first node (entering `1` at the prompt), we might see the following output:

```
Function Entry "my_fun" (0xfeed)
0: Widening Equivalence Domains
1: Modify Proof Node
2: Predomain
3: Observably Equivalent
4: Block Exits
5:   Call to: "my_sub_fun" (0xdeef) Returns to: "my_fun" (0xfeef)
```

Element 5 indicates that, starting at the function entry for `my_fun`, the original and patched
binaries both necessarily call `my_sub_fun` next, returning to the address `0xfeef` within `my_sub`.

Prompts
-----

Prompts are special proof nodes that affect the verifier behavior. After invoking `wait` (implicitly
invoked after providing any prompt input), the verifier prints completed nodes as they are finished until it becomes
blocked on a prompt. Once a prompt is available, `wait` implicitly navigates to it and presents the list
of available choices.

For example::
  Control flow desynchronization found at: GraphNode segment1+0x4114 [ via: "transport_handler" (segment1+0x400c) ]
  0: Choose synchronization points 
  1: Assert divergence is infeasible 
  2: Assume divergence is infeasible 
  3: Remove divergence in equivalence condition 
  4: Defer decision 
  ?>

At this point the analysis is blocked, waiting for input before proceeding.
Normal navigation commands can be used here (`up`, `top`, etc) to see the surrounding analysis context for this prompt.
However, navigating to any of these options (i.e. entering a number at this prompt) will take the corresponding
action and resume the analysis.

After input is provided for the prompt, the repl will implicitly navigate back to the toplevel and `wait`.

Ad-hoc choices
----

Some choices can be made ad-hoc, without blocking the analysis waiting for input. For example, most
toplevel nodes have a `Modify Proof Node` element, which presents a list of actions the user can request
to perform on the given node. Any requested actions will occur after the current analysis step is finished,
and often will then prompt the user for additional input.

