Reference for commands for PATE interactive repl
========

Overview
--------
The PATE interactive repl allows a user to observe the output of the
verifier as it executes. Additionally it allows the user to provide
input when necessary.

The verifier starts its analysis at the entry point given on the command
line when it was launched (i.e. as a symbol with `-s` or the main entry point
defined by the ELF file, by default).

At the toplevel there will be a list of blocks, printed out as they
are analyzed. At any point this can be interrupted by pressing
<ENTER>, where the verifier will continue processing in the background, but
the user may now inspect any results that are currently available.

The output is a simple tree structure, where a node is selected by
entering its corresponding number at the prompt. After selecting a node,
its contents will be printed and nested nodes can then be selected. The
`up` command will move up the tree, and `top` will return to the toplevel.

Prompt
------
The prompt indicates the status of the current node as follows:

* `*>` current node still has some active task running
* `?>` current node requires user input
* `!>` current node has raised a warning
* `x>` current node has raised an error
* `>` current node, and all sub-nodes, have finished processing

Node Status
-----
Similar to the prompt, nodes may be printed with a suffix that indicates
some additional status as follows:

* `(*)` node still has some active task running
* `(?)` node requires user input
* `(!)` node has raised a warning
* `(x)` node has raised an error

A status suffix indicates that the node, or some sub-node, has the given status.
e.g. at the toplevel the prompt `x>` indicates that an error was thrown during
some block analysis, while the corresponding node for the block will have a `(x)` suffix.

Navigation Commands
-----
* <#> - navigate to a node, printing its contents
* up - navigate up one tree level
* top - navigate to the toplevel
* goto_err - navigate to the first leaf node with an error status
* next - navigate to the highest-numbered node at the current level


Diagnostic Commands
-----
* status - print the status of the current node
* full_status - print the status of the current node, without truncating the output
* ls - print the list of nodes at the current level
* wait - wait at the current level for more results. Exits when the node finishes, or
the user provides any input

Interactive Commands
-----

When the prompt is `?>`, the verifier is waiting for input at some sub-node.
To select an option, simply navigate (i.e. by entering a #) to the desired choice.

* goto_prompt - navigate to the first leaf node waiting for user input

Toplevel Output
-----

The toplevel of the interactive repl (reachable via the `top` command) is
a list of all analysis steps that were taken, starting from the selected
entry point. Here is an example output line:

`6: segment1+0x3fe4 [ via: "delete_connection" (segment1+0x3fcc) <- "transport_handler" (segment1+0x4068) ] (Widening Equivalence Domains)`

The components of this are as follows:
  * `6:` - the number of this node, enter at the prompt to navigate to it
    and see a detailed view of the analysis step
  * `segment1+0x3fe4` - the address that this analysis started from
  * `[ via: "delete_connection" (segment1+0x3fcc) <- "transport_handler" (segment1+0x4068) ]` -
    the calling context for this node, shown as the trace of function calls taken on the path
    to it (most recent call is first, left-to-right).
  * `(Widening Equivalence Domains)` - the reason this analysis step was taken. This is provided
    by whichever previous analysis step scheduled this node to be processed.

Each pair of address and calling contexts defines a unique node, but they may appear multiple
times in the toplevel list. Each entry corresponds to an individual analysis step, where nodes
may be re-analyzed any number of times. The latest (highest-numbered) entry corresponds to the
most recent analysis of a node.

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
