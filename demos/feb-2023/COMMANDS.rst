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