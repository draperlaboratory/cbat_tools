This repository contains three BAP plugins, the value-set plugin, explicit-edge plugin,
and weakest-precondition plugin.
For details on the plugins and their flags, see:
- [the value-set README](./value_set/README.md),
- [the explicit-edge README](./explicit_edge/README.md), or
- [the weakest-precondition README](./wp/plugin/README.md).

For a general overview, read below:

Purpose
----------------------

CFG reconstruction, especially in the presence of indirect jumps, is a difficult task.
However, it is a basic prerequisite of a large class of static analyses.
While the existing BAP machinery recovers large portions of a binary's CFG, it does not
do so at indirect jumps.

A value-set analysis can be used to determine the possible values of the registers used
as jump targets. While the value-set analysis, like many others, is only sound on a
complete control flow graph, this strategy can produce a sound superset of the CFG by
iterating edge insertion with updating the value-set results.


Contents
---------------------

This project consists of

- **A value-set style analysis (VSA) and a CFG edge reconstruction
algorithm based on it.** The analysis uses circular linear progressions\[[1][1]\]\[[2][2]\] to
represent sets of bitvectors. Small sets are represented exactly to increase precision,
e.g. in the case where a jump target can be one of three locations. The analysis handles
all conversion between different representations internally and exposes a generic interface
for sets of words.

  * The edge reconstruction algorithm simply calls the VSA, inserts known
edges, and iterates this to a fixed point. Note that the edge reconstruction algorithm
is capped on the number of edges it inserts at a given indirect jump so as to prevent
blowup when a target is unknown. This can happen either because the VSA fails to deduce the
possible targets of the jump sufficiently precisely, there are a large number of possible
targets, or the jump target is dependent on the subroutine input (e.g. a return).

  * In many of the above cases, the results of the analysis should be considered unsound.
The precise condition necessary for the edge reconstruction to produce a supergraph of
the CFG is as follows: Any indirect jump that is unresolved by the edge insertion
must jump to the return address provided to the subroutine by its caller. This condition
could likely be weakened by incorporating a formula based approach similar to \[[1][1]\]
to track the stored return address and, where possible, prove via the analysis that it
is the only viable target of the jump.

- **A weakest-precondition computation (WP),** which verifies intra-procedural properties specified
using first-order logic, and resolved using the Z3 theorem prover. See the
[README](./wp/plugin) for the plugin for more details.

[1]: http://www.csa.iisc.ernet.in/~cplse/papers/srikant-memocode-2007.pdf
[2]: http://www.es.mdh.se/pdf_publications/3813.pdf


Build
------------------
Each plugin has a set of requirements needed before building. More info can be found in:
- [the value-set README](./value_set/README.md#build),
- [the explicit-edge README](./explicit_edge/README.md#build), or
- [the wp README](./wp/plugin/README.md#buildinstalltest).

Note that `explicit-edge` requires the `cbat_value_set` library installed in `value-set`.


Running the Passes
---------------------
The plugins define the `value-set`, `explicit-edge`, and `wp` BAP passes.
To run a pass in BAP, see `bap --help` or
- [the value-set README](./value_set/README.md#running-a-pass),
- [the explicit-edge README](./explicit_edge/README.md#running-a-pass), or
- [the wp README](./wp/plugin/README.md#invocation).


Disclaimer
-------------------
This work is sponsored by ONR/NAWC Contract N6833518C0107.  Its content does not necessarily reflect the position or policy of the US Government and no official endorsement should be inferred.

