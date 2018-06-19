This repository contains two BAP plugins, the value-set plugin and the explicit-edge plugin.
For details on the plugins and their flags, see [the value-set README](./value_set/README.md)
and [the explicit-edge README](./explicit_edge/README.md). For a general overview,
read below:

Purpose
----------------------

CFG reconstruction, especially in the presence of indicrect jumps, is a difficult task.
However, it is a basic prerequisite of a large class of static analyses.
While the existing BAP machinery recovers large portions of a binary's CFG, it does not
do so at indirect jumps.

A value-set analysis can be used to determine the possible values of the registers used
as jump targets. While the value-set analysis, like many others, is only sound on a
complete control flow graph, this strategy can produce a sound superset of the CFG by
iterating edge insertion with updating the value-set results.


Contents
---------------------

This project consists of a value-set style analysis (VSA) and a CFG edge reconstruction
algorithm based on it. The analysis uses circular linear progressions\[[1][1]\]\[[2][2]\] to
represent sets of bitvectors. Small sets are represented exactly to increase precision,
e.g. in the case where a jump target can be one of three locations. The analysis handles
all conversion between different representations internally and exposes a generic interface
for sets of words.

The edge reconstruction algorithm simply calls the VSA, inserts known
edges, and iterates this to a fixed point. Note that the edge reconstruction algorthim
is capped on the number of edges it inserts at a given indirect jump so as to prevent
blowup when a target is unknown. This can happen either because the VSA fails to deduce the
possible targets of the jump sufficiently precisely, there are a large number of possible
targets, or the jump target is dependent on the subroutine input (e.g. a return).

In many of the above cases, the results of the analysis should be considered unsound.
The precise condition necessary for the edge reconstruction to produce a supergraph of
the CFG is as follows: Any indirect jump that is unresolved by the edge insertion
must jump to the return address provided to the subroutine by its caller. This condition
could likely be weakened by encorporating a formula based approach similar to \[[1][1]\]
to track the stored return address and, where possible, prove via the analysis that it
is the only viable target of the jump.

[1]: http://www.csa.iisc.ernet.in/~cplse/papers/srikant-memocode-2007.pdf
[2]: http://www.es.mdh.se/pdf_publications/3813.pdf


Build
------------------
These plugins are built using OASIS.
Make sure to have OPAM and OASIS installed before building (OASIS can be installed via `opam install oasis`).
These plugins also require version 1.5.0 of BAP (currently the GitHub master branch).
For difficulties installing BAP, see the BAP build instructions.
The package `ppx_deriving` is also required for the value-set plugin.
To install, run `opam install ppx_deriving`.
Once BAP and `ppx_deriving` are installed, the script `build_both.sh` should build both plugins.


Running the Passes
---------------------
The plugins respectively define the `value-set` and `explicit-edge` BAP passes.
To run a pass in BAP, see `bap --help` or [the value-set README](./value_set/README.md)
and [the explicit-edge README](./explicit_edge/README.md).


Disclaimer
-------------------
This work is sponsored by ONR/NAWC Contract N6833518C0107.  Its content does not necessarily reflect the position or policy of the US Government and no official endorsement should be inferred.

