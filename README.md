# CBAT

![CBAT Logo](cbat_logo.png)

This repository contains some tools built on top of BAP: there is a value set analysis (see [value-set](./value_set) and [explicit-edge](./explicit_edge)), a [weakest-precondition](./wp/plugin) analysis, and a [BIL debugger](./bildb).

For a general overview, read below.


Contents
---------------------

This repository consists of

- **A weakest-precondition computation (WP),** and a program comparison algorithm based on it. The WP calculation verifies intra-procedural properties specified
using first-order logic, and resolved using the Z3 theorem prover.  To compare programs, we combine them into a single program and use the weakest-precondition computation to find differences in the behavior of the two parts. See the [README](./wp/plugin) for more details.

- **A value-set style analysis (VSA)** and a CFG edge reconstruction algorithm based on it. The analysis uses circular linear progressions\[[1][1]\]\[[2][2]\] to represent sets of bitvectors. Small sets are represented exactly to increase precision, e.g. in the case where a jump target can be one of three locations. The analysis handles all conversion between different representations internally and exposes a generic interface for sets of words.

  * The edge reconstruction algorithm simply calls the VSA, inserts known edges, and iterates this to a fixed point. Note that the edge reconstruction algorithm
is capped on the number of edges it inserts at a given indirect jump so as to prevent blowup when a target is unknown. This can happen either because the VSA fails to deduce the possible targets of the jump sufficiently precisely, there are a large number of possible targets, or the jump target is dependent on the subroutine input (e.g. a return).

  * In many of the above cases, the results of the analysis should be considered unsound. The precise condition necessary for the edge reconstruction to produce a supergraph of the CFG is as follows: Any indirect jump that is unresolved by the edge insertion must jump to the return address provided to the subroutine by its caller. This condition could likely be weakened by incorporating a formula based approach similar to \[[1][1]\] to track the stored return address and, where possible, prove via the analysis that it is the only viable target of the jump.

- **A BIL Debugger (bildb)** a BIL debugger that can be used to debug binaries lifted to BAP's intermediate language (BIL).


[1]: http://www.csa.iisc.ernet.in/~cplse/papers/srikant-memocode-2007.pdf
[2]: http://www.es.mdh.se/pdf_publications/3813.pdf


Disclaimer
-------------------
This work is sponsored by ONR/NAWC Contract N6833518C0107.  Its content does not necessarily reflect the position or policy of the US Government and no official endorsement should be inferred.

