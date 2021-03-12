# CBAT

![CBAT Logo](docs/cbat_logo.png)

This repository contains tools built on top of
[BAP](https://github.com/BinaryAnalysisPlatform/bap).  To get started, see the
[CBAT documentation](https://draperlaboratory.github.io/cbat_tools/).

## Repository layout

To get started, see the documentation link above.  If you're digging into the code, this repository contains three tools in different directories as follows:

* [weakest-precondition](./wp) - An SMT-based weakest precondition (WP) analysis
  for BAP.  We use this both for single program analysis and for comparing the
  behavior of two programs.  The WP calculation verifies intra-procedural
  properties specified using first-order logic, and resolved using the Z3
  theorem prover.  To compare programs, the plugin combines them into a single
  program and uses the weakest precondition computation to find differences in
  the behavior of the two parts.

* [bildb](./bildb) - A debugger to step through binary programs lifted into
  BAP's intermediate language (BIL). The debugger lets users see the binary
  program as BAP sees them, in the simpler BIL syntax that is architecture
  independent. Users can step/skip forwards backwards, set breakpoints, read/set
  registers and memory locations, and so on.

* [value-set-analysis](./vsa) - A value set analysis (VSA) for BAP, and a tool
  to add missing edges to a CFG based on the value set analysis.  The CFG edge
  reconstruction is done by performing VSA to discover and add new edges to the
  CFG, and iterating to a fixpoint. The value set analysis itself can be used
  independently of the CFG reconstruction.  **Note:** The vsa plugin was built
  for earlier versions of BAP, and has not been updated for BAP 2.x.  It is
  known not to compile with current versions of BAP.  We plan to revisit it in
  the future.


## Disclaimer

This work is sponsored by ONR/NAWC Contract N6833518C0107.  Its content does not
necessarily reflect the position or policy of the US Government and no official
endorsement should be inferred.

