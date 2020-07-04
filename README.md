# CBAT

![CBAT Logo](cbat_logo.png)

This repository contains tools built on top of [BAP](https://github.com/BinaryAnalysisPlatform/bap). For details and instructions on how to get started with any of these tools, follow the the links below and see their respective READMEs.

* [weakest-precondition](./wp) - A tool to automatically check the relative correctness of two programs, based on a weakest-precondition computation (WP), and a program comparison algorithm based on it. The WP calculation verifies intra-procedural properties specified using first-order logic, and resolved using the Z3 theorem prover.  To compare programs, we combine them into a single program and use the weakest-precondition computation to find differences in the behavior of the two parts. 

* [value-set-analysis](./vsa) - A tool that can add missing edges to a CFG, using a value set analysis. The CFG edge reconstruction is done by performing VSA to discover and add new edges to the CFG, and iterating to a fixpoint. The value set analysis itself can be used independently of the CFG reconstruction, if the CFG reconstruction is not needed.

* [bildb](./bildb) - A debugger to step through binary programs lifted into BAP's intermediate language (BIL). The debugger lets users see the binary program as BAP sees them, in the simpler BIL syntax that is architecture independent. Users can step/skip forwards backwards, set breakpoints, read/set registers and memory locations, and so on.


## Disclaimer

This work is sponsored by ONR/NAWC Contract N6833518C0107.  Its content does not necessarily reflect the position or policy of the US Government and no official endorsement should be inferred.

