# Value Set Analysis (VSA)

This project contains two BAP plugins:

* [value_set](./value_set/) - A value set analysis plugin.
* [explicit_edge](./explicit_edge/) - A CFG edge reconstruction plugin. 

See the READMEs for both plugins for more details, and instructions on how to get started.

The CFG edge reconstruction is based on the value set analysis. The value set analysis uses circular linear progressions\[[1][1]\]\[[2][2]\] to represent sets of bitvectors. Small sets are represented exactly to increase precision, e.g. in the case where a jump target can be one of three locations. The analysis handles all conversion between different representations internally and exposes a generic interface for sets of words.

  * The edge reconstruction algorithm simply calls the VSA, inserts known edges, and iterates this to a fixed point. Note that the edge reconstruction algorithm
is capped on the number of edges it inserts at a given indirect jump so as to prevent blowup when a target is unknown. This can happen either because the VSA fails to deduce the possible targets of the jump sufficiently precisely, there are a large number of possible targets, or the jump target is dependent on the subroutine input (e.g. a return). See the [explicit_edge](./explicit_edge/) README for details.

  * In many of the above cases, the results of the analysis should be considered unsound. The precise condition necessary for the edge reconstruction to produce a supergraph of the CFG is as follows: Any indirect jump that is unresolved by the edge insertion must jump to the return address provided to the subroutine by its caller. This condition could likely be weakened by incorporating a formula based approach similar to \[[1][1]\] to track the stored return address and, where possible, prove via the analysis that it is the only viable target of the jump.

[1]: http://www.csa.iisc.ernet.in/~cplse/papers/srikant-memocode-2007.pdf
[2]: http://www.es.mdh.se/pdf_publications/3813.pdf
