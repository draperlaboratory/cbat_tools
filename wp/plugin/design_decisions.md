# Design decisions for the BIL WP computation #

## Unsound design decisions ##

- The memory access is represented as a map from addr_size to bytes
  (or some smaller word size).
  When accessing words of size k bytes, it reads the first byte,
  increments, etc. k times, without accounting for arithmetic overflow.

- We do not handle endianness in memory reads or writes

- We do not correctly handle preconditions from indirect jumps: we do
  not evaluate the possible targets of the jump, and so cannot find
  all possible pre-conditions to that jump. Solving this can be quite finicky.

- We do not correctly handle calls: no effort is made to correctly
  update the variables modified by the call, in particular we assume
  nothing was modified.

- Loop invariants are not computed, we unroll the loops a set number
  of times (default 5, but user-configurable). See the relevant
  section.
  
  
  
## Loop Unrolling ##

It is not entirely obvious how to unroll loops in an unstructured
language. Our strategy for unrolling loops is the following:

    1. Identify exits:
       We find post-dominators of strongly connected components, failing
       if more than one is found (for now).
    2. Compute preconditions for loop body:
       Taking the precondition for the exit node (or a trivial one if
       there are no exit nodes), we compute the precondition of
       targets of back edges, going through them n times if we unfold
       n times.

We use the environment hooks to implement this loop unfolding
mechanism, which makes it easy to swap out different implementations
(e.g. assuming that the loop executes *exactly* n times, or excluding
more than n iterations).
