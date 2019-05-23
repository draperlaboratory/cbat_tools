# Design decisions for the BIL WP compuation #

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
