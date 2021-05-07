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

- Our memory model assumes that the valid region of memory contains addresses
  above the stack pointer and 0x256 bytes below the lowest address of the stack.
  The stack grows downward in this case.



## Loop Unrolling ##

It is not entirely obvious how to unroll loops in an unstructured
language. Our strategy for unrolling loops is the following:

    1. Identify exits:
       We find post-dominators of strongly connected components, failing
       if more than one is found (for now).
    2. Compute preconditions for loop body:
       Taking the precondition for the exit node (or a trivial one if
       there are no exit nodes), we compute the precondition of
       targets of back edges, going through them n times if we unroll
       n times.

We use the environment hooks to implement this loop unrolling
mechanism, which makes it easy to swap out different implementations
(e.g. assuming that the loop executes *exactly* n times, or excluding
more than n iterations).



## Address Rewriting ##

One problem that we face is comparing pointers to symbols in the data and bss
sections across two binaries. Although two symbols may refer to the same value,
their locations can have different addresses. One way we tackle this problem is
by rewriting the concrete addresses in the modified binary.

First, we identify the symbols and their starting addresses in the data and
bss sections in both binaries using `objdump`. For each symbol, we calculate the
offset between their starting addresses. Then we visit the subroutine in
question from the modified binary. Every time we see a concrete bitvector, we
check to see if its falls within the address range of a symbol. If it does,
we subtract the corresponding offset from the bitvector, allowing it to match
that of the original binary.

This is unsound in that:

    1. It matches up the symbols by their names. WP does not check if the values
       of each corresponding pair of symbols actually have the same values.
    2. We are updating values in the modified binary. We are not performing
       the equivalence check on the exact binaries given by the user.
