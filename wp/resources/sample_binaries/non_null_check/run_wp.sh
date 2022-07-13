#!/bin/sh

# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# In this comparison with the default flags, we are just comparing the output
# register RAX between the two binaries. Since both do not write to RAX, the
# property that RAX are equal at the end of execution holds.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
