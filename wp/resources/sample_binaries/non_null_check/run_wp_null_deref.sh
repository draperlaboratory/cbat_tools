#!/bin/sh

# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# This test turns on the check-null-deref flag. With this flag, we assume that
# if each memory read in the original binary reads a non-null address, then
# that same memory read will also be non-null in the modified binary. In this
# case, since we are reading at an offset of 1 from the original, we cannot assume
# that address is non-null.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --check-null-derefs \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
