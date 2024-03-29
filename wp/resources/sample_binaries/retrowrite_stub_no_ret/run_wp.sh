#!/bin/sh

# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This tests the __afl_maybe_log spec that it is the callee's
# responsibility to pop the stack pointer.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --fun-specs=afl-maybe-log \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
