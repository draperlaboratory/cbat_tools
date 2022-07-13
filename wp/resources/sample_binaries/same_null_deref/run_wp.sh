#!/bin/sh

# This example demonstrates how CBAT can catch null dereferences when comparing
# binaries. If both binaries are identical and both dereference null, wp should
# return UNSAT because there are no new paths in the modified binary that would
# have more null dereferences relative to the original binary.

# Should return UNSAT

run () {
  bap wp \
    --func=null_deref \
    --check-null-derefs \
    -- ./bin/main_1 ./bin/main_2
}

run
