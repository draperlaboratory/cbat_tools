#!/bin/sh

# A test that gives RAX the value of RDI + 1. The two binaries differ in the
# order of the increment and move instructions, but have the same output.

# Runs WP with a postcondition that states that the end value of RAX in the
# modified binary is equal to the initial value of RDI in the original
# binary + 1.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --postcond="(assert (= RAX_mod (bvadd init_RDI_orig #x0000000000000001)))" \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
