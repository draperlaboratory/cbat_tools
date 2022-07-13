#!/bin/sh

# This test compares two binaries that have the same data section, but different
# BSS section.

# This test turns on the rewrite-addresses flag handling the different memory values in
# the previous test. Now the values of x and y are equal between the two
# binaries.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15 \
    --rewrite-addresses \
    -- ./bin/main_1 ./bin/main_2
}

run
