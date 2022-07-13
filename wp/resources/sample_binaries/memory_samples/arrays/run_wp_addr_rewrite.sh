#!/bin/sh

# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# This test turns on the rewrite-addresses flag which rewrite the addresses
# found in the modified binary to match that of the original binary.

# Should return UNSAT

run () {
  bap wp \
    --func=foo_get \
    --rewrite-addresses \
    --compare-post-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15  \
    -- ./bin/main_1 ./bin/main_2
}

run
