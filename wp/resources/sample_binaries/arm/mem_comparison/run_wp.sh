#!/bin/sh

# This tests that we can properly model memory for ARM binaries.

# A test where the function foo_get indexes the array foo with length 10. The
# address of the memory read is different between the two binaries.

# Should return SAT

run () {
  bap wp \
    --show=bir,paths \
    --func=foo_get \
    --compare-post-reg-values=R0,R1,R4,R5,R6,R7,R8,R9,R10,R11 \
    -- ./bin/main_1 ./bin/main_2
}

run
