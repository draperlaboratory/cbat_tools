#!/bin/sh

# A binary that returns the value of a global variable.

# This tests matching a symbol in the original binary with that of the modified
# binary whose name has been updated similarly to retrowrite's instrumentation
# and whose address is at a different location.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --mem-offset \
    -- ./bin/main_1 ./bin/main_2
}

run
