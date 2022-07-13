#!/bin/sh

# This tests a loop without an invariant to check.

# Should return SAT.

run () {
  bap wp \
    --num-unroll=0 \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000003))" \
    -- ./bin/main
}

run
