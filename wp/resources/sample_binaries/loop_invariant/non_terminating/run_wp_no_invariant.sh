#!/bin/sh

# This tests a loop without an invariant to check.

# Should return SAT.

run () {
  bap wp \
    --num-unroll=0 \
    --func=loop \
    --postcond="(assert false)" \
    -- ./bin/main
}

run
