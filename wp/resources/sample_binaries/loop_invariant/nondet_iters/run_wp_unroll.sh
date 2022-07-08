#!/bin/sh

# This tests a loop without an invariant to check. WP can't determine how many
# times x is incremented, since the we iterate over the loop an arbitrary
# number of times.

# Should return SAT.

run () {
  bap wp \
    --num-unroll=5 \
    --func=loop \
    --precond="(assert (bvult RDX #x000000007fffffff))" \
    --postcond="(assert (= RAX init_RDX))" \
    -- ./bin/main
}

run
