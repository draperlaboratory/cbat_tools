#!/bin/sh

# This tests WP's ability to unroll a simple loop.

# Should return UNSAT.

run () {
  bap wp \
    --num-unroll=5 \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000003))" \
    -- ./bin/main
}

run
