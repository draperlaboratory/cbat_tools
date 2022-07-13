#!/bin/sh

# in the case we do not unroll the loop all the way and terminate early
# expected behavior is to not be affected by the loop. See issue #236

# Should return SAT

run() {
  bap wp \
    --func=foo \
    --num-unroll=2 \
    --postcond="(assert (not (= RAX #x0000000000000005)))" \
    --no-byteweight \
    -- ./bin/main_1
}

run
