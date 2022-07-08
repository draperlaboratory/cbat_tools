#!/bin/sh

# test that an unrolled loop does not effect resulting values

# Should return SAT with RDI=5

run() {
  bap wp \
    --func=foo \
    --num-unroll=3 \
    --postcond="(assert (not (= RAX #x0000000000000005)))" \
    --no-byteweight \
    -- ./bin/main_1
}

run
