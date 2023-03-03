#!/bin/sh

# test that an unrolled loop does not effect results in the comparative case

# Should return UNSAT

run() {
  bap wp \
    --func=foo \
    --num-unroll=3 \
    --postcond="(assert (= RAX_orig RAX_mod))" \
    --no-byteweight \
    --show=diagnostics \
    -- ./bin/main_1 ./bin/main_2
}

run
