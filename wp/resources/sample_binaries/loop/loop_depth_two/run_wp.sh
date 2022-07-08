#!/bin/sh

# nested loop test two levels deep
# both loops are preserved based on cfg.  Expected value of RAX (j) should be 3
# RAX (j) ends as 2 and not 3.
# Note that by looking at the CFG and compiling with O0, both loops do exist.

# Should return UNSAT

# this is SAT but should be unsat since RAX should be 3
run_sat() {
  bap wp \
    --func=foo \
    --num-unroll=18 \
    --postcond="(assert (not (= RAX #x0000000000000002)))" \
    --no-byteweight \
    -- ./bin/main
}

# this is UNSAT but should be sat since RAX should be 3 at the end of execution
run_unsat() {
  bap wp \
    --func=foo \
    --num-unroll=18 \
    --postcond="(assert (not (= RAX #x0000000000000003)))" \
    --no-byteweight \
    -- ./bin/main
}

run_unsat
