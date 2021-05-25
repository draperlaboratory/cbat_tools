# Tests a simple loop invariant checker.

# Should return UNSAT.

run () {
  bap wp \
    --show=bir \
    --num-unroll=0 \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000003))" \
    --loop-invariant="$(cat loop_invariant.smt)" \
    -- ./bin/main
}

run
