# Tests a simple loop invariant checker.

# Should return UNSAT.

run () {
  bap wp \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000005))" \
    --loop-invariant="$(cat loop_invariant.smt)" \
    -- ./bin/main
}

run
