# Tests a simple loop invariant checker.

# Should return UNSAT.

run () {
  bap wp \
    --show=bir \
    --func=loop \
    --precond="(assert (bvule RDX #x000000007fffffff))" \
    --postcond="(assert (= RAX init_RDX))" \
    --loop-invariant="$(cat loop_invariant.smt)" \
    -- ./bin/main
}

run
