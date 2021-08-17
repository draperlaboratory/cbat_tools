# Tests a simple loop invariant checker.

# Should return UNSAT.

run () {
  bap wp \
    --func=sum \
    --optimization-level=3 \
    --postcond="$(cat property.smt)" \
    --loop-invariant="$(cat loop_invariant.smt)" \
    --pointer-reg-list=RSI \
    --show=bir,paths \
    -- ./bin/main
}

    # --precond="$(cat precond.smt)" \
#    --postcond="$(cat property.smt)" \
#    --loop-invariant="$(cat loop_invariant.smt)" \
#    --loop-invariant="$(cat dummy_invariant.smt)" \

run
