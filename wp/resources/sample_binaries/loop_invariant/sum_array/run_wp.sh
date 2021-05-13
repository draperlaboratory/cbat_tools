# Tests a simple loop invariant checker.

# Should return UNSAT.

run () {
  bap wp \
    --func=sum \
    --postcond="$(cat property.smt)" \
    --loop-invariant="$(cat loop_invariant.smt)" \
    --pointer-reg-list=RSI \
    --show=precond-smtlib \
    -- ./bin/main
}

#    --postcond="$(cat property.smt)" \
#    --loop-invariant="$(cat loop_invariant.smt)" \
#    --loop-invariant="$(cat dummy_invariant.smt)" \

run
