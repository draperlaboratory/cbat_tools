# Should return SAT, since (true /\ (true => false)) is false, which is SAT

run () {
  bap wp \
    --func=main \
    --show=precond-smtlib \
    --postcond="(assert false)" \
    --user-func-spec="g,(assert true),(assert true)" \
    -- ./bin/main
}

run
