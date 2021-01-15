# Should return SAT, since (true /\ (true => false)) is false, which is SAT

run () {
  bap wp \
    --func=main \
    --postcond="(assert false)" \
    --user-func-spec="g,(assert true),(assert false)" \
    -- main
}

run
