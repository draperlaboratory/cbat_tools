#Arbitrary change
# Should return UNSAT, since (true /\ (false => false)) is true, which is UNSAT

run () {
  bap wp \
    --func=main \
    --postcond="(assert false)" \
    --user-func-spec="g,(assert true),(assert false)" \
    -- ./bin/main
}

run

