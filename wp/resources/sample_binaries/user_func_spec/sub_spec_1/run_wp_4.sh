# Should return SAT, since (true /\ (true => false)) is false, which is SAT
# Note: This example would have returned UNSAT if the --user-func-specs flag
# weren't used. So we turn an UNSAT into SAT with the --user-func-specs flag.

run () {
  bap wp \
    --func=main \
    --show=precond-smtlib \
    --postcond="(assert true)" \
    --user-func-specs="g,(assert false),(assert true)" \
    -- ./bin/main
}

run
