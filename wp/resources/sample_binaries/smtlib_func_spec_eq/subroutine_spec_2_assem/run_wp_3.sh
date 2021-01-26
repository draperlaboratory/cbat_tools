#This file should return SAT

run () {
bap wp \
    --func=main \
    --show=precond-smtlib \
    --user-func-spec="g,(assert true),(assert true)" \
    --trip-assert \
    -- main
    }

run
