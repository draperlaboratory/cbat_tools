# This example returns SAT when no --user-func-spec flag is included.
# This example returns UNSAT when the following --user-func-spec flag is added.

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main_1
}

run
