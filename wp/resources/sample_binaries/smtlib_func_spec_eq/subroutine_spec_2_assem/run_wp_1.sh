# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- main
}

run
