# Should return SAT

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000067))" \
    --trip-assert \
    -- main
}

run
