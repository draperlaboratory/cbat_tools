# Should return SAT since RAX would need to be 0x61 instead of 0x67 to be UNSAT

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000067))" \
    --trip-assert \
    -- ./bin/main_1
}

run
