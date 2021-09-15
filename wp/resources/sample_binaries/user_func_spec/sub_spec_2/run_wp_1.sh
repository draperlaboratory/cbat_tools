# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)

run () {
  bap wp \
    --func=main \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000067))" \
    --trip-assert \
    -- ./bin/main
}

run
