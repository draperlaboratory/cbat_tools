# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)

run () {
  bap wp \
    --func=main \
    --precond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --postcond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000067))" \
    --trip-assert \
    -- ./bin/main
}

run
