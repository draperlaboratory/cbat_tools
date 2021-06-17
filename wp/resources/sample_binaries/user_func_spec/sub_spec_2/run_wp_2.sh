# Should return UNSAT: since when RAX is not 0x67, we can't trigger assert(0)

run () {
  bap wp \
    --func=main \
    --precond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --postcond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main
}

run
