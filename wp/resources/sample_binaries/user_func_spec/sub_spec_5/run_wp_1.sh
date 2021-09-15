# Should return SAT: we provide a spec only for g, which means f can still return 0x67 and we can trip the assert

run () {
  bap wp \
    --func=main \
    --precond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --postcond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main
}

run
