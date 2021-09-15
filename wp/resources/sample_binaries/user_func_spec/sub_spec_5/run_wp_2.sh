# Should return UNSAT: we can trip neither assert because both f and g have postcondition RAX=61

run () {
  bap wp \
    --func=main \
    --precond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --postcond="(assert (= (bvand RDI #xFFFFFFFF00000000) #x0000000000000000))" \
    --user-func-specs="f,(assert true),(assert (= RAX #x0000000000000061));g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main
}

run
