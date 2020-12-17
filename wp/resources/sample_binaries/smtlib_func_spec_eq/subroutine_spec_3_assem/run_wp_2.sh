
# Should return SAT

run () {
  bap wp \
    --func=main \
    --show=paths \
    --postcond="(assert (= RAX (bvmul init_RDI RDI)))" \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000067))" \
    -- main
}

run
