run () {
  bap wp \
    --func=main \
    --show=paths \
    --precond="(assert (= RDI #x0000000000000007))"\
    --postcond="(assert (= RAX (bvmul #x0000000000000007 RDI)))" \
    --user-func-spec="g,(assert (= RDI #x0000000000000007)),(assert (= RAX (bvmul init_RDI RDI)))" \
    -- main
}

run
