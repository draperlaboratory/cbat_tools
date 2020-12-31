run () {
  bap wp \
    --func=main \
    --show=paths \
    --precond="(assert (= RDI #x0000000000000007))"\
    --postcond="(assert (= RAX (bvmul #x0000000000000007 RDI)))" \
    --user-func-spec="foo,(assert (= RDI #x0000000000000007)),(assert (= RAX (bvmul foo_init_RDI RAX)))" \
    -- main
}

run
