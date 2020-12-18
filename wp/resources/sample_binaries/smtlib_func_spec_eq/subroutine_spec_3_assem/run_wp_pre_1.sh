# main:
#     mov     rax, 9
#     mov     rdi, 1
#     ret
# .end:

# Should return UNSAT, since RDI=9 ensures us that the right value for RDI is picked
# to ensure RAX = init_RDI * RDI

# run
run () {
  bap wp \
    --func=main \
    --show=paths \
    --postcond="(assert (= RAX (bvmul init_RDI RDI)))" \
    --precond="(assert (= RDI #x0000000000000009))" \
    -- main
}

run
