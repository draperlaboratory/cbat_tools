# main:
#     mov     rax, 9
#     mov     rdi, 1
#     ret
# .end:

# Should return SAT

# run
run () {
  bap wp \
    --func=main \
    --show=paths \
    --postcond="(assert (= RAX (bvmul init_RDI RDI)))" \
    -- main
}

run
