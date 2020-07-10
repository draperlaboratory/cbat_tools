# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc (RDI) cannot be 2.
# As a result, the output of the function should be the same between both
# binaries.

# Should return UNSAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-precond="(assert (and (= #x0000000000000000 (bvand RDI_mod #xFFFFFFFF00000000)) (not (= RDI_mod #x0000000000000002))))"
}

compile && run
