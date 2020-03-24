# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc (RDI) must be 2.
# In this case, the output value of the function will differ.

# Should return SAT.

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-precond="(assert (= RDI_mod #x0000000000000002)) (assert (= RDI_orig #x0000000000000002))"
}

compile && run
