# A test that gives RAX the value of RDI + 1. The two binaries differ in the
# order of the increment and move instructions, but have the same output.

# Runs WP with a postcondition that states that the end value of RAX in the
# modified binary is equal to the initial value of RDI in the original
# binary + 2, which is impossible.

# Should return SAT

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
    --wp-postcond="(assert (= RAX_mod (bvadd init_RDI_orig #x0000000000000002)))"
}

compile && run
