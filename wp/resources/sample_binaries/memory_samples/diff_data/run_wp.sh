# Tests having a different value in the data section (at the same addresses)
# and the same values on the stack.

# The test accumulates that values in the data section and stack and stores
# the result in RAX. Because the data section has different values, the output
# RAX also differs.

# Should return SAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-final-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj
}

compile && run
