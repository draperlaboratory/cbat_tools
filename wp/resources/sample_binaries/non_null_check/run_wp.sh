# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# In this comparison with the default flags, we are just comparing the output
# register RAX between the two binaries. Since both do not write to RAX, the
# property that RAX are equal at the end of execution holds.

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
    --wp-file2=main_2.bpj
}

compile && run
