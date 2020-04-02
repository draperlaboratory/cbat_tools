# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# This test turns on the check-null-deref flag. With this flag, we assume that
# if each memory read in the original binary reads a non-null address, then
# that same memory read will also be non-null in the modified binary. In this
# case, since we are reading at an offset of 1 from the original, we cannot assume
# that address is non-null.

# Should return SAT

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
    --wp-check-null-deref
}

compile && run
