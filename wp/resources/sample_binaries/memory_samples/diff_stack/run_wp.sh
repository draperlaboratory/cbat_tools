# This test accumulates the values on the stack into RAX. THe two binaries have
# different values on the stack, giving different outputs.

# Should return SAT.

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj
}

compile && run
