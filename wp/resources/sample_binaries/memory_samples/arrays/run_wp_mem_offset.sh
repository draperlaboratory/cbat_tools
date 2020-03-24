# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# This test turns on the mem_offset flag, which equates the memory values of the
# original binary with that of the modified binary at an offset. However, since
# foo has a length of 10, if the input to foo_get is greater than or equal to 10,
# we are indexing outside of the array, getting undefined behavior.

# Should return SAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=foo_get \
    --wp-output-vars=RAX,RBX,RSP,RBP,R12,R13,R14,R15 \
    --wp-mem-offset

}

compile && run
