# This test compares two binaries that have the same data section, but different
# BSS section.

# This test turns on the mem_offset flag handling the different memory values in
# the previous test. Now the values of x and y are equal between the two
# binaries.

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-final-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15  \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-mem-offset

}

compile && run
