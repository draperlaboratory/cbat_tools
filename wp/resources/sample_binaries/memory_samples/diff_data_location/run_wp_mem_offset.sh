# Tests having different locations for the data section and same values on the
# stack. The binaries are the same except for the location of val.

# This test turns on the mem_offset flag, which equates the memory values of the
# original binary with that of the modified binary at an offset.

# Should return UNSAT

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
    --wp-file2=main_2.bpj \
    --wp-mem-offset
}

compile && run
