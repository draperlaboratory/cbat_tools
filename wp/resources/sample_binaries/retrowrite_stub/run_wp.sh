# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This tests that the function spec for __afl_maybe_log
# properly pops the stack pointer at the end of the function.

# Should return UNSAT

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
    --wp-fun-specs=afl_maybe_log
}

compile && run
