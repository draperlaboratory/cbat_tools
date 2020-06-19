# This test compares csmith.c compiled with different compilers.

# This test inlines all function calls rather than using function summaries.

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
    --wp-use-fun-input-regs \
    --wp-inline=.* \
    --wp-file1=csmith-10684.bpj \
    --wp-file2=csmith-16812.bpj
}

compile && run
