# This test compares csmith.c compiled with different compilers

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-use-fun-input-regs \
    --wp-file1=csmith-10684.bpj \
    --wp-file2=csmith-16812.bpj
}

compile && run
