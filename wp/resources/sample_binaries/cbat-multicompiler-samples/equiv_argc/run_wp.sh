# This test compares equiv_argc that has been compiled with different compilers.

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
    --wp-file1=equiv_argc-6404.bpj \
    --wp-file2=equiv_argc-6487.bpj
}

compile && run
