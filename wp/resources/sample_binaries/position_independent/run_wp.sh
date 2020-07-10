# This tests inlining a function that has been compiled with fPIC.
# init() returns different values, and if inlined properly, WP should be able
# to capture this.

# Should return SAT.

set -x

dummy_dir=../dummy

compile () {
  make FLAGS="-fPIC -shared"
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=example \
    --wp-inline=init
}

compile && run
