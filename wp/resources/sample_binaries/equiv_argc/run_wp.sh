# The modified version of this test adds a check to argc and returns a
# different value if true. WP is able to determine that this is the case when
# argc is 2. (RDI = 2)

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-final-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj
}

compile && run
