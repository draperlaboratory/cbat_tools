# A simple test where the output of a function is a pointer that contains
# different values. WP is able to catch that the output varies between the
# two binaries. In this case, main_1 returns a 5 and main_2 returns a 6.

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj
}

compile && run
