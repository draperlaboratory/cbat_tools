# The modified binary adds a null check after the call to malloc. In the case
# that malloc returns NULL, the modified binary will hit an assert_fail.

# Should return SAT.

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
    --wp-trip-asserts \
    --wp-fun-specs=verifier_nondet
}

compile && run
