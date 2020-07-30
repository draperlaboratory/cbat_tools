# This tests that an indirect call with no return does not have 
# its stack pointer incremented as part of our indirect call spec.

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
    --wp-function=indirect_call \
    --wp-check-calls \
    --wp-postcond="(assert (and (= RSP_orig (bvadd init_RSP_orig #x0000000000000008)) (= RSP_mod (bvadd init_RSP_mod #x0000000000000008))))"
}

compile && run
