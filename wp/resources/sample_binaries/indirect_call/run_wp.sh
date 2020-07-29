# This tests that an indirect call with a return has its stack pointer incremented
# as part of our indirect call spec.

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
    --wp-check-calls
}

compile && run
