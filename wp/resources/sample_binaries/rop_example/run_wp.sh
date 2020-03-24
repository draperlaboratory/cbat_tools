# This tests a C file that has been compiled with GCC and with a tool that
# compiles the file into a ROP chain.

# Should return UNSAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-file1=main-original.bpj \
    --wp-file2=main-rop.bpj \
    --wp-inline=.*
}

compile && run
