set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=foo_get \
    --wp-output-vars=RAX,RBX,RSP,RBP,R12,R13,R14,R15

}

compile && run
