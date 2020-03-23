set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=main \
    --wp-postcond="(assert (= RAX_mod (bvadd init_RDI_orig #x0000000000000002)))"
}

compile && run
