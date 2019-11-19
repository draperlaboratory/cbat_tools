set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-file1=equiv_argc-6404.bpj \
    --wp-file2=equiv_argc-6487.bpj
}

compile && run
