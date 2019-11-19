set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-inline \
    --wp-file1=csmith-10684.bpj \
    --wp-file2=csmith-16812.bpj
}

compile && run
