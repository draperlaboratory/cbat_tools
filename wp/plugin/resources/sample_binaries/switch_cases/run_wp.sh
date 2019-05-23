set -x

compile () {
  bap_wp_dir=../../../lib/bap_wp
  wp_dir=../../../BAP/wp
  dummy_dir=../dummy

  make -C $bap_wp_dir install.local &&
  make -C $wp_dir clean             &&
  make -C $wp_dir                   &&
  make -C $dummy_dir                &&
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=process_message \
    --wp-check-calls=true
}

compile && run
