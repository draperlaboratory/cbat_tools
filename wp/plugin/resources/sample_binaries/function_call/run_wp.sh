set -x

compile () {
  bap_wp_dir=../../../lib/bap_wp
  wp_dir=../../../BAP/wp

  make -C $bap_wp_dir install.local
  make -C $wp_dir clean
  make -C $wp_dir
  make
}

run () {
  bap main --pass=wp --wp-inline=true --wp-func=main
}

compile && run
