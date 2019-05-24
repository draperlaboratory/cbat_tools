set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-inline=true --wp-func=main
}

compile && run
