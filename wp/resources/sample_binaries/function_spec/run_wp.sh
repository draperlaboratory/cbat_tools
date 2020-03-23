set -x

compile () {
  make
}

run () {
    bap main --pass=wp --wp-func=main
}

compile && run
