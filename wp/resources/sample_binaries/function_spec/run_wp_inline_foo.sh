set -x

compile () {
  make
}

run () {
    bap main --pass=wp --wp-inline="foo" --wp-func=main
}

compile && run
