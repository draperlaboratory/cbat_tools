set -x

compile () {
  make
}

run () {
    bap main --pass=wp --wp-inline="NONEXISTENTGARBAGE" --wp-func=main
}

compile && run
