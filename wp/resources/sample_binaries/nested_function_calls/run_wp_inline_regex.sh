set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-inline="foo|bar" --wp-func=main
}

compile && run
