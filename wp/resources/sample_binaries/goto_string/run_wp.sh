set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-func=main --wp-print-path=true
}

compile && run
