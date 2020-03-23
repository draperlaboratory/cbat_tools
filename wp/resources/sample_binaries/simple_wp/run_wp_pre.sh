set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-precond="(assert (= RDI #x0000000000000002))"
}

compile && run
