set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-postcond="(assert (= RAX0 #x0000000000000000))"
}

compile && run
