set -x

compile () {
  make -C ../../../BAP/wp && make
}

run () {
  bap main --pass=wp
}

compile && run
