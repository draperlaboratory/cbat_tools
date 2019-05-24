set -x

compile () {
    make
}

run () {
  bap main --pass=wp
}

compile && run
