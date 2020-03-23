set -x

compile () {
  make
}

run () {
  bap verifier_assume_unsat --pass=wp
}

compile && run
