set -x

compile () {
  make
}

run () {
  bap verifier_assume_sat --pass=wp
}

compile && run
