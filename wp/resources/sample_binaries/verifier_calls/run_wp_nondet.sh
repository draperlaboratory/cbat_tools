set -x

compile () {
  make
}

run () {
  bap verifier_nondet --pass=wp
}

compile && run
