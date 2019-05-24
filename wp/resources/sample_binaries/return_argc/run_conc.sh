set -x

compile () {
  make
}

run () {
    bap main \
        --pass=run \
        --run-entry-points=main \
        --conc-pre \
        --conc-subroutine=main \
        --conc-postcond="(assert (= RAX0 #x0000000000000000))"
}

compile && run
