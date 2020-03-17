set -x

compile () {
  make
}

run () {
    # This succeeds!
    # bap main --pass=wp --wp-inline=.* --wp-func=main
    bap main --pass=wp --wp-func=main
}

compile && run
