set -x

compile () {
  make
}

run () {
    # This succeeds!
    # bap main --pass=wp --wp-inline=true --wp-func=main
    bap main --pass=wp --wp-inline=false --wp-func=main
}

compile && run
