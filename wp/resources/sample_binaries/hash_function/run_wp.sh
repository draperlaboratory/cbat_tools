# Trips an assert if a password hashes to the "special" value in a hashtable.

compile() {
        make
}

run() {
        bap main --pass=wp \
                --wp-function=perform_hash \
                --wp-inline=bad_hash \
                --wp-trip-assert

}

clean() {
        make clean
}

clean && compile && run
