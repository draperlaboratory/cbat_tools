compile() {
        make
}

run() {
        bap main --pass=wp --wp-num-unroll=2 --wp-trip-asserts

}

clean() {
        make clean
}

clean && compile && run
