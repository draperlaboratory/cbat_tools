compile() {
        make
}

run() {
        bap main --optimization-level=3 --pass=wp --wp-num-unroll=5

}

clean() {
        make clean
}

clean && compile && run
