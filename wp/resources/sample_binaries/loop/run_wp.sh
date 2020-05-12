compile() {
        make
}

run() {
        bap main --pass=wp --wp-num-unroll=2

}

clean() {
        make clean
}

clean && compile && run
