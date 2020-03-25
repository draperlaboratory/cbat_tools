compile() {
        make
}

run() {
        bap main --pass=wp --wp-num-unroll=100

}

clean() {
        make clean
}

clean && compile && run
