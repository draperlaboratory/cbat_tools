# an example that compares the debruijn method of finding the LSB instead
# to that of using a for loop

set -x

compile () {
        make
}

run () {
        bap ../dummy/hello_world.out --pass=wp \
                --wp-compare=true \
                --wp-file1=main_1.bpj \
                --wp-file2=main_2.bpj \
                --wp-function=rightmost_index_32 \
                --wp-compare-post-reg-values=RAX
}

compile && run
