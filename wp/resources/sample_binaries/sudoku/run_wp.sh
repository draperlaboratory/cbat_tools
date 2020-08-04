#!/bin/bash
set -x

# solves a 4 by 4 sudoku puzzle encoded into a 32 bit integer. If the correct
# solution is provided as input to sudoku_solver, a null dereference is
# performed

compile () {
    make clean
    make
}

run () {
    compile
    bap main --pass=wp \
        --wp-function=sudoku_solver \
        --wp-check-null-deref \
        --no-byteweight
}

run
