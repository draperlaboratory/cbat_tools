#!/bin/bash

# solves a 9 by 9 sudoku puzzle encoded into a a series of 64 bit integers. If
# the correct solution is provided as input to sudoku_solver, an assert is
# tripped is performed

# Should return SAT

run () {
  bap wp \
    --func=sudoku_solver \
    --check-null-derefs \
    --no-byteweight \
    --inline="sub*" \
    -- main
}

run
