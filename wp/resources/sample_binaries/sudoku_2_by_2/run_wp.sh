#!/bin/bash

# solves a 4 by 4 sudoku puzzle encoded into a 32 bit integer. If the correct
# solution is provided as input to sudoku_solver, a null dereference is
# performed

# Should return SAT

run () {
  bap wp \
    --func=sudoku_solver \
    --check-null-derefs \
    --fun-specs=chaos-caller-saved \
    --no-byteweight \
    -- ./bin/main
}

run
