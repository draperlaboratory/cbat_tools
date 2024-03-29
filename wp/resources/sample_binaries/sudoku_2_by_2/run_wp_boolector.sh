#!/bin/bash

# solves a 4 by 4 sudoku puzzle encoded into a 32 bit integer. If the correct
# solution is provided as input to sudoku_solver, a null dereference is
# performed

# Should return SAT

run () {
  if type boolector > /dev/null 2>&1
  then
    bap wp \
      --func=sudoku_solver \
      --check-null-derefs \
      --no-byteweight \
      --ext-solver=boolector \
      --show=diagnostics \
      -- ./bin/main
  else
    bap wp \
    --func=sudoku_solver \
    --check-null-derefs \
    --no-byteweight \
    --show=diagnostics \
    -- ./bin/main
  fi

}

run
