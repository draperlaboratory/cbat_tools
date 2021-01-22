#!/bin/bash

# an example that compares the debruijn method of finding the LSB instead
# to that of using a for loop

# Should return UNSAT

run () {
  bap wp \
    --func=rightmost_index_8 \
    --compare-post-reg-values=RAX \
    --no-byteweight \
    -- ./bin/main_1 ./bin/main_2
}

run
