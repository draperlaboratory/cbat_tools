#!/bin/bash

# an example that compares the debruijn method of finding the LSB instead
# to that of using a for loop

# Should return UNSAT

run () {
  bap wp \
    --func=rightmost_index_16 \
    --compare-post-reg-values=RAX \
    --no-byteweight \
    -- main_1 main_2
}

run
