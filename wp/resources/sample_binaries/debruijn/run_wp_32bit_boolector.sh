#!/bin/bash

# an example that compares the debruijn method of finding the LSB instead
# to that of using a for loop

# Should return UNSAT

run () {
  if type boolector > /dev/null 2>&1
  then
  bap wp \
    --func=rightmost_index_32 \
    --compare-post-reg-values=RAX \
    --no-byteweight \
    --ext-solver=boolector \
    -- ./bin/main_1 ./bin/main_2
  else
  bap wp \
  --func=rightmost_index_32 \
  --compare-post-reg-values=RAX \
  --no-byteweight \
  -- ./bin/main_1 ./bin/main_2
  fi
}

run
