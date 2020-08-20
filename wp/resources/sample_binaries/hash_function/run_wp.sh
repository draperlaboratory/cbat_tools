#!/bin/bash
# Trips an assert if a password hashes to the "special" value in a hashtable.

# Should return SAT

set -x

compile() {
  make
}

run() {
  bap wp \
    --func=perform_hash \
    --inline=bad_hash \
    --trip-asserts \
    -- main
}

clean() {
  make clean
}

clean && compile && run
