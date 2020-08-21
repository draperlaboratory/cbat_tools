#!/bin/bash
# Trips an assert if a password hashes to the "special" value in a hashtable.

# Should return SAT

set -x

run() {
  bap wp \
    --func=perform_hash \
    --inline=bad_hash \
    --trip-asserts \
    -- main
}

run
