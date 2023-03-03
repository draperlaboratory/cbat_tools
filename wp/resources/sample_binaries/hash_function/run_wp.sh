#!/bin/bash
# Trips an assert if a password hashes to the "special" value in a hashtable.

# Should return SAT

run() {
  bap wp \
    --func=perform_hash \
    --inline=bad_hash \
    --trip-asserts \
    --show=diagnostics \
    -- ./bin/main
}

run
