#!/bin/sh

# A simple example that contains a dereferences a NULL value.

# In this case, the verification condition that checks if memory dereferences
# are non-null is turned off, and WP is unable to determine which input causes
# the null dereference.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    -- ./bin/main
}

run
