# An example with a linked list that attempts to write a 1 into a NULL pointer.

# In this case, the verification condition that checks if memory dereferences
# are non-null is turned off, and WP is unable to determine that this binary
# attempts to write a 1 in an address that is NULL.

# Should return UNSAT

run () {
  bap wp \
    --func=create_linked_list \
    -- ./bin/main
}

run
