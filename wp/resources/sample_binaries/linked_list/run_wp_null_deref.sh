# An example with a linked list that attempts to write a 1 into a NULL pointer.

# In this case, the check-null-deref flag is set. This adds a hook to every
# memory read and write in the program, and adds a verification condition that
# asserts that each read/write is to a non-null address. From this WP can
# determine that this binary is attempting to write a 1 into a NULL address.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=create_linked_list \
    --check-null-derefs \
    -- main
}

compile && run
