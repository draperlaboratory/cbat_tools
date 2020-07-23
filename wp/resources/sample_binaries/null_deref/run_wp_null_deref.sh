# A simple example that contains a dereferences a NULL value.

# In this case, the check-null-deref flag is set. This adds a hook to every
# memory read in the program and adds a verification condition that
# asserts that each read is to a non-null address. From this WP can determine
# that argc/RDI = 3 causes the null dereference.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --check-null-derefs \
    -- main
}

compile && run
