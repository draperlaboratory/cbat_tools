# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# In this comparison with the default flags, we are just comparing the output
# register RAX between the two binaries. Since both do not write to RAX, the
# property that RAX are equal at the end of execution holds.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    -- main_1.bpj main_2.bpj
}

compile && run
