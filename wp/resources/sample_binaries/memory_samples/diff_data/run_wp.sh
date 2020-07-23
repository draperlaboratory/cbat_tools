# Tests having a different value in the data section (at the same addresses)
# and the same values on the stack.

# The test accumulates that values in the data section and stack and stores
# the result in RAX. Because the data section has different values, the output
# RAX also differs.

# Should return SAT

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
