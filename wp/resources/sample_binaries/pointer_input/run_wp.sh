# This binary returns a pointer that was passed in as an argument. This test
# compares the binary with itself.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --mem-offset \
    -- main_1.bpj main_2.bpj
}

compile && run
