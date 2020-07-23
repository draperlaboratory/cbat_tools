# This test compiles the same C file with and without stack protection.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RSI,RAX \
    -- main_1.bpj main_2.bpj
}

compile && run
