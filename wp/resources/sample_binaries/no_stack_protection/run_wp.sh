# This test compiles the same C file with and without stack protection.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RSI,RAX \
    -- main_1 main_2
}

run
