# This test compiles the same C file with and without stack protection.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RSI,RAX \
    --fun-specs=chaos-caller-saved \
    -- ./bin/main_1 ./bin/main_2
}

run
