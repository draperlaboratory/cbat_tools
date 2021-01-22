# This binary returns a double dereference to argv. This test
# compares the binary with itself.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --mem-offset \
    -- ./bin/main_1 ./bin/main_2
}

run
