# This test contains a single call to malloc. This tests the alloc spec that
# given the same allocator state and argument to malloc, malloc will return
# the same result.

# Should return UNSAT

run () {
  bap wp \
    --func=foo \
    --compare-post-reg-values=RAX \
    -- ./bin/main_1.o ./bin/main_2.o
}

run
