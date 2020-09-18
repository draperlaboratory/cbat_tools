# This tests inlining a function that has been compiled with fPIC.
# init() returns different values, and if inlined properly, WP should be able
# to capture this.

# Should return SAT.

run () {
  bap wp \
    --func=example \
    --inline="init|sub_*" \
    --compare-post-reg-values=RAX \
    -- main_1.so main_2.so
}

run
