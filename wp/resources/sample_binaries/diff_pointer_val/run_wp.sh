# A simple test where the output of a function is a pointer that contains
# different values. WP is able to catch that the output varies between the
# two binaries. In this case, main_1 returns a 5 and main_2 returns a 6.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    -- ./bin/main_1 ./bin/main_2
}

run
