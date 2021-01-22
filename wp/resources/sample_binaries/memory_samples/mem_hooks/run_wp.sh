# Tests having different locations for the data section and same values on the
# stack. The binaries are the same except for the location of val.

# This tests the usage of the --check-invalid-derefs flag.
# This test should have the same output whether this flag is set or not.

# Should return SAT.

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --show=bir,paths \
    --check-invalid-derefs \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
