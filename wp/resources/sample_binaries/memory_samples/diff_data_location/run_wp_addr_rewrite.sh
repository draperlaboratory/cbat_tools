# Tests having different locations for the data section and same values on the
# stack. The binaries are the same except for the location of val.

# This test turns on the rewrite-addresses flag, which rewrites the addresses
# in the modified binary to match the original binary.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --rewrite-addresses \
    --no-glibc-runtime \
    -- main_1 main_2
}

run
