# This test accumulates the values on the stack into RAX. THe two binaries have
# different values on the stack, giving different outputs.

# Should return SAT.

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
