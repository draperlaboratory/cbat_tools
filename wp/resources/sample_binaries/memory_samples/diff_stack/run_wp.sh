# This test accumulates the values on the stack into RAX. THe two binaries have
# different values on the stack, giving different outputs.

# Should return SAT.

set -x

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-glibc-runtime \
    -- main_1 main_2
}

run
