# Tests having different locations for the data section and same values on the
# stack. The binaries are the same except for the location of val.

# This test turns on the mem_offset flag, which equates the memory values of the
# original binary with that of the modified binary at an offset.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --mem-offset \
    --no-glibc-runtime \
    -- main_1 main_2
}

compile && run
