# A simple test where the output of a function is a pointer that contains
# different values. WP is able to catch that the output varies between the
# two binaries. In this case, main_1 returns a 5 and main_2 returns a 6.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    -- main_1.bpj main_2.bpj
}

compile && run
