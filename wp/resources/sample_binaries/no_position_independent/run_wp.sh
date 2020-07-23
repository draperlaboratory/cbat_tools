# This tests inlining a function that has been compiled without the  fPIC flag.
# init() returns different values, and if inlined properly, WP should be able
# to capture this.

# Should return SAT.

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=example \
    --inline=init \
    --compare-post-reg-values=RAX \
    -- main_1.bpj main_2.bpj
}

compile && run
