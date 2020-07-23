# This tests a C file that has been compiled with GCC and with a tool that
# compiles the file into a ROP chain.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --inline=.* \
    --compare-post-reg-values=RAX \
    -- main-original.bpj main-rop.bpj
}

compile && run
