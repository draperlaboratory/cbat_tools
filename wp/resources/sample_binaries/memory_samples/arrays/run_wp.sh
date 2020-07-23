# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# Because foo's address is different between the binaries, Z3 can create a
# countermodel where the data at the modified binary's address differs from the
# data at the original binary's address.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=foo_get \
    --compare-post-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15  \
    -- main_1.bpj main_2.bpj
}

compile && run
