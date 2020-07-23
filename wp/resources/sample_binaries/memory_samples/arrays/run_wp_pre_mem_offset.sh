# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# This test enforces that the index passed into foo_get is less that 10,
# ensuring that foo_get reads from the array. With the mem_offset flag on,
# the memory values at the original address match that off the modified address.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=foo_get \
    --compare-post-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15  \
    --mem-offset \
    --precond="(assert (bvult RDI_orig #x000000000000000a))" \
    -- main_1.bpj main_2.bpj
}

compile && run
