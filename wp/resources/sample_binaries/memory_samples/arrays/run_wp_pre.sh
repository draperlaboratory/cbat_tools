# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# This test enforces that the index passed into foo_get is less that 10,
# ensuring that foo_get reads from the array. However, with the mem_offset flag
# off, the addresses of foo are different between the two binaries, Z3 can create a
# countermodel where the data at the modified binary's address differs from the
# data at the original binary's address.

# Should return SAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=foo_get \
    --wp-output-vars=RAX,RBX,RSP,RBP,R12,R13,R14,R15 \
    --wp-precond="(assert (bvult RDI_orig #x000000000000000a))"

}

compile && run
