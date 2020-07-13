# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# Because foo's address is different between the binaries, Z3 can create a
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
    --wp-compare-post-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15  \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=foo_get \

}

compile && run
