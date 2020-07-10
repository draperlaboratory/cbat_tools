# This test compares two binaries that have the same data section, but different
# BSS section.

# Since the addresses for x and y are different between the binaries,
# Z3 can generate a countermodel where the data at x and y's modified addresses
# differ from that of the original addresses, causing x + y to differ.

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

}

compile && run
