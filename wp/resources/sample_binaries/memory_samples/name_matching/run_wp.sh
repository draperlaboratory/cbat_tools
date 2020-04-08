# A binary that returns the value of a global variable.

# This tests matching a symbol in the original binary with that of the modified
# binary whose name has been updated similarly to retrowrite's instrumentation
# and whose address is at a different location.

# Should return UNSAT

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
    --wp-mem-offset

}

compile && run
