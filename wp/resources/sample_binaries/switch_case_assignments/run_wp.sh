# This tests that removing a switch case can result in a fall through to
# another case that is not intended.

# After removing the case to LOG_STATUS, the NAV case will fall through to
# DEPLOY, setting the deploy flag to true. In the original binary, deploy
# should be set to false at the end of execution.

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=process_status
}

compile && run
