# This tests that removing a switch case can result in a fall through to
# another case that is not intended. After removing the case to LOG_STATUS,
# the NAV case will fall through to DEPLOY, calling deploy_payload().

# This tests that if a function is not called in the original binary, it should
# not be called in the modified binary by turning on the check-calls flag.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=process_message \
    --compare-func-calls \
    -- main_1.bpj main_2.bpj
}

compile && run
