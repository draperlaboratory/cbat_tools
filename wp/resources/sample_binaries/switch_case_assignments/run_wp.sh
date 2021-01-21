# This tests that removing a switch case can result in a fall through to
# another case that is not intended.

# After removing the case to LOG_STATUS, the NAV case will fall through to
# DEPLOY, setting the deploy flag to true. In the original binary, deploy
# should be set to false at the end of execution.

# Should return SAT

run () {
  bap wp \
    --func=process_status \
    --compare-post-reg-values=RAX \
    --fun-specs=chaos-caller-saved \
    -- ./bin/main_1 ./bin/main_2
}

run
