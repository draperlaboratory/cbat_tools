#!/bin/sh

# This checks that in an subroutine that does not use RSP
# that RSP is still included in the generated pointer constraints
# and that there are no errors

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --pointer-reg-list=RDI,RSI \
    -- ./bin/main
}

run
