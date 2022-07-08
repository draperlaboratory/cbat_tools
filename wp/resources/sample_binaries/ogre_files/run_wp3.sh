#!/bin/sh

# Checks that return value of f1 is identical if we lift the same
# binary twice.  Uses the same ogre file for both.
#
# Should be UNSAT

run () {
    bap wp \
      --func=f1 \
      --ogre=main1.ogre \
      --postcond="(assert (= R0_orig R0_mod))" \
      -- ./bin/main_1_stripped ./bin/main_1_stripped
}

run
