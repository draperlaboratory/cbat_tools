#!/bin/sh

# Checks to see if f1 in main_2 returns 1 more than f1 in main_1.  It should.
# We use stripped main_1 and unstripped main_2 and only provide ogre for
# the former.
#
# Should be UNSAT

run () {
    bap wp \
      --func=f1 \
      --ogre-orig=main1.ogre \
      --postcond="(assert (= (bvadd (_ bv1 32) R0_orig) R0_mod))" \
      -- ./bin/main_1_stripped ./bin/main_2
}

run
