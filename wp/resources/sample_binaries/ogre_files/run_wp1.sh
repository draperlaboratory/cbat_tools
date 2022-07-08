#!/bin/sh

# Checks return value of f1 in unstripped main_1.
# Uses ogre file to lift only relevant function.
#
# Should be UNSAT

run () {
    bap wp \
      --func=f1 \
      --ogre=main1.ogre \
      --postcond="(assert (= R0 (_ bv1 32)))" \
      -- ./bin/main_1
}

run
