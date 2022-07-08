#!/bin/sh

# Checks return value of f1 in stripped main_1
# Uses ogre file to lift only relevant function, and give it a name
#
# Should be UNSAT

run () {
    bap wp \
      --func=f1 \
      --ogre=main1.ogre \
      --postcond="(assert (= R0 (_ bv1 32)))" \
      -- ./bin/main_1_stripped
}

run
