# This test analyzes both the gotoExample and nestedIfExample.

# This test inlines all the calls to calloc rather than running the calloc
# function spec.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-inline=.* --wp-trip-asserts
}

compile && run
